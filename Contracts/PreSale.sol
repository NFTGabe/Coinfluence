// SPDX-License-Identifier: MIT

pragma solidity ^0.8.0;

/*
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        this; // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }
}


/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor () {
        address msgSender = _msgSender();
        _owner = msgSender;
        emit OwnershipTransferred(address(0), msgSender);
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}



interface IBEP20 {
  /**
   * @dev Returns the amount of tokens in existence.
   */
  function totalSupply() external view returns (uint256);

  /**
   * @dev Returns the token decimals.
   */
  function decimals() external view returns (uint8);

  /**
   * @dev Returns the token symbol.
   */
  function symbol() external view returns (string memory);

  /**
  * @dev Returns the token name.
  */
  function name() external view returns (string memory);

  /**
   * @dev Returns the bep token owner.
   */
  function getOwner() external view returns (address);

  /**
   * @dev Returns the amount of tokens owned by `account`.
   */
  function balanceOf(address account) external view returns (uint256);

  /**
   * @dev Moves `amount` tokens from the caller's account to `recipient`.
   *
   * Returns a boolean value indicating whether the operation succeeded.
   *
   * Emits a {Transfer} event.
   */
  function transfer(address recipient, uint256 amount) external returns (bool);

  /**
   * @dev Returns the remaining number of tokens that `spender` will be
   * allowed to spend on behalf of `owner` through {transferFrom}. This is
   * zero by default.
   *
   * This value changes when {approve} or {transferFrom} are called.
   */
  function allowance(address _owner, address spender) external view returns (uint256);

  /**
   * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
   *
   * Returns a boolean value indicating whether the operation succeeded.
   *
   * IMPORTANT: Beware that changing an allowance with this method brings the risk
   * that someone may use both the old and the new allowance by unfortunate
   * transaction ordering. One possible solution to mitigate this race
   * condition is to first reduce the spender's allowance to 0 and set the
   * desired value afterwards:
   * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
   *
   * Emits an {Approval} event.
   */
  function approve(address spender, uint256 amount) external returns (bool);

  /**
   * @dev Moves `amount` tokens from `sender` to `recipient` using the
   * allowance mechanism. `amount` is then deducted from the caller's
   * allowance.
   *
   * Returns a boolean value indicating whether the operation succeeded.
   *
   * Emits a {Transfer} event.
   */
  function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);

  /**
   * @dev Emitted when `value` tokens are moved from one account (`from`) to
   * another (`to`).
   *
   * Note that `value` may be zero.
   */
  event Transfer(address indexed from, address indexed to, uint256 value);

  /**
   * @dev Emitted when the allowance of a `spender` for an `owner` is set by
   * a call to {approve}. `value` is the new allowance.
   */
  event Approval(address indexed owner, address indexed spender, uint256 value);
}


abstract contract ReentrancyGuard {

    bool private _notEntered;

    constructor () {
        _notEntered = true;
    }

    modifier nonReentrant() {
        
        // On the first call to nonReentrant, _notEntered will be true
        require(_notEntered, "ReentrancyGuard: reentrant call");

        // Any calls to nonReentrant after this point will fail
        _notEntered = false;

        _;

        _notEntered = true;
    }
}



contract CFLUPresale is Context, Ownable, ReentrancyGuard {

    IBEP20 private _token;
    address private _wallet;
    mapping(uint256 => uint256) _weiRaised;

    // phase detail
    uint256 private _phase;
    uint256 private _cap;
    uint256 private _rate;
    uint256 private _phaseSupplyLeft;
    uint256 private _phaseSupplyTotal;
    uint256 private _phaseStartTimestamp; //epoch in seconds
    uint256 private _phaseEndTimestamp; //epoch in seconds

    constructor(address token, address wallet) {
        _token = IBEP20(token);
        _wallet = wallet;
    }

    /******************************************************
     * INFO REGARDING THE CURRENT SALE PHASE
     ******************************************************/
    function rate() public view returns (uint256) {
        return _rate;
    }

    function cap() public view returns (uint256) {
        return _cap;
    }

    function phaseSupplyLeft() public view returns (uint256) {
        return _phaseSupplyLeft;
    }

    function phaseSupplyTotal() public view returns (uint256) {
        return _phaseSupplyTotal;
    }  

    function phaseStartTimestamp() public view returns (uint256) {
        return _phaseStartTimestamp;
    }

    function phaseEndTimestamp() public view returns (uint256) {
        return _phaseEndTimestamp;
    } 

    function phaseIsActive() public view returns (bool){
        return (block.timestamp > _phaseStartTimestamp &&
                block.timestamp < _phaseEndTimestamp);
    }

    function currentPhase() public view returns (uint256){
        return _phase;
    }

    function weiRaised(uint256 phase) public view returns (uint256){
        return _weiRaised[phase];
    }

    function presaleWallet() public view returns (address){
        return _wallet;
    }

    function tokenAddress() public view returns (IBEP20){
        return _token;
    }

    fallback () external payable {
        purchaseToken(_msgSender());
    }
    /**
     * Purchase token. Provided amount is the total amount of token (without digits).
     * This function has a non-reentrancy guard, so it shouldn't be called by
     * another `nonReentrant` function.
     */
    function purchaseToken(address beneficiary) public payable nonReentrant {
        require(_msgSender() != address(0), "CFLUPresale: AddressZero cannot purchase.");
        require(phaseIsActive(), "CFLUPresale: Current phase is not active.");
        require( msg.value >= 0.1 ether, "CFLUPresale: Minimum amount required to purchase tokens is 0.1 BNB");

        uint256 tokenValue = msg.value * _rate;
        require(tokenValue <= _phaseSupplyLeft, "CFLUPresale: Amount exceeds remaining supply of the current phase.");

        _token.transfer(beneficiary, tokenValue);
        _weiRaised[_phase] = _weiRaised[_phase] + msg.value;
        _phaseSupplyLeft = _phaseSupplyLeft - tokenValue;

        address payable walletPayable = payable(_wallet);
        walletPayable.transfer(msg.value);
    }


    /**********************************************************
     * OWNER SECTION
     **********************************************************/

    function withdrawToken(uint256 amount) public onlyOwner {
        _token.transfer(owner(), amount);
        if(address(this).balance > 0){
            payable(payable(owner())).transfer(address(this).balance);
        }
    }

    function setCurrentPhase(uint256 phase, uint256 cap, uint rate, uint256 timestampStart, uint256 timestampEnd) public onlyOwner {
        require(cap * rate <= _token.balanceOf(address(this)), "CFLUPresale: Supply value exceeds the token balance");
        require(timestampStart >= block.timestamp, "CFLUPresale: opening time is before current time");
        require(timestampEnd > timestampStart, "CFLUPresale: opening time is not before closing time");
        _cap = cap;
        _rate = rate;
        _phaseSupplyTotal = cap * rate;
        _phaseSupplyLeft = cap * rate;
        _phaseStartTimestamp = timestampStart;
        _phaseEndTimestamp = timestampEnd;
        _phase = phase;
    }
 
}
module

public import CFSG.Sporadic.HeldB.InnerCheckInputs
public import CFSG.Sporadic.HeldB.OuterArithCheck

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB

@[expose] def heComm (y yi x xi : Array Nat) : Array Nat :=
  compA 8330 (compA 8330 y x) (compA 8330 yi xi)

@[expose] def heNonTwo (c : Array Nat) (s m : Nat) : Bool :=
  eqA 8330 (hePowA c (2 ^ s * m)) (idA 8330) && !eqA 8330 (hePowA c (2 ^ s)) (idA 8330)

@[expose] def heInvChk (_ : Unit) : Bool :=
  heNonTwo (heComm (heGen 0) (invCand 8330 (heGen 0)) (compA 8330 (heGen 1) (heGen 0))
      (compA 8330 (invCand 8330 (heGen 0)) (invCand 8330 (heGen 1)))) 1 3 &&
    heNonTwo (heComm heT1Arr (invCand 8330 heT1Arr) (heGen 0) (invCand 8330 (heGen 0))) 0 3 &&
    heNonTwo (heComm heT1Arr (invCand 8330 heT1Arr) (compA 8330 (heGen 1) (heGen 0))
      (compA 8330 (invCand 8330 (heGen 0)) (invCand 8330 (heGen 1)))) 0 3 &&
    eqA 8330 (compA 8330 heUArr (heGen 0)) (compA 8330 (heGen 0) heUArr) &&
    heNonTwo (heComm heUArr heUArr (compA 8330 (heGen 1) (heGen 0))
      (compA 8330 (invCand 8330 (heGen 0)) (invCand 8330 (heGen 1)))) 0 15

end CFSG.Quasithin.F7Two

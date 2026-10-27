module

public import CFSG.Sporadic.HeldB.AutData
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Sporadic.HeldB.AutData
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.HeldB.OuterArithCheckInputs
public import Certificates.Certificate2116

public section

namespace CFSG.Sporadic.HeldB

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def heUArr : Array ℕ := hePowA heAutRArr 5

theorem heOuterArith_check :
    isInvA 8330 heAutRArr (invCand 8330 heAutRArr) = true ∧
    eqA 8330 (hePowA heAutRArr 10) (idA 8330) = true ∧
    eqA 8330 (hePowA heAutRArr 2) (idA 8330) = false ∧
    eqA 8330 (hePowA heAutRArr 5) (idA 8330) = false ∧
    eqA 8330 (compA 8330 heAutRArr (heGen 0)) (compA 8330 (heGen 0) heAutRArr) = true ∧
    eqA 8330 (compA 8330 heW2Arr (compA 8330 heAutRArr (heGen 1)))
      (compA 8330 (heGen 1) (compA 8330 heW2Arr heAutRArr)) = true ∧
    siftA 8330 (rawLevels 8330 heStrongArrs heBase.toArray) heBase.toArray 0 heAutRArr = false ∧
    siftA 8330 (rawLevels 8330 heStrongArrs heBase.toArray) heBase.toArray 0
      (hePowA heAutRArr 2) = true :=
  Certificates.certificate2116

end CFSG.Sporadic.HeldB

module

public import CFSG.Sporadic.SuzRecog.Q3ACheck
public import Certificates.Data.SuzQ3ATitsData
public import Certificates.Data.SuzModelGroupsInputs
public import Certificates.Data.SuzQ3AOrbData

public section

namespace CFSG.Sporadic.SuzRecog.Q3A.TitsCheck

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.LevelTwoData
  CFSG.Sporadic.SuzRecog.Q3ATitsData CFSG.Sporadic.SuzRecog.Q3A.Check

@[expose] def rho2A : Array Nat := compA 1782 w0Arr (compA 1782 rhoArr (invCand 1782 w0Arr))

@[expose] def stabA (k : Nat) : Array Nat :=
  if k == 0 then stab0Arr else if k == 1 then stab1Arr else stab2Arr

@[expose] def gensT : List (Array Nat) :=
  [w0Arr, tau0Arr, rho0Arr, ModelGroupsData.s1Arr, ModelGroupsData.s2Arr, stab0Arr, stab1Arr,
    stab2Arr]

@[expose] def iv1 : Nat := actIdx w0Arr 0

@[expose] def iu0 : Nat := actIdx rho0Arr iv1

@[expose] def iu1 : Nat := actIdx ModelGroupsData.s1Arr iv1

@[expose, irreducible] def opar : Array Nat := hexTable 4 22880 0 Q3AOrbData.oparHex

@[expose, irreducible] def olab : Array Nat := hexTable 4 22880 0 Q3AOrbData.olabHex

@[expose, irreducible] def odep : Array Nat := hexTable 4 22880 0 Q3AOrbData.odepHex

@[expose] def forestCheck : Bool :=
  opar.size == 22880 && olab.size == 22880 && odep.size == 22880 &&
    allLt 22880 fun y => opar[y]! == 22880 ||
      (if odep[y]! == 0 then y == iu0 || y == iu1
       else opar[y]! < 22880 && opar[opar[y]!]! < 22880 && odep[opar[y]!]! < odep[y]! &&
         olab[y]! < 3 && actIdx (stabA olab[y]!) opar[y]! == y)

@[expose] def titsCheck : Bool :=
  let ci := cArrInv iv1
  gensT.all (fun a => isInvA 1782 a (invCand 1782 a) && CFSG.Sporadic.SuzOddCore.inM a) &&
    isInvA 1782 rhoArr (invCand 1782 rhoArr) &&
    decide (iv1 < 22880) && decide (iu0 < 22880) && decide (iu1 < 22880) &&
    adjIdx 0 iv1 && actIdx w0Arr iv1 == 0 &&
    actIdx tau0Arr 0 == iv1 && actIdx tau0Arr iv1 == 0 && actIdx tau0Arr iu0 == iu0 &&
    actIdx rho0Arr 0 == iv1 && actIdx rho0Arr iu0 == 0 &&
    actIdx ModelGroupsData.s1Arr 0 == 0 && actIdx ModelGroupsData.s1Arr iu1 == iv1 &&
    actIdx ModelGroupsData.s2Arr 0 == iv1 && actIdx ModelGroupsData.s2Arr iv1 == 0 &&
    actIdx ModelGroupsData.s2Arr iu1 == iu1 &&
    (List.range 3).all (fun k => actIdx (stabA k) 0 == 0 && actIdx (stabA k) iv1 == iv1) &&
    eqA 1782 (compA 1782 (compA 1782 rho0Arr (compA 1782 rho2A (invCand 1782 rho0Arr)))
      (compA 1782 rho2A rhoArr)) (idA 1782) &&
    forestCheck && allLt 22880 fun y => !(adjIdx 0 y && adjWith ci y) || opar[y]! < 22880

end CFSG.Sporadic.SuzRecog.Q3A.TitsCheck

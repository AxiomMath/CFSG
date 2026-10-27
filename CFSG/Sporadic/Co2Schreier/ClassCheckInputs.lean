
module

public import CFSG.Sporadic.Co2Schreier.ThirdCheckBase
public import CFSG.Sporadic.Co2InvData
public meta import CFSG.Sporadic.Co2Schreier.ThirdCheckBase
public meta import CFSG.Sporadic.Co2InvData

public section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2.Native

@[expose] def cRepArr (pt : Array UInt32) (r : ℕ) : Array ℕ :=
  matPerm pt (CFSG.Sporadic.Co2Inv.co2InvReps[r]!).toList

@[expose] def fuseWords : List (List ℤ) :=
  [[1, 2, 1, 1, -2, -2, 1, 2, 1, -2], [2], [-2, 2, 1, -1, 2]]

@[expose] def fuseExps : List ℕ := [3, 5, 11]

@[expose] def pickRep (z t u : Array ℕ) (r : ℕ) : Array ℕ :=
  if r = 0 then z else if r = 1 then t else u

@[noinline, expose] def classCheck (pt : Array UInt32) (z t u : Array ℕ) : Bool :=
  eqA 2300 (compA 2300 u u) (idA 2300) && !eqA 2300 u (idA 2300) &&
    allLt 3 fun r =>
      isInvA 2300 (cRepArr pt r) (invCand 2300 (cRepArr pt r)) &&
      allLt 2300 (fun k => co2PackedVecs[(cRepArr pt r)[k]!]! ==
        vecMulN 22 (transposeRows 22 CFSG.Sporadic.Co2Inv.co2InvReps[r]!) co2PackedVecs[k]!) &&
      lettersOK 2 (fuseWords.getD r []) &&
      isInvA 2300 (wordArr aArrs (fuseWords.getD r []))
        (invCand 2300 (wordArr aArrs (fuseWords.getD r []))) &&
      eqA 2300 (powA (compA 2300 (pickRep z t u r) (compA 2300 (compA 2300
        (wordArr aArrs (fuseWords.getD r [])) (cRepArr pt r))
        (invCand 2300 (wordArr aArrs (fuseWords.getD r []))))) (fuseExps.getD r 0)) (idA 2300)

end CFSG.Sporadic.Co2Schreier

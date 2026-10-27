module

public import Certificates.Data.Kernel.Misc.L52

public section

namespace CFSG.KD.L52

open CFSG.Quasithin.H13.KGE64

@[expose] def pwN (Y k : Nat) : List Nat := (List.range 8).map (mPowN (mPowN Y k))

@[expose] def candN (pw : List Nat) : List Nat :=
  ((bools 10).map ofCodeN).filter fun u => (List.range' 1 6).all fun i => isUTN (cj5N pw u i)

@[expose] def pairN (pw cand : List Nat) : Bool :=
  let A := cand.filter (condA5N pw)
  let B := cand.filter (condB5N pw)
  A.all fun a => B.all fun b => !commAll5N pw a b

@[expose] def coversN (P Q : List Nat) : Bool :=
  (List.range' 1 6).all fun i => (List.range' 1 6).any fun i' =>
    P.getD i 0 == Q.getD i' 0 && P.getD (7 - i) 0 == Q.getD (7 - i') 0

@[expose] def l52StepFN (Y : Nat) (cand : List Nat) (k : Nat) : Bool :=
  coversN (pwN Y k) (pwN Y 1) && coversN (pwN Y 1) (pwN Y k) && pairN (pwN Y k) cand

@[expose] def l52CheckYFN (Y : Nat) : Bool :=
  let cand := candN (pwN Y 1)
  (List.range' 1 6).all (l52StepFN Y cand)

@[expose] def l52CheckFN : Bool :=
  [1, 2, 3].all fun j => mEqN (mPowN (l52YN j) 7) mIdN && l52CheckYFN (l52YN j)

end CFSG.KD.L52

end

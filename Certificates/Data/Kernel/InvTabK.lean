module

public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KC.InvTabK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim

@[expose] def subprodsF (m : Nat) (pA : Nat → Nat → Nat) : List Nat → List Nat
  | [] => [m]
  | y :: l => subprodsF m pA l ++ (subprodsF m pA l).map (pA y)

@[expose] def startF : List Nat → Nat
  | [] => 0
  | a :: _ => a + 1

@[expose] def greedyExtF (m : Nat) (cA : Nat → Nat → Bool) (pA : Nat → Nat → Nat) (l : List Nat) :
    List Nat :=
  let S := subprodsF m pA l
  ((List.range m).drop (startF l)).filter fun x =>
    (l.all fun y => cA x y) && !(S.contains x) && (S.all fun s => s == m || decide (x < pA x s))

@[expose] def forallGreedyF (m : Nat) (cA : Nat → Nat → Bool) (pA : Nat → Nat → Nat)
    (pred : List Nat → Bool) : Nat → List Nat → Bool
  | 0, l => pred l
  | k + 1, l => (greedyExtF m cA pA l).all fun x => forallGreedyF m cA pA pred k (x :: l)

@[expose] def letterPK (idn : Nat) (L LI : List Nat) (z : Int) : Nat × Nat :=
  if z = 0 then (idn, idn)
  else if 0 < z then (L.getD (z.toNat - 1) idn, LI.getD (z.toNat - 1) idn)
  else (LI.getD ((-z).toNat - 1) idn, L.getD ((-z).toNat - 1) idn)

@[expose] noncomputable def wordP1 (n w : Nat) (L LI : List Nat) : List Int → Nat
  | [] => pidn n w
  | z :: wd => pcomp n w (mask w) (letterPK (pidn n w) L LI z).1 (wordP1 n w L LI wd)

@[expose] noncomputable def wordP2 (n w : Nat) (L LI : List Nat) : List Int → Nat
  | [] => pidn n w
  | z :: wd => pcomp n w (mask w) (wordP2 n w L LI wd) (letterPK (pidn n w) L LI z).2

end CFSG.KC.InvTabK

end

module

public import Certificates.Data.Kernel.Misc.ArrEnum

public section

namespace CFSG.KC.Misc.ConjTab

open CFSG.KC.Enum (pg pcomp)
open CFSG.KS (mask)
open CFSG.KC.LQT.P (allN)

@[expose] noncomputable def cj3 (n w p s q : Nat) : Nat :=
  pcomp n w (mask w) (pcomp n w (mask w) p s) q

@[expose] noncomputable def sigAt (n w : Nat) (R L LI S : Nat → Nat) (q : Nat) : Bool :=
  Nat.beq (R q) (cj3 n w (L (Nat.div q 2)) (S (Nat.mod q 2)) (LI (Nat.div q 2)))

@[expose] noncomputable def transAt (n w b kA : Nat) (R L LI T A : Nat → Nat) (i : Nat) : Bool :=
  allN kA fun k => allN 2 fun j =>
    Nat.beq (R (Nat.add (Nat.mul 2 (pg b (mask b) (T i) k)) j))
      (cj3 n w (L i) (R (Nat.add (Nat.mul 2 (A k)) j)) (LI i))

@[expose] noncomputable def sepAt (n w : Nat) (R : Nat → Nat) (x y i : Nat) : Bool :=
  allN i fun j =>
    !(Nat.beq (pg w (mask w) (R (Nat.mul 2 i)) x) (pg w (mask w) (R (Nat.mul 2 j)) x) &&
      Nat.beq (pg w (mask w) (R (Nat.mul 2 i)) y) (pg w (mask w) (R (Nat.mul 2 j)) y))

@[expose] noncomputable def parentAt (P : List (List Int)) (T : Nat → Nat) (par : Nat → Nat)
    (i : Nat) : Bool :=
  decide (P.getD i [] = P.getD (par i) [] ++ [(P.getD i []).getLastD 0]) &&
    decide (1 ≤ (P.getD i []).getLastD 0) && decide ((P.getD i []).getLastD 0 ≤ 4) &&
    Nat.beq (pg 8 (mask 8) (T (par i)) (Nat.sub ((P.getD i []).getLastD 0).toNat 1)) i

end CFSG.KC.Misc.ConjTab

end

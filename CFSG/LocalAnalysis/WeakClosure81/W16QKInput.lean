module

public import CFSG.LocalAnalysis.WeakClosure81.W16QDInputs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.CGT.Timmesfeld75
open Subgroup

@[expose] def sylowCenter {X : Type} [Group X] (R : Sylow 2 X) : Subgroup X :=
  (R : Subgroup X) ⊓ centralizer ((R : Subgroup X) : Set X)

structure KGroup1616Input : Prop where
  sz_simple : ∀ (n : ℕ) (X : Type) [Group X], 1 < n → CFSG.Quasithin.IsSz n X →
    IsSimpleGroup X
  sz_card : ∀ (n : ℕ) (X : Type) [Group X], 1 < n → CFSG.Quasithin.IsSz n X →
    Nat.card X = (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1)
  u3_sylow_ti : ∀ (n : ℕ) (X : Type) [Group X] [Finite X], 1 < n → IsU3Shape X n →
    ∀ R R' : Sylow 2 X, R ≠ R' → (R : Subgroup X) ⊓ (R' : Subgroup X) = ⊥
  u3_center_card : ∀ (n : ℕ) (X : Type) [Group X] [Finite X], 1 < n → IsU3Shape X n →
    ∀ R : Sylow 2 X, Nat.card (sylowCenter R) = 2 ^ n
  u3_omega : ∀ (n : ℕ) (X : Type) [Group X] [Finite X], 1 < n → IsU3Shape X n →
    ∀ R : Sylow 2 X, ∀ g : X, g ∈ (R : Subgroup X) → (g * g = 1 ↔ g ∈ sylowCenter R)
  u3_card_sylow : ∀ (n : ℕ) (X : Type) [Group X] [Finite X], 1 < n → IsU3Shape X n →
    Nat.card (Sylow 2 X) = (2 ^ n) ^ 3 + 1
  u3_pair : ∀ (n : ℕ) (X : Type) [Group X] [Finite X], 1 < n → IsU3Shape X n →
    ∀ R R' : Sylow 2 X, R ≠ R' →
      IsL2Pair ↥(sylowCenter R ⊔ sylowCenter R')
        ((sylowCenter R).subgroupOf (sylowCenter R ⊔ sylowCenter R')) (2 ^ n)

end CFSG.LocalAnalysis.WeakClosure81

end

module

public import Init

public section

namespace CFSG.Monster.B.CTIB.Kernel

inductive Reach (act : Nat → Nat → Nat) (ngen : Nat) (valid : Nat → Bool) (root : Nat) :
    Nat → Prop
  | root : Reach act ngen valid root root
  | step {a b : Nat} (k : Nat) : k < ngen → valid a = true → valid b = true →
      Reach act ngen valid root a → (act k a = b ∨ act k b = a) → Reach act ngen valid root b

@[expose] def OrbitList (act : Nat → Nat → Nat) (ngen : Nat) (valid : Nat → Bool)
    (root size : Nat) : Prop :=
  ∃ pts : List Nat, pts.length = size ∧ pts.Nodup ∧ root ∈ pts ∧
    (∀ p ∈ pts, valid p = true ∧ root ≤ p) ∧ (∀ p ∈ pts, ∀ k < ngen, act k p ∈ pts) ∧
    ∀ p ∈ pts, Reach act ngen valid root p

end CFSG.Monster.B.CTIB.Kernel

end

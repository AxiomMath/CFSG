module

public import Certificates.Data.Kernel.Misc.GL4Elt
public import Certificates.Data.A5GL42

public section

namespace CFSG.KC.Misc.GL4

open Certificates.A5GL42 (subspaceCodes)

@[expose] def SubC : Prop :=
  [0] ∈ subspaceCodes ∧ List.range 16 ∈ subspaceCodes ∧ (∀ s ∈ subspaceCodes, 0 ∈ s ∧ ∀ x ∈ s, x < 16) ∧
    ∀ s ∈ subspaceCodes, ∀ u < 16, u ∉ s →
      (List.range 16).filter (fun x => decide (x ∈ s ∨ (x ^^^ u) ∈ s)) ∈ subspaceCodes

instance : Decidable SubC := by unfold SubC; infer_instance

@[expose] def StabC (c : Nat) (s : List Nat) : Prop := ∀ x ∈ s, ∃ y ∈ s, mul4F c (colC x) = colC y

noncomputable instance (c : Nat) (s : List Nat) : Decidable (StabC c s) := by unfold StabC; infer_instance

@[expose] def GrpC (l : List Nat) (a b : Nat) : Prop :=
  (∀ c ∈ l, c < 65536) ∧ l.Nodup ∧ l.length = 60 ∧ id4 ∈ l ∧ a ∈ l ∧ b ∈ l ∧
    (∀ x ∈ l, ∀ y ∈ l, mul4F x y ∈ l) ∧ (∀ x ∈ l, ∃ y ∈ l, mul4F x y = id4) ∧
    (∀ x ∈ l, mul4F (mul4F (mul4F x x) x) x = id4 → mul4F x x = id4) ∧
    ∀ s ∈ subspaceCodes, StabC a s → StabC b s → s = [0] ∨ s = List.range 16

noncomputable instance (l : List Nat) (a b : Nat) : Decidable (GrpC l a b) := by unfold GrpC; infer_instance

end CFSG.KC.Misc.GL4

end

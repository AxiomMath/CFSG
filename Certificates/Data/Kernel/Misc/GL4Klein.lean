module

public import Certificates.Data.Kernel.Misc.GL4Grp

public section

namespace CFSG.KC.Misc.GL4

open Certificates.A5GL42 (subspaceCodes codesN codesO)

@[expose] noncomputable def V16: List Nat := (List.range 16).map colC

@[expose] noncomputable def commL(Ac Sc : List Nat) : List Nat :=
  (Ac.flatMap fun a => Sc.map fun x => x ^^^ mul4F a x).dedup

@[expose] noncomputable def fixL(Ac : List Nat) : List Nat :=
  V16.filter fun x => Ac.all fun a => Nat.beq (mul4F a x) x

@[expose] noncomputable def normL(Hc Ac : List Nat) : List Nat :=
  Hc.filter fun h => Ac.all fun x => Ac.any fun y => Nat.beq (mul4F h x) (mul4F y h)

@[expose] def SameL (l m : List Nat) : Prop := (∀ x ∈ l, x ∈ m) ∧ ∀ x ∈ m, x ∈ l

instance (l m : List Nat) : Decidable (SameL l m) := by unfold SameL; infer_instance

@[expose] def SpanC (Fc : List Nat) (n : Nat) : Prop :=
  0 ∈ Fc ∧ (∀ x ∈ Fc, ∀ y ∈ Fc, x ^^^ y ∈ Fc) ∧ Fc.dedup.length = n

instance (Fc : List Nat) (n : Nat) : Decidable (SpanC Fc n) := by unfold SpanC; infer_instance

@[expose] def KleinC (a b : Nat) : Prop :=
  a ≠ id4 ∧ b ≠ id4 ∧ a ≠ b ∧ mul4F a a = id4 ∧ mul4F b b = id4 ∧ mul4F a b = mul4F b a

noncomputable instance (a b : Nat) : Decidable (KleinC a b) := by unfold KleinC; infer_instance

@[expose] noncomputable def kAc(a b : Nat) : List Nat := [id4, a, b, mul4F a b]

@[expose] def LatC (Bc : List Nat) (Ls : List (List Nat)) : Prop :=
  (∀ m ∈ Ls, 0 ∈ m ∧ (∀ x ∈ m, ∀ y ∈ m, x ^^^ y ∈ m) ∧ ∀ h ∈ Bc, ∀ x ∈ m, mul4F h x ∈ m) ∧
    ∀ l ∈ subspaceCodes, (∀ h ∈ Bc, StabC h l) → ∃ m ∈ Ls, SameL (l.map colC) m

noncomputable instance (Bc : List Nat) (Ls : List (List Nat)) : Decidable (LatC Bc Ls) := by
  unfold LatC; infer_instance

@[expose] def MulC (S : List Nat) : Prop := id4 ∈ S ∧ ∀ c ∈ S, ∀ d ∈ S, mul4F c d ∈ S

noncomputable instance (S : List Nat) : Decidable (MulC S) := by unfold MulC; infer_instance

@[expose] def OffC (S : List Nat) : Prop :=
  (∃ c ∈ S, c ≠ id4) ∧
    (∀ c ∈ S, ∀ d ∈ S, ∀ x ∈ V16, (x ^^^ mul4F c x) ^^^ mul4F d (x ^^^ mul4F c x) = 0) ∧
    16 ≤ (fixL S).dedup.length * S.dedup.length

noncomputable instance (S : List Nat) : Decidable (OffC S) := by unfold OffC; infer_instance

@[expose] def NatC (Hc Ac F : List Nat) : Prop :=
  SpanC F 4 ∧ SameL F (fixL Ac) ∧ (∀ a ∈ Ac, a ≠ id4 → ∀ x ∈ V16, mul4F a x = x → x ∈ F) ∧
    LatC (normL Hc Ac) [[0], F, V16] ∧ ∀ S ∈ Ac.sublists, MulC S → OffC S → SameL S Ac

noncomputable instance (Hc Ac F : List Nat) : Decidable (NatC Hc Ac F) := by
  unfold NatC; infer_instance

@[expose] def OrthC (Hc Ac F₂ F₁ : List Nat) : Prop :=
  SpanC F₂ 8 ∧ SpanC F₁ 2 ∧ SameL F₁ (fixL Ac) ∧ LatC (normL Hc Ac) [[0], F₁, F₂, V16] ∧
    (∀ d ∈ normL Hc Ac, d ≠ id4 → mul4F (mul4F d d) d = id4 →
      ∀ x ∈ F₂, x ^^^ mul4F d x ∈ F₁ → x ∈ F₁) ∧
    ∀ S ∈ Ac.sublists, MulC S → ¬ OffC S

noncomputable instance (Hc Ac F₂ F₁ : List Nat) : Decidable (OrthC Hc Ac F₂ F₁) := by
  unfold OrthC; infer_instance

@[expose] def KleinNC : Prop :=
  ∀ a ∈ codesN, ∀ b ∈ codesN, KleinC a b → NatC codesN (kAc a b) (commL (kAc a b) V16)

noncomputable instance : Decidable KleinNC := by unfold KleinNC; infer_instance

@[expose] def KleinOC : Prop :=
  ∀ a ∈ codesO, ∀ b ∈ codesO, KleinC a b →
    OrthC codesO (kAc a b) (commL (kAc a b) V16) (commL (kAc a b) (commL (kAc a b) V16))

noncomputable instance : Decidable KleinOC := by unfold KleinOC; infer_instance

end CFSG.KC.Misc.GL4

end

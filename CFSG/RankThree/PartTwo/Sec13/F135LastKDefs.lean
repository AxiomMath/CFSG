module

public import CFSG.RankThree.PartTwo.Sec13.F135LastDefs
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup

abbrev He : Type := CFSG.Blueprint.NativeSporadic.He
abbrev ON : Type := CFSG.Blueprint.NativeSporadic.ON
abbrev J4 : Type := CFSG.Blueprint.NativeSporadic.J4

@[expose] def KFactTwoSix : Prop := HasTwoSix He ∧ HasTwoSix J4

@[expose] def KFactFourCubeSeven : Prop := ∃ (A : Subgroup ON) (x : ON), FourCubeSeven A x

@[expose] def KFactMultiplier : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.IsQuasisimple Q →
    (Nonempty (Q ⧸ Subgroup.center Q ≃* He) ∨ Nonempty (Q ⧸ Subgroup.center Q ≃* ON) ∨
      Nonempty (Q ⧸ Subgroup.center Q ≃* J4)) → Nat.card (Subgroup.center Q) ∣ 3

@[expose] def KFactK3 : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ),
    ((p = 7 ∧ (Nonempty (S ≃* He) ∨ Nonempty (S ≃* ON))) ∨ (p = 11 ∧ Nonempty (S ≃* J4))) →
    ∀ P : Subgroup (MulAut S), IsPGroup p P → p ^ 3 ≤ Nat.card P →
      ∀ α : MulAut S, α ^ 3 = 1 → (∀ π ∈ P, α * π = π * α) → α = 1

@[expose] def Identified (p : ℕ) (S : Type) [Group S] : Prop :=
  (p = 7 ∧ (Nonempty (S ≃* He) ∨ Nonempty (S ≃* ON))) ∨ (p = 11 ∧ Nonempty (S ≃* J4))

end CFSG.RankThree.PartTwo.Sec13.F135Last

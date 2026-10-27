module

public import CFSG.LocalAnalysis.StandardType.GGIOneExcTwE6

public section

namespace CFSG.StandardType.TwE6D3

open CFSG.Assembly

section Setup

variable {K : Type} [Field K] [Finite K] {n : ℕ} {L' : Type} [Group L']

structure Cfg (ψ : L' →* TwE6Delta.RecipeR K n) (A As : Subgroup (MulAut L')) : Prop where
  surj : Function.Surjective ψ
  ker_le : ψ.ker ≤ Subgroup.center L'
  perfect : commutator L' = ⊤
  hA : IsElemAbelian 3 A
  lt : A < As
  hAs : IsElemAbelian 3 As
  card_le : Nat.card As ≤ 3 * Nat.card A
  induces : ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l : L', φ (ψ l) = ψ (a l)
  rank : 3 ^ TwE6Delta.liftRank 3 ≤ Nat.card A
  rank3 : 3 ^ 3 ≤ Nat.card A
  adm : GGDeltaAdm 3 L' A
  none : GGNoTwoBetween A As

@[expose] def Induces (ψ : L' →* TwE6Delta.RecipeR K n) (a : MulAut L') : Prop :=
  ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l : L', φ (ψ l) = ψ (a l)

@[expose] def lam (Y : Subgroup (MulAut L')) : Subgroup L' :=
  Y.comap (MulAut.conj : L' →* MulAut L')

variable (K n) in
noncomputable def recipeISub : Subgroup (MulAut (TwE6Delta.RecipeR K n)) :=
  Subgroup.closure (LargeEvenInnSet (TwE6Delta.RecipeR K n) ∪
    LargeEvenChevDiagImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n))

theorem mem_recipeISub {φ : MulAut (TwE6Delta.RecipeR K n)} :
    φ ∈ recipeISub K n ↔ φ ∈ TwE6Delta.RecipeI K n := Iff.rfl

noncomputable def inducedSub (ψ : L' →* TwE6Delta.RecipeR K n) : Subgroup (MulAut L') where
  carrier := {a | Induces ψ a}
  mul_mem' := by
    rintro a b ⟨φa, hφa, ha⟩ ⟨φb, hφb, hb⟩
    refine ⟨φa * φb, (mem_recipeISub).1 (Subgroup.mul_mem _ ((mem_recipeISub).2 hφa)
      ((mem_recipeISub).2 hφb)), fun l => ?_⟩
    rw [MulAut.mul_apply, hb, ha]
    rfl
  one_mem' := ⟨1, (mem_recipeISub).1 (Subgroup.one_mem _), fun l => rfl⟩
  inv_mem' := by
    rintro a ⟨φ, hφ, ha⟩
    refine ⟨φ⁻¹, (mem_recipeISub).1 (Subgroup.inv_mem _ ((mem_recipeISub).2 hφ)), fun l => ?_⟩
    have h1 : φ (ψ (a⁻¹ l)) = ψ l := by
      rw [ha]
      change ψ (a (a⁻¹ l)) = ψ l
      rw [MulAut.apply_inv_self]
    have h2 := congrArg (⇑φ⁻¹) h1
    rw [MulAut.inv_apply, MulEquiv.symm_apply_apply] at h2
    exact h2.symm

theorem mem_inducedSub {ψ : L' →* TwE6Delta.RecipeR K n} {a : MulAut L'} :
    a ∈ inducedSub ψ ↔ Induces ψ a := Iff.rfl

@[expose] def TorusLiftInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 →
    3 ∣ 2 ^ n + 1 →
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* TwE6Delta.RecipeR K n),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      Nat.card (Subgroup.center L') = 3 →
      ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A → 3 ^ 5 ≤ Nat.card A →
        (∀ a ∈ A, Induces ψ a) →
        ∃ E : Subgroup L', IsElemAbelian 3 E ∧ 3 ^ 6 ≤ Nat.card E ∧ ∀ a ∈ A, ∀ e ∈ E, a e = e

@[expose] def EndNodeInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 →
    3 ∣ 2 ^ n + 1 → 3 ∣ n →
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* TwE6Delta.RecipeR K n),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      Nat.card (Subgroup.center L') = 3 →
      ∀ Y : Subgroup (MulAut L'), IsElemAbelian 3 Y → Nat.card Y = 3 ^ 6 →
        (∀ y ∈ Y, Induces ψ y) →
        ∃ t : MulAut L', GGIsEndNode Y t ∧ ¬ LargeEvenSmall (LargeEvenLayer (ggFix t)) ∧
          ∀ s : MulAut L', (∀ y ∈ Y, s * y = y * s) → s ^ 3 = 1 → ¬ Induces ψ s →
            ∃ j ∈ LargeEvenLayer (ggFix t), s j ≠ j

end Setup

end CFSG.StandardType.TwE6D3

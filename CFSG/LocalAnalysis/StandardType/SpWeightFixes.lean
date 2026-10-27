module

public import CFSG.LocalAnalysis.StandardType.SpWeightForm
public import CFSG.LocalAnalysis.StandardType.SpBlockMatrices
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.StandardType

namespace SpFixed

open Matrix
open CFSG.Open (StatedSp)

section Twist

variable {F : Type} [Field F] [Finite F] [CharP F 2] {Ω : Type} [Field Ω] [Algebra F Ω] [CharP Ω 2]
  [IsAlgClosed Ω]

theorem exists_frobenius_twist (h3 : 3 ∣ Nat.card F + 1) :
    ∃ σ : Ω ≃+* Ω, (∀ x : F, σ (algebraMap F Ω x) = algebraMap F Ω x) ∧
      (∀ η : Ω, η ^ 3 = 1 → σ η = η⁻¹) ∧ ∀ η : Ω, η ^ 7 = 1 → ∃ k : ℕ, σ η = η ^ 2 ^ k := by
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨f, _, hfcard⟩ := FiniteField.card F 2
  have hcard : Nat.card F = 2 ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hfcard
  have h3' : 3 ∣ 2 ^ (f : ℕ) + 1 := by
    rw [← hcard]
    exact h3
  refine ⟨iterateFrobeniusEquiv Ω 2 (f : ℕ), ?_, ?_, ?_⟩
  · intro x
    rw [iterateFrobeniusEquiv_def]
    have hx : (algebraMap F Ω x) ^ Nat.card F = algebraMap F Ω x := by
      rw [Nat.card_eq_fintype_card, ← map_pow, FiniteField.pow_card]
    rw [← hcard]
    exact hx
  · intro η hη
    obtain ⟨m, hm⟩ := h3'
    have hpow : η ^ (2 ^ (f : ℕ) + 1) = 1 := by
      rw [hm, pow_mul, hη, one_pow]
    have hmul : η ^ 2 ^ (f : ℕ) * η = 1 := by
      rw [← pow_succ, hpow]
    rw [iterateFrobeniusEquiv_def]
    exact eq_inv_of_mul_eq_one_left hmul
  · intro _η _hη
    exact ⟨(f : ℕ), rfl⟩

end Twist

section Blocks

variable {F : Type} [Field F] {n : ℕ} {Ω : Type} [Field Ω] [Algebra F Ω] [CharP Ω 2] [IsAlgClosed Ω]
  {D : Subgroup (StatedSp n F)} [Fintype D] [Finite (StatedSp n F)]

theorem blk_conjHom_eq_one (W : WeightBasis F n Ω D)
    (hn : n ≤ 4 ∨ (n = 5 ∧ ∃ σ : Ω ≃+* Ω, (∀ x : F, σ (algebraMap F Ω x) = algebraMap F Ω x) ∧
      (∀ η : Ω, η ^ 3 = 1 → σ η = η⁻¹) ∧ ∀ η : Ω, η ^ 7 = 1 → ∃ k : ℕ, σ η = η ^ 2 ^ k))
    (hDc : Fintype.card D = 9) (hexp : ∀ a ∈ D, a ^ 3 = 1)
    {J : Subgroup (StatedSp n F)} (hJC : J ≤ Subgroup.centralizer (D : Set (StatedSp n F)))
    (hA : IsAlternatingEightCover ↥J) (k : D → Ω) (hk : ∃ a, k a ≠ 1) (g : ↥J) :
    SpBlocks.blk (W.fiber k) (W.conjHom (g : StatedSp n F)) = 1 := by
  let I := W.fiber k
  let Q : ↥J →* Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) Ω := W.conjHom.comp J.subtype
  have hQ : ∀ g : ↥J, SpBlocks.Splits I (Q g) := fun g => W.splits_conjHom_fiber (hJC g.2) k
  rcases hn with hn4 | ⟨hn5, σ, hσF, hσ3, hσ7⟩
  · have hI : I.card ≤ 3 := by
      have h := W.card_fiber_le hDc hexp k hk
      change (W.fiber k).card ≤ 3
      omega
    exact SpBlocks.IsAlternatingEightCover.blk_eq_one_of_card_le_three hA I Q hQ hI g
  · have hI : I.card ≤ 5 := by
      have h := W.card_fiber_le hDc hexp k hk
      subst hn5
      change (W.fiber k).card ≤ 5
      omega
    have hσw : ∀ (a : D) (α : Fin n ⊕ Fin n), σ (W.w a α) = (W.w a α)⁻¹ :=
      fun a α => hσ3 _ (W.w_pow_three hexp a α)
    have hH : SpBlocks.Splits I (W.form σ) := W.splits_form_fiber σ hσF hσw k
    have hHu : IsUnit (W.form σ) := W.isUnit_form σ
    have hform : ∀ g : ↥J, (Q g)ᵀ * W.form σ * (Q g).map σ = W.form σ :=
      fun g => W.form_invariant σ hσF (g : StatedSp n F)
    exact SpBlocks.IsAlternatingEightCover.blk_eq_one_of_card_le_five hA I Q hQ σ hσ7
      hH hHu hform hI g

end Blocks

section Fixes

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem fixes_of_ker (hn : n ≤ 4 ∨ (n = 5 ∧ 3 ∣ Nat.card F + 1))
    (D : Subgroup (StatedSp n F)) [Fintype D] (hDc : Fintype.card D = 9)
    (hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (hexp : ∀ a ∈ D, a ^ 3 = 1)
    {J : Subgroup (StatedSp n F)} (hJC : J ≤ Subgroup.centralizer (D : Set (StatedSp n F)))
    (hA : IsAlternatingEightCover ↥J) :
    ∀ g ∈ J, ∀ v : Fin n ⊕ Fin n → F, fixedNorm D *ᵥ v = 0 → matHom F n g *ᵥ v = v := by
  classical
  intro g hg v hv
  let Ω := AlgebraicClosure F
  have hodd : Odd (Fintype.card D) := by
    rw [hDc]; decide
  obtain ⟨W⟩ := exists_weightBasis (F := F) (n := n) (Ω := Ω) D hcomm hexp
  have hn' : n ≤ 4 ∨ (n = 5 ∧ ∃ σ : Ω ≃+* Ω,
      (∀ x : F, σ (algebraMap F Ω x) = algebraMap F Ω x) ∧
      (∀ η : Ω, η ^ 3 = 1 → σ η = η⁻¹) ∧
      ∀ η : Ω, η ^ 7 = 1 → ∃ k : ℕ, σ η = η ^ 2 ^ k) := by
    rcases hn with h4 | ⟨h5, h3dvd⟩
    · exact Or.inl h4
    · obtain ⟨σ, hσF, hσ3, hσ7⟩ := exists_frobenius_twist (F := F) (Ω := Ω) h3dvd
      exact Or.inr ⟨h5, σ, hσF, hσ3, hσ7⟩
  have hs : ∀ k : D → Ω, SpBlocks.Splits (W.fiber k) (W.conjHom g) :=
    fun k => W.splits_conjHom_fiber (hJC hg) k
  have hblk : ∀ k : D → Ω, k ≠ 1 → SpBlocks.blk (W.fiber k) (W.conjHom g) = 1 := by
    intro k hk1
    have hk : ∃ a, k a ≠ 1 := by
      by_contra h
      push Not at h
      exact hk1 (funext fun a => h a)
    exact blk_conjHom_eq_one W hn' hDc hexp hJC hA k hk ⟨g, hg⟩
  set y : Fin n ⊕ Fin n → Ω := W.Pinv *ᵥ (fun i => algebraMap F Ω (v i)) with hydef
  have hy : ∀ a, W.wt a = 1 → y a = 0 := by
    intro a ha
    rw [hydef]
    exact W.vec_eq_zero_of_fixedNorm hodd hv ha
  have hfix : W.conjHom g *ᵥ y = y :=
    SpBlocks.mulVec_eq_self_of_blk_eq_one W.wt 1 (W.conjHom g) hs hblk y hy
  have hcancel : ∀ X : Fin n ⊕ Fin n → Ω, W.Pm *ᵥ (W.Pinv *ᵥ X) = X := by
    intro X
    rw [Matrix.mulVec_mulVec, W.Pm_mul_Pinv, Matrix.one_mulVec]
  have hconj : W.conjHom g *ᵥ y
      = W.Pinv *ᵥ (matOver F n Ω g *ᵥ fun i => algebraMap F Ω (v i)) := by
    rw [hydef]
    calc W.conjHom g *ᵥ (W.Pinv *ᵥ fun i => algebraMap F Ω (v i))
        = (W.Pinv * matOver F n Ω g * W.Pm) *ᵥ
            (W.Pinv *ᵥ fun i => algebraMap F Ω (v i)) := by
            rw [W.conjHom_apply g]
      _ = W.Pinv *ᵥ (matOver F n Ω g *ᵥ
            (W.Pm *ᵥ (W.Pinv *ᵥ fun i => algebraMap F Ω (v i)))) := by
            rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ = W.Pinv *ᵥ (matOver F n Ω g *ᵥ fun i => algebraMap F Ω (v i)) := by
            rw [hcancel]
  have hstep : W.Pinv *ᵥ (matOver F n Ω g *ᵥ fun i => algebraMap F Ω (v i)) = y := by
    rw [← hconj, hfix]
  have hmatΩ : matOver F n Ω g *ᵥ (fun i => algebraMap F Ω (v i))
      = (fun i => algebraMap F Ω (v i)) := by
    have h := congrArg (fun w : Fin n ⊕ Fin n → Ω => W.Pm *ᵥ w) hstep
    rw [hydef] at h
    simpa only [hcancel] using h
  funext i
  apply FaithfulSMul.algebraMap_injective F Ω
  have h2 := congr_fun hmatΩ i
  rw [RingHom.map_mulVec]
  exact h2

end Fixes

end SpFixed

end CFSG.StandardType

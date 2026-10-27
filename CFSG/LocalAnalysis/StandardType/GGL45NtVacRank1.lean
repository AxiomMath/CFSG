module

public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGTableBLinear
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTri
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem lin_I_subset_inn {K : Type} [Field K] [Finite K] [CharP K 2] :
    LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K)) Set.univ ⊆
      Set.range (MulAut.conj :
        LargeEvenProj (LargeEvenSLGroup (Fin 2) K) →* MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 2) K))) := by
  rintro φ ⟨A, -, hφ⟩
  have := Fintype.ofFinite K
  obtain ⟨l, hl⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2)
    (((A : GL (Fin 2) K).det : Kˣ) : K)
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact (A : GL (Fin 2) K).det.ne_zero (by rw [hl, mul_zero])
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 l⁻¹ (inv_ne_zero hl0)) * A ∈
      LargeEvenSLGroup (Fin 2) K := by
    have hdet : (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 l⁻¹ (inv_ne_zero hl0)) * A :
        GL (Fin 2) K).det = 1 := by
      apply Units.ext
      rw [map_mul, Units.val_mul, Units.val_one, Matrix.GeneralLinearGroup.det_scalar,
        Fintype.card_fin, Units.val_pow_eq_pow_val, Units.val_mk0]
      rw [hl]
      rw [← pow_two l, ← mul_pow, inv_mul_cancel₀ hl0, one_pow]
    rw [TypeA.mem_largeEvenSLGroup_iff, ← Matrix.GeneralLinearGroup.val_det_apply]
    simpa using congrArg (fun u : Kˣ => (u : K)) hdet
  set A' := Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 l⁻¹ (inv_ne_zero hl0)) * A with hA'
  have hA'SL : A' ∈ LargeEvenSLGroup (Fin 2) K := hmem
  have hconj : ∀ h : GL (Fin 2) K, A' * h * A'⁻¹ = A * h * A⁻¹ := by
    intro h
    have hc := Subgroup.mem_center_iff.mp
      (TableB.scalar_mem_center (ι := Fin 2) (Units.mk0 l⁻¹ (inv_ne_zero hl0)))
    rw [hA', mul_inv_rev]
    set s := Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 l⁻¹ (inv_ne_zero hl0))
    calc s * A * h * (A⁻¹ * s⁻¹) = s * (A * h * A⁻¹) * s⁻¹ := by group
      _ = (A * h * A⁻¹) * s * s⁻¹ := by rw [hc (A * h * A⁻¹)]
      _ = A * h * A⁻¹ := by group
  obtain ⟨a, ha⟩ : ∃ a : LargeEvenSLGroup (Fin 2) K, (a : GL (Fin 2) K) = A' :=
    ⟨⟨A', hA'SL⟩, rfl⟩
  refine ⟨(a : LargeEvenProj (LargeEvenSLGroup (Fin 2) K)), ?_⟩
  ext x
  induction x using QuotientGroup.induction_on with
  | H h =>
    rw [MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    have hrel : ((a * h * a⁻¹ : LargeEvenSLGroup (Fin 2) K) : GL (Fin 2) K) = A * h * A⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ha]
      exact hconj h
    exact (hφ h (a * h * a⁻¹) hrel).symm

private theorem center_linProj_eq_bot {K : Type} [Field K] [Finite K] [CharP K 2] :
    Subgroup.center (LargeEvenProj (LargeEvenSLGroup (Fin 2) K)) = ⊥ := by
  let e : LargeEvenProj (LargeEvenSLGroup (Fin 2) K) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K :=
    (TypeA.recipeEquiv 2 K).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSLTwoEquivSL K)
  have hcenterSL : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center,
      CFSG.LocalAnalysis.ComponentInitial.LinearCover.scalars_two_eq_bot]
  rw [eq_bot_iff]
  intro x hx
  have hx' : e x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) :=
    (MulEquivClass.apply_mem_center_iff e).2 hx
  rw [hcenterSL, Subgroup.mem_bot] at hx'
  exact Subgroup.mem_bot.mpr (e.injective (by rw [hx', map_one]))

private theorem ggL45NtVacRank1_linear {p N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : LargeEvenRawCont} (hN : ∃ m, 1 ≤ m ∧ N = 2 ^ m)
    (h : LargeEvenRecipeLinear 2 N Q) :
    LargeEvenRecipeLinear 2 N fun R _ I F => Q R I F ∧ GGL45NtVac p R I F := by
  obtain ⟨K, hKfield, hKfin, hKN, hQ⟩ := h
  obtain ⟨m, hm1, hmN⟩ := hN
  have hKcard : Nat.card K = 2 ^ m := by rw [hKN, hmN]
  have hKchar : CharP K 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := m)
      (by rw [← Nat.card_eq_fintype_card]; exact hKcard)
  haveI : CharP K 2 := hKchar
  refine ⟨K, inferInstance, inferInstance, hKN, hQ, ?_⟩
  right
  rintro ⟨A, hAab, hAcard, hAI⟩
  have hAle : A ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (LargeEvenProj (LargeEvenSLGroup (Fin 2) K)) :=
    fun a ha => lin_I_subset_inn (hAI a ha)
  obtain ⟨A₀, hA₀el, hA₀card⟩ :=
    CFSG.RankThree.PartOne.K133.exists_elemAb_card_eq_of_le_inner
      (center_linProj_eq_bot (K := K)) hAab.isElementaryAbelian hAle
  have hA₀ab : IsElemAbelian p A₀ := CFSG.Open.isElemAbelian_of_isElementaryAbelian
  let e : LargeEvenProj (LargeEvenSLGroup (Fin 2) K) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K :=
    (TypeA.recipeEquiv 2 K).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSLTwoEquivSL K)
  let A₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) := A₀.map e.toMonoidHom
  have hA₁ : IsElemAbelian p A₁ := CFSG.Open.IsElemAbelian.map hA₀ab e.toMonoidHom
  have hcard₁ : Nat.card A₁ = Nat.card A₀ := Subgroup.card_map_of_injective e.injective
  have hle := TableBExcSmallRest.card_le_of_isElemAbelian_sl2 hp hp2 hA₁
  have hle' : p ^ 2 ≤ p := by
    calc p ^ 2 ≤ Nat.card A := hAcard
      _ = Nat.card A₀ := hA₀card.symm
      _ = Nat.card A₁ := hcard₁.symm
      _ ≤ p := hle
  have hp_lt : p < p ^ 2 := by
    have := Nat.pow_lt_pow_right hp.one_lt (show 1 < 2 by norm_num)
    simpa using this
  exact absurd hle' (not_le.mpr hp_lt)

theorem ggL45NtVacOn_rankOne :
    GGL45NtVacOn fun p lab => GGL45FamNonTorsion p lab ∧
      ((lab.tag = .A ∧ lab.rank = 1) ∨ (lab.tag = .twD ∧ lab.rank = 2)) := by
  intro p hp hp2 lab hlab _hkg hS Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  rcases hS with ⟨_hnt, hcond⟩
  rcases hcond with ⟨htag, hrank⟩ | ⟨htag, hrank⟩
  · subst htag
    subst hrank
    have hn : 1 ≤ n := by
      have := hlab
      simp only [LargeEvenInLambda2] at this
      exact this.1
    simp only [LargeEvenRawDatum, LargeEvenRecipeLinear, ↓reduceIte] at hQ ⊢
    exact ggL45NtVacRank1_linear hp hp2 ⟨n, hn, rfl⟩ hQ
  · subst htag
    subst hrank
    have hn : 1 ≤ n := by
      have := hlab
      simp only [LargeEvenInLambda2] at this
      exact this.1
    simp only [LargeEvenRawDatum, LargeEvenRecipeLinear, ↓reduceIte] at hQ ⊢
    refine ggL45NtVacRank1_linear hp hp2 ⟨2 * n, by omega, ?_⟩ hQ
    rw [← pow_mul, mul_comm n 2]

end CFSG.StandardType

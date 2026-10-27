module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSmallShapes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC163Alt
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenThirteen
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LieType.BorelTits (orthGroup statedOmega_le_orthGroup)
open CFSG.ClassicalGroups.Orthogonal (toLinEquiv closure_isometries_eq_comap)

variable {Y : Type} [Group Y] [Finite Y]

private theorem w183_isSolvable_statedProj_statedOmega_le_two
    {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [CharP K 2]
    (Q₀ : (ι → K) → K) (Q : QuadraticForm K (ι → K)) (hQ : ⇑Q = Q₀)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank K (ι → K) ≤ 2) :
    Group.IsSolvable (StatedProj (StatedOmega Q₀)) := by
  have : Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup Q) :=
    CFSG.StandardType.LayerCores.OrthRegular.isSolvable_orthogonalGroup_of_finrank_le_two
      hnd hdim
  have hEq : orthGroup Q₀ =
      (TauCeti.QuadraticMap.orthogonalGroup Q).comap (toLinEquiv ι K).toMonoidHom :=
    closure_isometries_eq_comap (Q := Q) (Q₀ := Q₀) hQ
  have hOrth : Group.IsSolvable ↥(orthGroup Q₀) := by
    have hmap : (orthGroup Q₀).map (toLinEquiv ι K).toMonoidHom =
        TauCeti.QuadraticMap.orthogonalGroup Q := by
      rw [hEq]
      exact Subgroup.map_comap_eq_self_of_surjective
        (toLinEquiv ι K).surjective _
    let e := ((orthGroup Q₀).equivMapOfInjective
      (toLinEquiv ι K).toMonoidHom (toLinEquiv ι K).injective).trans
        (MulEquiv.subgroupCongr hmap)
    exact Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom) e.injective
  have := hOrth
  have : Group.IsSolvable ↥(StatedOmega Q₀) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (statedOmega_le_orthGroup Q₀))
      (Subgroup.inclusion_injective _)
  exact Group.isSolvable_of_surjective
    (QuotientGroup.mk'_surjective ((StatedScalars ι K).subgroupOf (StatedOmega Q₀)))

private theorem w183_four_le_of_isOmegaPlus
    {X : Type} [Group X] {n a : ℕ}
    (hq : CFSG.Open.IsQuasisimple X) (hshape : IsOmegaPlus X n a) :
    4 ≤ n := by
  by_contra hlt
  have hev : Even n := hshape.1
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hshape
  let := hKf
  let := hKfin
  have : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hKcard
  have hsolv : ∀ r : ℕ, r ≤ 1 →
      Group.IsSolvable (StatedProj (StatedOmega (StatedQuadPlus r K))) := by
    intro r hr
    have hQ : ⇑(CFSG.LieType.Universal.Spin.quadPlus r K) = StatedQuadPlus r K :=
      CFSG.LieType.Universal.Spin.coe_quadPlus r K
    have hnd : (QuadraticMap.polarBilin
        (CFSG.LieType.Universal.Spin.quadPlus r K)).Nondegenerate :=
      CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus r K
    have hdim : Module.finrank K (Fin r ⊕ Fin r → K) ≤ 2 := by
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      omega
    exact w183_isSolvable_statedProj_statedOmega_le_two (StatedQuadPlus r K)
      (CFSG.LieType.Universal.Spin.quadPlus r K) hQ hnd hdim
  have hn : n = 0 ∨ n = 2 := by
    obtain ⟨k, hk⟩ := hev
    omega
  rcases hn with rfl | rfl
  · have hdiv : (0 : ℕ) / 2 = 0 := by norm_num
    have : Group.IsSolvable (StatedProj (StatedOmega (StatedQuadPlus (0 / 2) K))) := by
      simpa [hdiv] using hsolv 0 (by norm_num)
    have : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact CFSG.ClassicalInvolution.not_isSolvable_of_open_isQuasisimple hq inferInstance
  · have hdiv : (2 : ℕ) / 2 = 1 := by norm_num
    have : Group.IsSolvable (StatedProj (StatedOmega (StatedQuadPlus (2 / 2) K))) := by
      simpa [hdiv] using hsolv 1 (by norm_num)
    have : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact CFSG.ClassicalInvolution.not_isSolvable_of_open_isQuasisimple hq inferInstance

private theorem w183_four_le_of_isOmegaMinus
    {X : Type} [Group X] {n a : ℕ}
    (hq : CFSG.Open.IsQuasisimple X) (hshape : IsOmegaMinus X n a) :
    4 ≤ n := by
  by_contra hlt
  have hev : Even n := hshape.1
  obtain ⟨-, K, hKf, hKfin, b, c, hKcard, hirr, ⟨e⟩⟩ := hshape
  let := hKf
  let := hKfin
  have : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hKcard
  have hsolv : ∀ r : ℕ, r ≤ 1 →
      Group.IsSolvable (StatedProj (StatedOmega (StatedQuadMinus r K b c))) := by
    intro r hr
    have hQ : ⇑(CFSG.LieType.Universal.Spin.quadMinus r K b c) = StatedQuadMinus r K b c :=
      CFSG.LieType.Universal.Spin.coe_quadMinus (n := r) (K := K) b c
    have hnd : (QuadraticMap.polarBilin
        (CFSG.LieType.Universal.Spin.quadMinus r K b c)).Nondegenerate :=
      CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite
        (n := r) (K := K) hirr
    have hdim : Module.finrank K (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K) ≤ 2 := by
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      omega
    exact w183_isSolvable_statedProj_statedOmega_le_two (StatedQuadMinus r K b c)
      (CFSG.LieType.Universal.Spin.quadMinus r K b c) hQ hnd hdim
  have hn : n = 0 ∨ n = 2 := by
    obtain ⟨k, hk⟩ := hev
    omega
  rcases hn with rfl | rfl
  · have hdiv : (0 : ℕ) / 2 = 0 := by norm_num
    have : Group.IsSolvable (StatedProj (StatedOmega (StatedQuadMinus (0 / 2) K b c))) := by
      simpa [hdiv] using hsolv 0 (by norm_num)
    have : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact CFSG.ClassicalInvolution.not_isSolvable_of_open_isQuasisimple hq inferInstance
  · have hdiv : (2 : ℕ) / 2 = 1 := by norm_num
    have : Group.IsSolvable (StatedProj (StatedOmega (StatedQuadMinus (2 / 2) K b c))) := by
      simpa [hdiv] using hsolv 1 (by norm_num)
    have : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact CFSG.ClassicalInvolution.not_isSolvable_of_open_isQuasisimple hq inferInstance

private theorem w183_pRank_le_one_of_isOmegaMinus_four
    {X : Type} [Group X] [Finite X] {a : ℕ} (ha : 1 ≤ a) (hshape : IsOmegaMinus X 4 a)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    CFSG.Open.pRank q (⊤ : Subgroup X) ≤ 1 :=
  pRank_le_one_of_isL2_or_isSz
    (Or.inl (S18.isL2_of_isOmegaMinus_four ha hshape)) hq hq2

theorem s16nt_range_omPlus {n a : ℕ} (hq : CFSG.Open.IsQuasisimple Y)
    (hnt : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 2 ≤ CFSG.Open.pRank q (⊤ : Subgroup Y))
    (h : IsOmegaPlus Y n a) : 6 ≤ n := by
  by_cases ha1 : a = 1
  · subst ha1
    exact s16k_six_le_of_isOmegaPlus hq h
  · have ha2 : 2 ≤ a := by
      obtain ⟨K, hKf, hKfin, hKcard, -⟩ := h.2
      let := hKf
      let := hKfin
      have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
      have h1 : 1 ≤ a := by
        by_contra hlt
        have ha0 : a = 0 := by omega
        rw [ha0, pow_zero] at hKcard
        omega
      by_contra hlt
      exact ha1 (by omega)
    have h4 : 4 ≤ n := w183_four_le_of_isOmegaPlus hq h
    have hne4 : n ≠ 4 := by
      intro hn4
      exact C163.not_isQuasisimple_of_isOmegaPlus_four ha2 (hn4 ▸ h) hq
    obtain ⟨k, hk⟩ := h.1
    omega

theorem s16nt_range_omMinus {n a : ℕ} (hq : CFSG.Open.IsQuasisimple Y)
    (hnt : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 2 ≤ CFSG.Open.pRank q (⊤ : Subgroup Y))
    (h : IsOmegaMinus Y n a) : 6 ≤ n := by
  have ha1 : 1 ≤ a := by
    obtain ⟨K, hKf, hKfin, b, c, hKcard, -, -⟩ := h.2
    let := hKf
    let := hKfin
    have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
    by_contra hlt
    have ha0 : a = 0 := by omega
    rw [ha0, pow_zero] at hKcard
    omega
  have h4 : 4 ≤ n := by
    by_cases haeq : a = 1
    · subst haeq
      exact s16k_four_le_of_isOmegaMinus hq h
    · exact w183_four_le_of_isOmegaMinus hq h
  have hne4 : n ≠ 4 := by
    intro hn4
    obtain ⟨q, hqp, hq2, hqge⟩ := hnt
    have := w183_pRank_le_one_of_isOmegaMinus_four ha1 (hn4 ▸ h) hqp hq2
    omega
  obtain ⟨k, hk⟩ := h.1
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end

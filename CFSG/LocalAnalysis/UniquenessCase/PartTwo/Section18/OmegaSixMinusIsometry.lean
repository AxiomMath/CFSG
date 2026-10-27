module

public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixed
public import Mathlib.RingTheory.Coalgebra.CoassocSimps

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.ClassicalGroups.Orthogonal QuadraticMap

variable {K V V' : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
  {Q : QuadraticForm K V} {Q' : QuadraticForm K V'}

private lemma polar_isometry_T2J4a (e : V ≃ₗ[K] V') (he : ∀ x, Q' (e x) = Q x) (x y : V) :
    polar Q' (e x) (e y) = polar Q x y := by
  simp only [polar, ← map_add, he]

private lemma trans_eichler_T2J4a (e : V ≃ₗ[K] V') (he : ∀ x, Q' (e x) = Q x) (u w : V) :
    e.symm.trans ((eichler Q u w).trans e) = eichler Q' (e u) (e w) := by
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · have h' : Q' (e u) = 0 ∧ polar Q' (e u) (e w) = 0 :=
      ⟨by rw [he, h.1], by rw [polar_isometry_T2J4a e he, h.2]⟩
    refine LinearEquiv.ext fun x' => ?_
    obtain ⟨x, rfl⟩ : ∃ x, e x = x' := ⟨e.symm x', e.apply_symm_apply x'⟩
    rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.trans_apply,
      eichler_apply h.1 h.2, eichler_apply h'.1 h'.2]
    simp only [map_sub, map_add, map_smul, polar_isometry_T2J4a e he, he]
  · have h' : ¬(Q' (e u) = 0 ∧ polar Q' (e u) (e w) = 0) := fun hc =>
      h ⟨(he u).symm.trans hc.1, (polar_isometry_T2J4a e he u w).symm.trans hc.2⟩
    rw [eichler_of_not h, eichler_of_not h']
    refine LinearEquiv.ext fun x => ?_
    simp

private lemma trans_eichler_symm_T2J4a (e : V ≃ₗ[K] V') (he : ∀ x, Q' (e x) = Q x)
    (u' w' : V') :
    e.trans ((eichler Q' u' w').trans e.symm) = eichler Q (e.symm u') (e.symm w') := by
  have he' : ∀ y : V', Q (e.symm y) = Q' y := fun y => by
    rw [← he (e.symm y), e.apply_symm_apply]
  simpa using trans_eichler_T2J4a (Q := Q') (Q' := Q) e.symm he' u' w'

private def conjMulEquiv_T2J4a (e : V ≃ₗ[K] V') :
    (V ≃ₗ[K] V) ≃* (V' ≃ₗ[K] V') :=
  MulEquiv.mk'
    { toFun := fun g => e.symm.trans (g.trans e)
      invFun := fun g' => e.trans (g'.trans e.symm)
      left_inv := by
        intro g
        ext x
        simp [LinearEquiv.trans_apply]
      right_inv := by
        intro g'
        ext x
        simp [LinearEquiv.trans_apply] }
    (by
      intro g h
      ext x
      simp [LinearEquiv.trans_apply])

theorem exists_mulEquiv_gom_of_isometry (e : V ≃ₗ[K] V') (he : ∀ x, Q' (e x) = Q x) :
    ∃ ψ : Gom Q ≃* Gom Q', ∀ (g : Gom Q) (x : V), (ψ g).app (e x) = e (g.app x) := by
  let c := conjMulEquiv_T2J4a e
  have hc_apply : ∀ g : V ≃ₗ[K] V, c g = e.symm.trans (g.trans e) := fun g => rfl
  have hc_symm_apply : ∀ g' : V' ≃ₗ[K] V', c.symm g' = e.trans (g'.trans e.symm) := fun g' => rfl
  have h1 : (elementaryGroup Q).map (c : (V ≃ₗ[K] V) →* (V' ≃ₗ[K] V')) ≤ elementaryGroup Q' := by
    rw [Subgroup.map_le_iff_le_comap]
    refine elementaryGroup_le_of_eichler_mem fun u w _ _ => ?_
    rw [Subgroup.mem_comap]
    show c (eichler Q u w) ∈ elementaryGroup Q'
    rw [hc_apply, trans_eichler_T2J4a e he u w]
    exact eichler_mem_elementaryGroup Q' (e u) (e w)
  have h2 : elementaryGroup Q' ≤
      (elementaryGroup Q).comap (c.symm : (V' ≃ₗ[K] V') →* (V ≃ₗ[K] V)) := by
    refine elementaryGroup_le_of_eichler_mem fun u' w' _ _ => ?_
    rw [Subgroup.mem_comap]
    show c.symm (eichler Q' u' w') ∈ elementaryGroup Q
    rw [hc_symm_apply, trans_eichler_symm_T2J4a e he u' w']
    exact eichler_mem_elementaryGroup Q (e.symm u') (e.symm w')
  have hmap : (elementaryGroup Q).map (c : (V ≃ₗ[K] V) →* (V' ≃ₗ[K] V')) = elementaryGroup Q' := by
    refine le_antisymm h1 ?_
    rw [← Subgroup.map_equiv_eq_comap_symm c (elementaryGroup Q)] at h2
    exact h2
  refine ⟨(c.subgroupMap (elementaryGroup Q)).trans (MulEquiv.subgroupCongr hmap), ?_⟩
  intro g x
  show ((c.subgroupMap (elementaryGroup Q)).trans (MulEquiv.subgroupCongr hmap) g :
    V' ≃ₗ[K] V') (e x) = e ((g : V ≃ₗ[K] V) x)
  simp [MulEquiv.trans_apply, hc_apply, LinearEquiv.trans_apply]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

end

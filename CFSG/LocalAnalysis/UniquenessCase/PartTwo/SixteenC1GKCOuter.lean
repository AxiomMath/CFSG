module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GKCForm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LargeExtraspecial.O62 CFSG.RankThree.OrthogonalInvolutions QuadraticMap

theorem s16c1c_sq_eq_one_of_vanish {g : V₀ ≃ₗ[ZMod 2] V₀} (hg : g ∈ O₀ true)
    (hz : ∀ v : V₀, qModel true (g v - v) = 0) : g * g = 1 := by
  have hiso : ∀ v, qModel true (g v) = qModel true v :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hg
  have h1 : ∀ v, polar (qModel true) (g v) v = 0 := by
    intro v
    have h := hz v
    rw [CharTwo.sub_eq_add, QuadraticMap.map_add (qModel true), hiso] at h
    rwa [CharTwo.add_self_eq_zero, zero_add] at h
  have h2 : ∀ v w, polar (qModel true) (g v) w = polar (qModel true) (g w) v := by
    intro v w
    have h := h1 (v + w)
    rw [map_add, polar_add_left, polar_add_right, polar_add_right, h1, h1, zero_add, add_zero] at h
    exact (CharTwo.add_eq_zero.1 h)
  have h3 : ∀ x y, polar (qModel true) (g x) (g y) = polar (qModel true) x y := by
    intro x y
    have : g x + g y = g (x + y) := (map_add g x y).symm
    simp only [polar, this, hiso]
  have h4 : ∀ v w, polar (qModel true) (g (g v) - v) w = 0 := by
    intro v w
    rw [polar_sub_left, h2 (g v) w, h3 w v, polar_comm, sub_self]
  have h5 : ∀ v, g (g v) - v = 0 := fun v =>
    (qModel_nondegenerate true).1 _ fun w => by
      rw [QuadraticMap.polarBilin_apply_apply]
      exact h4 v w
  refine LinearEquiv.ext fun v => ?_
  have := h5 v
  rw [sub_eq_zero] at this
  simpa using this

theorem s16c1c_outerNons {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {β : W ≃* Multiplicative V₀} (hβ : IsOmegaModel H β) : OmegaOuterNons H := by
  intro Q hQ hQH x hx hxH
  obtain ⟨g, rfl⟩ := s16c1G44_kappa_surjective β x
  have hgO : g ∈ O₀ true := s16c1c_mem_O_of_mem_normalizer hβ hx
  have hgΩ : g ∉ Ω₀ true := fun hg => hxH ((s16c1G_mem_H_iff hβ _).2 ⟨g, hg, rfl⟩)
  by_contra hcon
  have hzero : ∀ w, Q (s16c1G_kappa β g w * w⁻¹) = 0 := fun w =>
    by_contra fun h => hcon ⟨w, h⟩
  have hv : ∀ v : V₀, qModel true (g v - v) = 0 := by
    intro v
    have h := hzero (β.symm (Multiplicative.ofAdd v))
    rw [s16c1c_form_eq hβ hQ.1 hQH, map_mul, map_inv, s16c1G_kappa_apply] at h
    simpa [sub_eq_add_neg] using h
  have hsq := s16c1c_sq_eq_one_of_vanish hgO hv
  have hzero' : ∀ y ∈ commSpace g, qModel true y = 0 := by
    intro y hy
    obtain ⟨v, rfl⟩ := mem_commSpace.1 hy
    exact hv v
  have heven := even_finrank_commSpace_of_forall_eq_zero (qModel_nondegenerate true) hgO hsq hzero'
  exact hgΩ ⟨hgO, heven⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

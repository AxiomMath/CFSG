module

public import CFSG.Timmesfeld.Moufang.Criterion

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G] {D : Set G}

theorem mem_rootSet_of_forall_commute [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    {y t : G} (hy : y ∈ D) (ht : t ∈ D) (h : ∀ f ∈ D, Commute y f → Commute t f) :
    t ∈ rootSet D y := by
  classical
  set Sy : Set G := {f | f ∈ D ∧ Commute y f} with hSy
  set St : Set G := {f | f ∈ D ∧ Commute t f} with hSt
  have hsub : Sy ⊆ St := fun f hf => ⟨hf.1, h f hf.1 hf.2⟩
  obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_of_isClass hclass hy ht)
  have himage : (fun x => g * x * g⁻¹) '' Sy = St := by
    ext f
    constructor
    · rintro ⟨x, ⟨hxD, hyx⟩, rfl⟩
      refine ⟨conj_mem_of_isClass hclass g hxD, ?_⟩
      rw [← hg]
      exact (Commute.conj_iff g).2 hyx
    · rintro ⟨hfD, htf⟩
      refine ⟨g⁻¹ * f * g⁻¹⁻¹, ⟨conj_mem_of_isClass hclass g⁻¹ hfD, ?_⟩, by group⟩
      have := (Commute.conj_iff g⁻¹).2 htf
      rwa [← hg, show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at this
  have hcard : St.ncard ≤ Sy.ncard := by
    rw [← himage]
    exact Set.ncard_image_le (Set.toFinite _)
  have heq : Sy = St := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  refine ⟨ht, fun f hf => ⟨fun htf => ?_, fun hyf => h f hf hyf⟩⟩
  have : f ∈ Sy := heq ▸ ⟨hf, htf⟩
  exact this.2

theorem commute_or_special_of_collinear (hD : IsRootInvolutionSet D) {x y f : G} (hy : y ∈ D)
    (hx : x ∈ D) (hxy : Commute x y) (hxyD : x * y ∈ D) (hf : f ∈ D) (hfy : Commute f y) :
    Commute f x ∨ orderOf (f * x) = 4 := by
  rcases hD.orderOf_mul hf hx with h | h | h
  · exact Or.inl ((commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hf)
      (hD.mul_self_eq_one hx)).2 (by rw [← h, pow_orderOf_eq_one]))
  · exact Or.inr h
  · have h1 := eq_of_collinear_of_odd hD hy hxy hxyD hf hfy h
    have : f = x := (mul_eq_one_iff_eq_inv.1 h1).trans (hD.inv_eq hx)
    exact Or.inl (this ▸ Commute.refl f)

end CFSG.Timmesfeld.Bridge

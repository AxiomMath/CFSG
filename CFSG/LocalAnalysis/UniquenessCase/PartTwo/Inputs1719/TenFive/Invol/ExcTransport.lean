module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Map

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

theorem exists_inv_of_injective_conj {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) {C : Subgroup G} (β : MulAut C) (z : G')
    (hβz : ∀ u : C, f (β u : G) = z * f (u : G) * z⁻¹)
    {y : G'} (hy : y ∈ Subgroup.normalizer ((C.map f : Subgroup G') : Set G'))
    {Q : C → Prop} (hQ : ∀ θ : C →* C, Function.Injective θ → ∀ w, Q w → Q (θ w)) {w₀ : C}
    (hw₀ : Q w₀) (hinv : y * z * y⁻¹ * f (w₀ : G) * (y * z * y⁻¹)⁻¹ = (f (w₀ : G))⁻¹) :
    ∃ w : C, β w = w⁻¹ ∧ Q w := by
  have hmem : ∀ u : C, y⁻¹ * f (u : G) * y ∈ C.map f := by
    intro u
    refine (Subgroup.mem_set_normalizer_iff.mp hy (y⁻¹ * f (u : G) * y)).mpr ?_
    have h : y * (y⁻¹ * f (u : G) * y) * y⁻¹ = f (u : G) := by group
    rw [h]
    exact Subgroup.mem_map_of_mem f u.2
  let H : Subgroup G' := C.map f
  let φ : C →* G' := (MulAut.conj y⁻¹).toMonoidHom.comp (f.comp C.subtype)
  have hφ : ∀ u : C, φ u ∈ H := by
    intro u
    simpa [φ, H, MulAut.conj_apply] using hmem u
  let θ : C →* C := (Subgroup.equivMapOfInjective C f hf).symm.toMonoidHom.comp
    (φ.codRestrict H hφ)
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h1 : f (a : G) = f (b : G) := (MulAut.conj y⁻¹).injective hab
    exact Subtype.ext (hf h1)
  have hcr : Function.Injective (φ.codRestrict H hφ) :=
    (MonoidHom.injective_codRestrict φ H hφ).mpr hφinj
  have hθinj : Function.Injective θ := by
    intro a b hab
    exact hcr ((Subgroup.equivMapOfInjective C f hf).symm.injective hab)
  have hfθ : ∀ u : C, f (θ u : G) = y⁻¹ * f (u : G) * y := by
    intro u
    have happ : (Subgroup.equivMapOfInjective C f hf) (θ u) = φ.codRestrict H hφ u := by
      simp [θ]
    rw [← Subgroup.coe_equivMapOfInjective_apply C f hf (θ u), happ]
    simp [φ]
  let w : C := θ w₀
  refine ⟨w, ?_, hQ θ hθinj w₀ hw₀⟩
  refine Subtype.ext (hf ?_)
  have hw : f ((w : C) : G) = y⁻¹ * f ((w₀ : C) : G) * y := by
    simpa [w] using hfθ w₀
  rw [hβz w, hw, Subgroup.coe_inv, map_inv, hw]
  have hA : z * (y⁻¹ * f ((w₀ : C) : G) * y) * z⁻¹ =
      y⁻¹ * (y * z * y⁻¹ * f ((w₀ : C) : G) * (y * z * y⁻¹)⁻¹) * y := by
    group
  rw [hA, hinv]
  group

theorem exists_inv_good_of_injective_conj {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) {C : Subgroup G} (β : MulAut C) (z : G')
    (hβz : ∀ u : C, f (β u : G) = z * f (u : G) * z⁻¹)
    {y : G'} (hy : y ∈ Subgroup.normalizer ((C.map f : Subgroup G') : Set G'))
    {p : ℕ} {w₀ : C} (hw₀ : orderOf w₀ = p) (hgood : IsSpecialGood p w₀)
    (hinv : y * z * y⁻¹ * f (w₀ : G) * (y * z * y⁻¹)⁻¹ = (f (w₀ : G))⁻¹) :
    ∃ w : C, orderOf w = p ∧ β w = w⁻¹ ∧ IsSpecialGood p w := by
  obtain ⟨w, hw, hwo, hwg⟩ := exists_inv_of_injective_conj f hf β z hβz hy
    (Q := fun w => orderOf w = p ∧ IsSpecialGood p w)
    (fun θ hθ w hw => ⟨(orderOf_injective θ hθ w).trans hw.1, hw.2.map hθ⟩) ⟨hw₀, hgood⟩ hinv
  exact ⟨w, hwo, hw, hwg⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

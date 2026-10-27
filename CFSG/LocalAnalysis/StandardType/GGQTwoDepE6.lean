module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDepLin
public import CFSG.LocalAnalysis.StandardType.GGQTwoDepE6Lin
public import CFSG.LocalAnalysis.StandardType.GGQTwoFinishGen

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem lr7sf_weyl_lift {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K) :
    ∀ w ∈ M.toLin.weyl, ∃ ψ ∈ ggAutomizer (L ⊔ K) Bs, ggLin (p := p) M.model ψ = w := by
  intro w hw
  have hle : M.toLin.weyl ≤ (ggAutomizer (L ⊔ K) Bs).map (ggLin (p := p) M.model) := by
    have hpar : M.toLin.weyl =
        (Subgroup.closure (M.simple '' Set.univ)).map (ggLin (p := p) M.model) := by
      rw [show M.toLin.weyl = M.parabL Set.univ from rfl, ggQ2_parabL_eq_map]
    rw [hpar]
    refine Subgroup.map_mono ?_
    refine (Subgroup.closure_le (ggAutomizer (L ⊔ K) Bs)).mpr ?_
    rintro t ⟨k, -, rfl⟩
    by_cases hk : k ≠ M.a
    · exact ggAutomizer_mono Bs le_sup_left
        (by rw [M.automizer_L]; exact Subgroup.subset_closure ⟨k, hk, rfl⟩)
    · have hka : k = M.a := by simpa using hk
      have hkb : k ≠ M.b := by rw [hka]; exact M.a_ne_b
      exact ggAutomizer_mono Bs le_sup_right
        (by rw [M.automizer_K]; exact Subgroup.subset_closure ⟨k, hkb, rfl⟩)
  obtain ⟨ψ, hψ, hψw⟩ := hle hw
  exact ⟨ψ, hψ, hψw⟩

theorem ggQ2_e6_automizer_le (hHeart : GGQ2HeartInput) (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p = 3) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hAJ : ggAutomizer J Bs ≠ ⊥)
    (hK1 : GGQTwoK1 p B Bs x D J) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (M : GGQTwoModel p Bs x y D L J K) (e : Fin 6 ≃ M.ι)
    (hE : M.coxeter = CoxeterMatrix.E₆.reindex e) (ha : M.a = e 1) :
    ggAutomizer ⊤ Bs ≤ ggAutomizer (Subgroup.normalizer (ggG0 p B x L D J : Set G)) Bs := by
  subst hp
  have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have : FiniteDimensional (ZMod 3) M.V := Module.Finite.of_finite
  have : FiniteDimensional (ZMod 3) M.toLin.V := ‹FiniteDimensional (ZMod 3) M.V›
  have hxne : x ≠ 1 := hS.1.1.1.2.2.2.2.2.2.1.2.2.1
  have hx0 : M.xV ≠ 0 := by
    intro h
    have h0 : Additive.ofMul (⟨x, M.hx⟩ : ↥Bs) = 0 :=
      M.model.injective (by rw [map_zero]; exact h)
    have h1 : (⟨x, M.hx⟩ : ↥Bs) = 1 :=
      Additive.ofMul.injective (by simpa using h0)
    exact hxne (Subtype.ext_iff.mp h1)
  have hx := (ggQ2_fixed_lin M).1
  have hW := ggQ2_weyl_le_lin M
  have hTF : TransvectionFree M.linGroup := ggQ2_transvectionFree M hS.1.2.2.2.1
  have hpm := ggQ2_e6_pm hHeart M.toLin e hE ha M.xV hx0 hx M.linGroup hW hTF
  intro φ hφ
  have hφlin : ggLin (p := 3) M.model φ ∈ M.linGroup :=
    Subgroup.mem_map.mpr ⟨φ, hφ, rfl⟩
  obtain ⟨g, hgW, hgcase⟩ := hpm (ggLin (p := 3) M.model φ) hφlin
  let g' : M.V ≃ₗ[ZMod 3] M.V := g
  have hgW' : g' ∈ M.toLin.weyl := hgW
  have hgcase' : (∀ v : M.V, ggLin (p := 3) M.model φ v = g' v) ∨
      (∀ v : M.V, ggLin (p := 3) M.model φ v = -(g' v)) := hgcase
  obtain ⟨ψ₀, hψ₀, hψ₀g⟩ := lr7sf_weyl_lift (p := 3) M g' hgW'
  have hcase : (∀ v, ggLin (p := 3) M.model (ψ₀⁻¹ * φ) v = v) ∨
      (∀ v, ggLin (p := 3) M.model (ψ₀⁻¹ * φ) v = -v) := by
    rcases hgcase' with h | h
    · left
      intro v
      rw [map_mul, LinearEquiv.mul_apply, map_inv, hψ₀g]
      rw [show ggLin (p := 3) M.model φ v = g' v from h v]
      exact LinearEquiv.symm_apply_apply g' v
    · right
      intro v
      rw [map_mul, LinearEquiv.mul_apply, map_inv, hψ₀g]
      rw [show ggLin (p := 3) M.model φ v = -(g' v) from h v]
      rw [map_neg]
      exact congrArg Neg.neg (LinearEquiv.symm_apply_apply g' v)
  refine ggQ2_finish_of_le hLB hP hS hAJ hK1 hnb (H := L ⊔ K)
    (sup_le (le_ggG0_left _ _ _ _ _ _) (le_ggG0_of_ggNbr hnb)) hφ
    (Subgroup.inv_mem _ hψ₀) ?_
  intro b hbD
  rcases hcase with h | h
  · have hb' : (ψ₀⁻¹ * φ) b = b := by
      apply Additive.ofMul.injective
      apply M.model.injective
      rw [← ggLin_apply_ofMul (p := 3) M.model (ψ₀⁻¹ * φ) b, h]
    rw [hb']
    exact hbD
  · have hb' : (ψ₀⁻¹ * φ) b = b⁻¹ := by
      apply Additive.ofMul.injective
      apply M.model.injective
      rw [← ggLin_apply_ofMul (p := 3) M.model (ψ₀⁻¹ * φ) b, h, ofMul_inv, map_neg]
    rw [hb']
    simpa using D.inv_mem hbD

end CFSG.StandardType

end

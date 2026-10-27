module

public import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneNineIrred
public import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneNineReduce

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem exists_mixed_centre_data [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ h ∈ H, ∀ w ∈ W, h w ∈ W) → W = ⊥ ∨ W = ⊤)
    (htv : QTwoLin.TransvectionFree H) (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV H)
    {τ : ZMod p} {g : U ≃ₗ[ZMod p] U} {c : U} {φ : Module.Dual (ZMod p) U}
    (hn2 : 2 ≤ Module.finrank (ZMod p) U) (hn3 : 3 ≤ Module.finrank (ZMod p) U)
    (hg : g ∈ H) (hh : IsHomologyWith τ g c φ) (hτ1 : τ ≠ 1) (hτ2 : τ ^ 2 ≠ 1) :
    ∃ (β : U ≃ₗ[ZMod p] U) (c₂ : U) (φ₂ : Module.Dual (ZMod p) U)
      (γ : U ≃ₗ[ZMod p] U) (cγ : U) (φγ : Module.Dual (ZMod p) U),
      β ∈ H ∧ IsHomologyWith τ β c₂ φ₂ ∧ g * β ≠ β * g ∧
      IsCompl (Submodule.span (ZMod p) {c, c₂}) (LinearMap.ker φ ⊓ LinearMap.ker φ₂) ∧
      γ ∈ H ∧ IsHomologyWith τ γ cγ φγ ∧ cγ ∉ Submodule.span (ZMod p) {c, c₂} ∧
      cγ ∉ LinearMap.ker φ ⊓ LinearMap.ker φ₂ := by
  obtain ⟨h, hhH, hcommh⟩ :=
    exists_conj_not_commute_of_isHomologyWith hn2 hirr htv hprim hg hh hτ1
  have hβH : h * g * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hhH hg) (H.inv_mem hhH)
  have hβh : IsHomologyWith τ (h * g * h⁻¹) (h c)
      (φ ∘ₗ (h.symm : U →ₗ[ZMod p] U)) := hh.conj h
  have hcomm : g * (h * g * h⁻¹) ≠ (h * g * h⁻¹) * g := by simpa using hcommh
  have hWY : IsCompl (Submodule.span (ZMod p) {c, h c})
      (LinearMap.ker φ ⊓ LinearMap.ker (φ ∘ₗ (h.symm : U →ₗ[ZMod p] U))) :=
    isCompl_span_ker_inf_ker hh hβh
      (linked_of_not_commute htv hg hβH hh hβh hτ2 hcomm).2.2.2
  obtain ⟨h', h'hH, h'cW, h'cY⟩ :=
    exists_conj_centre_not_mem hn3 hirr htv hprim hg hβH hh hβh hτ1
  exact ⟨h * g * h⁻¹, h c, φ ∘ₗ (h.symm : U →ₗ[ZMod p] U),
    h' * g * h'⁻¹, h' c, φ ∘ₗ (h'.symm : U →ₗ[ZMod p] U),
    hβH, hβh, hcomm, hWY,
    H.mul_mem (H.mul_mem h'hH hg) (H.inv_mem h'hH), hh.conj h', h'cW, h'cY⟩

theorem orderOf_le_three_of_isHomologyWith [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} (hn : 3 ≤ Module.finrank (ZMod p) U)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ h ∈ H, ∀ w ∈ W, h w ∈ W) → W = ⊥ ∨ W = ⊤)
    (htv : QTwoLin.TransvectionFree H) (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV H)
    {τ : ZMod p} {g : U ≃ₗ[ZMod p] U} {c : U} {φ : Module.Dual (ZMod p) U} (hg : g ∈ H)
    (hh : IsHomologyWith τ g c φ) : orderOf τ ≤ 3 := by
  by_contra hle
  rw [not_le] at hle
  have h4 : 4 ≤ orderOf τ := by omega
  have hτ1 : τ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at h4
    omega
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h
    have hdvd : orderOf τ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
    have hle2 : orderOf τ ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  obtain ⟨β, c₂, φ₂, γ, cγ, φγ, hβH, hβh, hcomm, hWY, hγH, hγh, hcγW, hcγY⟩ :=
    exists_mixed_centre_data hirr htv hprim (le_trans (by norm_num) hn) hn hg hh hτ1 hτ2
  have hcγ : cγ ∈ Submodule.span (ZMod p) {c, c₂} ⊔
      (LinearMap.ker φ ⊓ LinearMap.ker φ₂) := by
    rw [codisjoint_iff.mp hWY.codisjoint]
    trivial
  obtain ⟨w, hwW, y, hyY, hwy⟩ := Submodule.mem_sup.mp hcγ
  have hy0 : y ≠ 0 := by
    intro hy
    apply hcγW
    rw [← hwy, hy, add_zero]
    exact hwW
  have hw0 : w ≠ 0 := by
    intro hw
    apply hcγY
    rw [← hwy, hw, zero_add]
    exact hyY
  have hy₁ : φ y = 0 := LinearMap.mem_ker.mp hyY.1
  have hy₂ : φ₂ y = 0 := LinearMap.mem_ker.mp hyY.2
  have hγh' : IsHomologyWith τ γ (w + y) φγ := by rw [← hwy] at hγh; exact hγh
  by_cases hz : φγ w = 0 ∨ φγ y = 0
  · exact false_of_mixed_centre_of_apply_eq_zero htv h4 hg hβH hγH hh hβh hγh' hcomm
      hwW hw0 hy₁ hy₂ hy0 hz
  · have hzw : φγ w ≠ 0 := fun h => hz (Or.inl h)
    have hzy : φγ y ≠ 0 := fun h => hz (Or.inr h)
    exact false_of_mixed_centre_of_apply_ne_zero htv h4 hg hβH hγH hh hβh hγh' hcomm
      hwW hy₁ hy₂ hzw hzy

end CFSG.StandardType.ZS

end

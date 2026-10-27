module

public import CFSG.LocalAnalysis.StandardType.ZS.MovedAction
import CFSG.LocalAnalysis.StandardType.ZS.SubgroupSpaces
import CFSG.LocalAnalysis.StandardType.ZS.ThroughRefl

public section

namespace CFSG.StandardType.ZS

variable (p : ℕ) [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

@[expose] def H3Frame (A : Subgroup (U ≃ₗ[ZMod p] U)) : Prop :=
  ∃ h₀ ∈ A, ∃ h₁ ∈ A, ∃ h₂ ∈ A, ∃ a ∈ A, IsRefl p h₀ ∧ IsRefl p h₁ ∧ IsRefl p h₂ ∧ IsRefl p a ∧
    h₀ ≠ h₁ ∧ h₀ ≠ h₂ ∧ h₁ ≠ h₂ ∧ Commute h₀ h₁ ∧ Commute h₀ h₂ ∧ Commute h₁ h₂ ∧
    orderOf (h₀ * a) = 5 ∧ orderOf (h₁ * a) = 5 ∧ orderOf (h₂ * a) = 3

@[expose] def J34Frame (A : Subgroup (U ≃ₗ[ZMod p] U)) : Prop :=
  ∃ s₀ ∈ A, ∃ s₁ ∈ A, ∃ s₂ ∈ A, ∃ a ∈ A, IsRefl p s₀ ∧ IsRefl p s₁ ∧ IsRefl p s₂ ∧ IsRefl p a ∧
    orderOf (s₀ * s₁) = 4 ∧ orderOf (s₁ * s₂) = 3 ∧ orderOf (s₀ * s₂) = 2 ∧
    orderOf (s₀ * a) = 3 ∧ orderOf (s₁ * a) = 3 ∧
    Commute a ((s₂ * s₁ * s₀ * (s₂ * s₁)⁻¹) * (s₁ * s₂ * s₁) * (s₂ * s₁ * s₀ * (s₂ * s₁)⁻¹)⁻¹)

variable {p}

private theorem commute_of_restrictHom_eq {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ}
    (hX : SplitSupport X l) {x y : X}
    (h : Commute
      (restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
        (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) x)
      (restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
        (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) y)) :
    Commute (x : U ≃ₗ[ZMod p] U) (y : U ≃ₗ[ZMod p] U) := by
  have hinj := restrictHom_injective_of_splitSupport hX
  have hxy : x * y = y * x := hinj (by rw [map_mul, map_mul]; exact h)
  exact congrArg (Subtype.val) hxy

private theorem orderOf_mul_of_restrictHom {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ}
    (hX : SplitSupport X l) (x y : X) :
    orderOf ((x : U ≃ₗ[ZMod p] U) * (y : U ≃ₗ[ZMod p] U)) =
      orderOf (restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
        (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) x *
        restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
        (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) y) := by
  have hinj := restrictHom_injective_of_splitSupport hX
  rw [← Subgroup.coe_mul, Subgroup.orderOf_coe,
    ← orderOf_injective (restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
      (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)) hinj (x * y), map_mul]

private theorem exists_isRefl_lift {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ}
    (hX : SplitSupport X l)
    {g : HardMathSupport.Kantor79.commutatorSpace X ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace X}
    (hg : g ∈ movedGroup X) (hgr : IsRefl p g) :
    ∃ x : X, IsRefl p (x : U ≃ₗ[ZMod p] U) ∧
      restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
        (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) x = g := by
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hg
  exact ⟨x, isRefl_of_isRefl_restrictHom hX (by rw [hx]; exact hgr), hx⟩

theorem H3Frame.of_movedGroup {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ} (hX : SplitSupport X l)
    (h : H3Frame p (movedGroup X)) : H3Frame p X := by
  unfold H3Frame at h
  obtain ⟨g₀, hg₀, g₁, hg₁, g₂, hg₂, ga, hga, hr₀, hr₁, hr₂, hra,
    hne₀₁, hne₀₂, hne₁₂, hc₀₁, hc₀₂, hc₁₂, ho₀, ho₁, ho₂⟩ := h
  obtain ⟨x₀, hrx₀, hx₀⟩ := exists_isRefl_lift hX hg₀ hr₀
  obtain ⟨x₁, hrx₁, hx₁⟩ := exists_isRefl_lift hX hg₁ hr₁
  obtain ⟨x₂, hrx₂, hx₂⟩ := exists_isRefl_lift hX hg₂ hr₂
  obtain ⟨xa, hrxa, hxa⟩ := exists_isRefl_lift hX hga hra
  refine ⟨x₀, x₀.2, x₁, x₁.2, x₂, x₂.2, xa, xa.2, hrx₀, hrx₁, hrx₂, hrxa,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hxy
    exact hne₀₁ (by rw [← hx₀, ← hx₁, Subtype.ext hxy])
  · intro hxy
    exact hne₀₂ (by rw [← hx₀, ← hx₂, Subtype.ext hxy])
  · intro hxy
    exact hne₁₂ (by rw [← hx₁, ← hx₂, Subtype.ext hxy])
  · exact commute_of_restrictHom_eq hX (by rw [hx₀, hx₁]; exact hc₀₁)
  · exact commute_of_restrictHom_eq hX (by rw [hx₀, hx₂]; exact hc₀₂)
  · exact commute_of_restrictHom_eq hX (by rw [hx₁, hx₂]; exact hc₁₂)
  · rw [orderOf_mul_of_restrictHom hX x₀ xa, hx₀, hxa, ho₀]
  · rw [orderOf_mul_of_restrictHom hX x₁ xa, hx₁, hxa, ho₁]
  · rw [orderOf_mul_of_restrictHom hX x₂ xa, hx₂, hxa, ho₂]

theorem J34Frame.of_movedGroup {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ} (hX : SplitSupport X l)
    (h : J34Frame p (movedGroup X)) : J34Frame p X := by
  unfold J34Frame at h
  obtain ⟨g₀, hg₀, g₁, hg₁, g₂, hg₂, ga, hga, hr₀, hr₁, hr₂, hra,
    ho₀₁, ho₁₂, ho₀₂, ho₀a, ho₁a, hcomm⟩ := h
  obtain ⟨x₀, hrx₀, hx₀⟩ := exists_isRefl_lift hX hg₀ hr₀
  obtain ⟨x₁, hrx₁, hx₁⟩ := exists_isRefl_lift hX hg₁ hr₁
  obtain ⟨x₂, hrx₂, hx₂⟩ := exists_isRefl_lift hX hg₂ hr₂
  obtain ⟨xa, hrxa, hxa⟩ := exists_isRefl_lift hX hga hra
  refine ⟨x₀, x₀.2, x₁, x₁.2, x₂, x₂.2, xa, xa.2, hrx₀, hrx₁, hrx₂, hrxa,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [orderOf_mul_of_restrictHom hX x₀ x₁, hx₀, hx₁, ho₀₁]
  · rw [orderOf_mul_of_restrictHom hX x₁ x₂, hx₁, hx₂, ho₁₂]
  · rw [orderOf_mul_of_restrictHom hX x₀ x₂, hx₀, hx₂, ho₀₂]
  · rw [orderOf_mul_of_restrictHom hX x₀ xa, hx₀, hxa, ho₀a]
  · rw [orderOf_mul_of_restrictHom hX x₁ xa, hx₁, hxa, ho₁a]
  · let w : X := x₂ * x₁ * x₀ * (x₂ * x₁)⁻¹ * (x₁ * x₂ * x₁) *
      (x₂ * x₁ * x₀ * (x₂ * x₁)⁻¹)⁻¹
    have hφw : (restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
        (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)) w =
        g₂ * g₁ * g₀ * (g₂ * g₁)⁻¹ * (g₁ * g₂ * g₁) * (g₂ * g₁ * g₀ * (g₂ * g₁)⁻¹)⁻¹ := by
      simp only [w, map_mul, map_inv, hx₀, hx₁, hx₂]
    exact commute_of_restrictHom_eq hX (x := xa) (y := w)
      (by simpa only [hxa, hφw] using hcomm)

theorem mem_commutatorSpace_of_reflection_mem (hp : p ≠ 2) {X : Subgroup (U ≃ₗ[ZMod p] U)}
    {a : U} {φ : Module.Dual (ZMod p) U} (hφ : φ a = 2) (hX : Module.reflection hφ ∈ X) :
    a ∈ HardMathSupport.Kantor79.commutatorSpace X := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hmem : Module.reflection hφ a - a ∈ HardMathSupport.Kantor79.commutatorSpace X :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hX ⟨a, rfl⟩
  have hsa : Module.reflection hφ a - a = (-2 : ZMod p) • a := by
    rw [Module.reflection_apply_self,
      show -a - a = -(a + a) by abel, ← two_smul (ZMod p) a, ← neg_smul]
    rfl
  have ha : a = (-2 : ZMod p)⁻¹ • (Module.reflection hφ a - a) := by
    rw [hsa, smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr h2), one_smul]
  rw [ha]
  exact Submodule.smul_mem _ _ hmem

theorem apply_eq_zero_of_reflection_mem (hp : p ≠ 2) {X : Subgroup (U ≃ₗ[ZMod p] U)}
    {a : U} {φ : Module.Dual (ZMod p) U} (hφ : φ a = 2) (hX : Module.reflection hφ ∈ X)
    {w : U} (hw : w ∈ centralizerSpace X) : φ w = 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have ha : a ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hφ
    exact h2 hφ.symm
  have hfix : Module.reflection hφ w = w :=
    (mem_centralizerSpace.mp hw) (Module.reflection hφ) hX
  have hsub : w - φ w • a = w := by
    rw [Module.reflection_apply] at hfix
    exact hfix
  have hneg : φ w • a = 0 := by
    have h1 : w - φ w • a - w = 0 := by rw [hsub, sub_self]
    have h2 : -(φ w • a) = 0 := by
      rw [show w - φ w • a - w = -(φ w • a) by abel] at h1
      exact h1
    exact neg_eq_zero.mp h2
  exact (smul_eq_zero.mp hneg).resolve_right ha

theorem exists_basis_snoc_of_splitSupport [Module.Finite (ZMod p) U]
    {X : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ} (hX : SplitSupport X l)
    (hU : Module.finrank (ZMod p) U = l + 1) {v : Fin l → U} (hv : LinearIndependent (ZMod p) v)
    (hvX : ∀ i, v i ∈ HardMathSupport.Kantor79.commutatorSpace X) :
    ∃ f : Module.Basis (Fin (l + 1)) (ZMod p) U,
      (∀ i, f (Fin.castSucc i) = v i) ∧ f (Fin.last l) ∈ centralizerSpace X := by
  obtain ⟨w, hwC, hw0⟩ := hX.exists_mem_centralizerSpace_ne_zero (by omega)
  have hwV : w ∉ Submodule.span (ZMod p) (Set.range v) := by
    intro hw
    have hwVX : w ∈ HardMathSupport.Kantor79.commutatorSpace X :=
      (Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hvX i)) hw
    have hinf : w ∈ HardMathSupport.Kantor79.commutatorSpace X ⊓ centralizerSpace X :=
      ⟨hwVX, hwC⟩
    rw [hX.1.inf_eq_bot] at hinf
    exact hw0 (by simpa using hinf)
  have hli : LinearIndependent (ZMod p) (Fin.snoc v w) := hv.finSnoc hwV
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp [hU]), ?_, ?_⟩
  · intro i
    rw [congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli (by simp [hU])) (Fin.castSucc i)]
    simp
  · rw [congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli (by simp [hU])) (Fin.last l),
      Fin.snoc_last]
    exact hwC

end CFSG.StandardType.ZS

end

module

public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxDefs

public section

open CFSG.RankThree.PartTwo.Sec19
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec4.E27

section Conj

variable {X : Type} [Field X] [Finite X]

theorem mem_cenX_conj_iff (σ : X ≃+* X) (h x k : C0 σ) :
    k ∈ cenX σ (h * x * h⁻¹) ↔ h⁻¹ * k * h ∈ cenX σ x := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hk
    calc h⁻¹ * k * h * x = h⁻¹ * (k * (h * x * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * x * h⁻¹) * k) * h := by rw [hk]
      _ = x * (h⁻¹ * k * h) := by group
  · intro hk
    calc k * (h * x * h⁻¹) = h * ((h⁻¹ * k * h) * x) * h⁻¹ := by group
      _ = h * (x * (h⁻¹ * k * h)) * h⁻¹ := by rw [hk]
      _ = h * x * h⁻¹ * k := by group

theorem layerSub_conj_iff (σ : X ≃+* X) (h x d : C0 σ) :
    d ∈ layerSub σ x ↔ h * d * h⁻¹ ∈ layerSub σ (h * x * h⁻¹) := by
  have hC : (cenX σ x).map (MulAut.conj h).toMonoidHom = cenX σ (h * x * h⁻¹) := by
    ext k
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [mem_cenX_conj_iff]
      simpa [MulAut.conj_apply, mul_assoc] using hc
    · intro hk
      refine ⟨h⁻¹ * k * h, (mem_cenX_conj_iff σ h x k).1 hk, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  have hL : (layerSub σ x).map (MulAut.conj h).toMonoidHom = layerSub σ (h * x * h⁻¹) := by
    show (⁅cenX σ x, cenX σ x⁆).map _ = ⁅cenX σ (h * x * h⁻¹), cenX σ (h * x * h⁻¹)⁆
    rw [Subgroup.map_commutator, hC]
  rw [← hL]
  constructor
  · intro hd
    exact ⟨d, hd, rfl⟩
  · rintro ⟨d', hd', hdd'⟩
    have : d' = d := (MulAut.conj h).injective hdd'
    rw [← this]
    exact hd'

@[expose] noncomputable def layerConjEquiv (σ : X ≃+* X) (h x : C0 σ) :
    layerSub σ x ≃* layerSub σ (h * x * h⁻¹) where
  toFun d := ⟨h * d * h⁻¹, (layerSub_conj_iff σ h x d).1 d.2⟩
  invFun d := ⟨h⁻¹ * d * h, (layerSub_conj_iff σ h x (h⁻¹ * d * h)).2 (by
    have : h * (h⁻¹ * (d : C0 σ) * h) * h⁻¹ = d := by group
    rw [this]
    exact d.2)⟩
  left_inv d := Subtype.ext (by simp [mul_assoc])
  right_inv d := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem coe_layerConjEquiv (σ : X ≃+* X) (h x : C0 σ) (d : layerSub σ x) :
    ((layerConjEquiv σ h x d : layerSub σ (h * x * h⁻¹)) : C0 σ) = h * d * h⁻¹ := rfl

theorem layerLinearModel_of_conj (σ : X ≃+* X) (h x : C0 σ)
    (hm : LayerLinearModel σ (h * x * h⁻¹)) : LayerLinearModel σ x := by
  obtain ⟨F, hF, hFin, h4, h3, e, he⟩ := hm
  refine ⟨F, hF, hFin, h4, h3, (layerConjEquiv σ h x).trans e, fun g hg => ?_⟩
  have hg' : h * g * h⁻¹ ∈ cenX σ (h * x * h⁻¹) := by
    rw [mem_cenX_conj_iff]
    simpa [mul_assoc] using hg
  obtain ⟨N, hN⟩ := he _ hg'
  refine ⟨N, fun d d' hdd' => ?_⟩
  exact hN (layerConjEquiv σ h x d) (layerConjEquiv σ h x d') (by
    rw [coe_layerConjEquiv, coe_layerConjEquiv, hdd']
    group)

theorem layerUnitaryModel_of_conj (σ : X ≃+* X) (n : ℕ) (h x : C0 σ)
    (hm : LayerUnitaryModel σ n (h * x * h⁻¹)) : LayerUnitaryModel σ n x := by
  obtain ⟨F, hF, hFd, e, he⟩ := hm
  refine ⟨F, hF, hFd, (layerConjEquiv σ h x).trans e, fun g hg => ?_⟩
  have hg' : h * g * h⁻¹ ∈ cenX σ (h * x * h⁻¹) := by
    rw [mem_cenX_conj_iff]
    simpa [mul_assoc] using hg
  obtain ⟨A, hA⟩ := he _ hg'
  refine ⟨A, fun d d' hdd' => ?_⟩
  exact hA (layerConjEquiv σ h x d) (layerConjEquiv σ h x d') (by
    rw [coe_layerConjEquiv, coe_layerConjEquiv, hdd']
    group)

end Conj

end CFSG.RankThree.PartTwo.Sec4.E27

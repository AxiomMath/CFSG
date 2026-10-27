module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.MS93.S512L

open scoped commutatorElement

variable {Γ : Type*} [Group Γ]

theorem commutatorElement_mem {H : Subgroup Γ} {x y : Γ} (hx : x ∈ H) (hy : y ∈ H) :
    ⁅x, y⁆ ∈ H := by
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)

theorem commutatorElement_mul_left_of_comm {x y z : Γ} (h : x * ⁅y, z⁆ = ⁅y, z⁆ * x) :
    ⁅x * y, z⁆ = ⁅y, z⁆ * ⁅x, z⁆ := by
  have e : ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e, h, mul_inv_cancel_right]

theorem commutatorElement_mul_right_of_comm {x y z : Γ} (h : y * ⁅x, z⁆ = ⁅x, z⁆ * y) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  have e : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e, h, mul_inv_cancel_right]

theorem commutatorElement_inv_left_of_comm {x z : Γ} (h : x * ⁅x, z⁆ = ⁅x, z⁆ * x) :
    ⁅x⁻¹, z⁆ = ⁅x, z⁆⁻¹ := by
  have e : ⁅x⁻¹, z⁆ = x⁻¹ * ⁅x, z⁆⁻¹ * x := by
    simp only [commutatorElement_def]
    group
  have h' : x⁻¹ * ⁅x, z⁆⁻¹ = ⁅x, z⁆⁻¹ * x⁻¹ := by
    calc x⁻¹ * ⁅x, z⁆⁻¹ = (⁅x, z⁆ * x)⁻¹ := by group
      _ = (x * ⁅x, z⁆)⁻¹ := by rw [h]
      _ = ⁅x, z⁆⁻¹ * x⁻¹ := by group
  rw [e, h', inv_mul_cancel_right]

theorem commutator_le_commutator_self {K V₀ Lt : Subgroup Γ}
    (hV₀K : V₀ ≤ K) (hKL : ⁅K, Lt⁆ ≤ V₀) (hV₀L : V₀ ≤ ⁅V₀, Lt⁆)
    (hLK : Lt ≤ Subgroup.normalizer (K : Set Γ)) (hLV₀ : Lt ≤ Subgroup.normalizer (V₀ : Set Γ))
    (hcen : ∀ x ∈ K, ∀ y ∈ K, ∀ z ∈ K, z * ⁅x, y⁆ = ⁅x, y⁆ * z)
    (hLc : ∀ x ∈ K, ∀ y ∈ K, ∀ l ∈ Lt, l * ⁅x, y⁆ = ⁅x, y⁆ * l) :
    ⁅V₀, K⁆ ≤ ⁅V₀, V₀⁆ := by
  rw [Subgroup.commutator_le]
  intro v hv w hw
  let P : Subgroup Γ :=
    { carrier := {u | u ∈ V₀ ∧ ⁅u, w⁆ ∈ ⁅V₀, V₀⁆}
      one_mem' := ⟨one_mem _, by rw [commutatorElement_one_left]; exact one_mem _⟩
      mul_mem' := by
        rintro u u' ⟨hu, hu₁⟩ ⟨hu', hu'₁⟩
        refine ⟨mul_mem hu hu', ?_⟩
        rw [commutatorElement_mul_left_of_comm (hcen _ (hV₀K hu') _ hw _ (hV₀K hu))]
        exact mul_mem hu'₁ hu₁
      inv_mem' := by
        rintro u ⟨hu, hu₁⟩
        refine ⟨inv_mem hu, ?_⟩
        rw [commutatorElement_inv_left_of_comm (hcen _ (hV₀K hu) _ hw _ (hV₀K hu))]
        exact inv_mem hu₁ }
  have hgen : ⁅V₀, Lt⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro u hu l hl
    have hu' : l * u⁻¹ * l⁻¹ ∈ V₀ := (Subgroup.mem_normalizer_iff.1 (hLV₀ hl) _).1 (inv_mem hu)
    have hcomm : ⁅u, l⁆ = u * (l * u⁻¹ * l⁻¹) := by
      rw [commutatorElement_def]
      group
    refine ⟨hcomm ▸ mul_mem hu hu', ?_⟩
    have hwl : l⁻¹ * w * l ∈ K := by
      have := (Subgroup.mem_normalizer_iff.1 (hLK (inv_mem hl)) w).1 hw
      simpa using this
    set d := ⁅w⁻¹, l⁻¹⁆ with hd
    have hdV : d ∈ V₀ := hKL (Subgroup.commutator_mem_commutator (inv_mem hw) (inv_mem hl))
    have hw' : l⁻¹ * w * l = w * d := by
      rw [hd, commutatorElement_def]
      group
    have e1 : ⁅l * u⁻¹ * l⁻¹, w⁆ = l * ⁅u⁻¹, l⁻¹ * w * l⁆ * l⁻¹ := by
      simp only [commutatorElement_def]
      group
    have e2 : ⁅l * u⁻¹ * l⁻¹, w⁆ = ⁅u⁻¹, l⁻¹ * w * l⁆ := by
      rw [e1, hLc _ (hV₀K (inv_mem hu)) _ hwl l hl, mul_inv_cancel_right]
    have e3 : ⁅u⁻¹, l⁻¹ * w * l⁆ = ⁅u⁻¹, w⁆ * ⁅u⁻¹, d⁆ := by
      rw [hw']
      exact commutatorElement_mul_right_of_comm (hcen _ (hV₀K (inv_mem hu)) _ (hV₀K hdV) _ hw)
    have e4 : ⁅u⁻¹, w⁆ = ⁅u, w⁆⁻¹ :=
      commutatorElement_inv_left_of_comm (hcen _ (hV₀K hu) _ hw _ (hV₀K hu))
    have e5 : ⁅⁅u, l⁆, w⁆ = ⁅l * u⁻¹ * l⁻¹, w⁆ * ⁅u, w⁆ := by
      rw [hcomm]
      exact commutatorElement_mul_left_of_comm (hcen _ (hV₀K hu') _ hw _ (hV₀K hu))
    have hc2 : ⁅u⁻¹, d⁆ * ⁅u, w⁆ = ⁅u, w⁆ * ⁅u⁻¹, d⁆ :=
      hcen _ (hV₀K hu) _ hw _ (commutatorElement_mem (hV₀K (inv_mem hu)) (hV₀K hdV))
    rw [e5, e2, e3, e4, mul_assoc, hc2, inv_mul_cancel_left]
    exact Subgroup.commutator_mem_commutator (inv_mem hu) hdV
  exact (hgen (hV₀L hv)).2

end CFSG.Quasithin.MS93.S512L

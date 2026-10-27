module

public import Mathlib.GroupTheory.Commutator.Basic
import CFSG.LocalAnalysis.GL83PartI.I_22_5.Basic

public section

namespace CFSG.StandardType

theorem ggB2der_eq_of_perfect {H : Type*} [Group H] (hperf : commutator H = ⊤) (φ : H →* H)
    (h : ∀ a : H, φ a * a⁻¹ ∈ Subgroup.center H) (a : H) : φ a = a := by
  refine GL83.CompFam.endo_eq_id_of_central hperf φ (fun x => ?_) a
  have hz : (φ x * x⁻¹)⁻¹ ∈ Subgroup.center H := Subgroup.inv_mem _ (h x)
  have e : (φ x * x⁻¹)⁻¹ = x * (φ x)⁻¹ := by group
  rw [e] at hz
  have key : (φ x)⁻¹ * x = x * (φ x)⁻¹ := by
    calc (φ x)⁻¹ * x = ((φ x)⁻¹ * (x * (φ x)⁻¹)) * φ x := by group
      _ = ((x * (φ x)⁻¹) * (φ x)⁻¹) * φ x := by rw [Subgroup.mem_center_iff.mp hz (φ x)⁻¹]
      _ = x * (φ x)⁻¹ := by group
  rw [key]
  exact hz

end CFSG.StandardType

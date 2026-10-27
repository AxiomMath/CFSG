
module

public import CFSG.Sporadic.Co1.Module.InvGroupBase

public import CFSG.Sporadic.Co1.Module.FormsBase1

public section

namespace CFSG.Sporadic.Co1.Module

open CFSG.Blueprint Matrix

attribute [local instance] vecMulAction

theorem ncard_fixQ_conj
    (x s : NativeSporadic.Co1) :
    {v : Vec24 | co1Act (x * s * x⁻¹) v = v ∧ q₀ v = 1}.ncard =
      {v : Vec24 | co1Act s v = v ∧ q₀ v = 1}.ncard := by
  have h : {v : Vec24 | co1Act (x * s * x⁻¹) v = v ∧ q₀ v = 1} =
      (co1Act x) '' {v | co1Act s v = v ∧ q₀ v = 1} := by
    ext v
    constructor
    · rintro ⟨hv, hq⟩
      have hv' : v ∈ {v : Vec24 | co1Act (x * s * x⁻¹) v = v} := hv
      rw [fixSet_conj] at hv'
      obtain ⟨w, hw, rfl⟩ := hv'
      exact ⟨w, ⟨hw, by rw [← q₀_co1Act x w]; exact hq⟩, rfl⟩
    · rintro ⟨w, ⟨hw, hq⟩, rfl⟩
      have hv : co1Act x w ∈ {v : Vec24 | co1Act (x * s * x⁻¹) v = v} := by
        rw [fixSet_conj]
        exact ⟨w, hw, rfl⟩
      exact ⟨hv, by rw [q₀_co1Act]; exact hq⟩
  rw [h, Set.ncard_image_of_injective _ (co1Act_injective x)]

end CFSG.Sporadic.Co1.Module

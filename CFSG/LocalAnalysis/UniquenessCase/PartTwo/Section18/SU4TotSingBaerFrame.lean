module

public import CFSG.ClassicalGroups.Unitary.Form

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.ClassicalGroups.Unitary

variable {F : Type} [Field F] {σ : F ≃+* F}

theorem exists_orthonormal_baer_frame (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0)
    {e f : Fin 4 → F} (hee : herm σ e e = 0) (hff : herm σ f f = 0) (hef : herm σ e f = 1) :
    ∃ z : Fin 4 → Fin 4 → F, (∀ i j, herm σ (z i) (z j) = if i = j then 1 else 0) ∧
      ∀ α : F, ∃ a b : F, σ a = a ∧ σ b = b ∧ α • z 0 + σ α • z 1 = a • e + b • f := by
  obtain ⟨lam, hlam⟩ := hσ.trace_surj 1 (map_one σ)
  have hfe : herm σ f e = 1 := by rw [herm_conj σ hσ.invol e f, hef, map_one σ]
  set z₀ : Fin 4 → F := e + lam • f with hz₀def
  set z₁ : Fin 4 → F := e + σ lam • f with hz₁def
  have hz0 : herm σ z₀ z₀ = 1 := by
    simp only [hz₀def, herm_add_left, herm_add_right, herm_smul_left, herm_smul_right,
      hee, hff, hef, hfe, mul_zero, mul_one, zero_mul, add_zero, zero_add]
    linear_combination hlam
  have hz1 : herm σ z₁ z₁ = 1 := by
    simp only [hz₁def, herm_add_left, herm_add_right, herm_smul_left, herm_smul_right,
      hee, hff, hef, hfe, hσ.invol, mul_zero, mul_one, zero_mul, add_zero, zero_add]
    linear_combination hlam
  have hz01 : herm σ z₀ z₁ = 0 := by
    simp only [hz₀def, hz₁def, herm_add_left, herm_add_right, herm_smul_left, herm_smul_right,
      hee, hff, hef, hfe, mul_zero, mul_one, zero_mul, add_zero, zero_add]
    linear_combination (σ lam) * h2
  obtain ⟨z₂, hz2, hez2, hfz2⟩ :=
    exists_norm_one_perp_pair (n := 4) hσ (by norm_num) hee hff hef
  obtain ⟨z₃, hz3, hz23, hez3, hfz3⟩ :=
    exists_norm_one_perp_three (n := 4) hσ (by norm_num) hz2 hee hff hef
      (herm_eq_zero_comm σ hσ.invol hez2) (herm_eq_zero_comm σ hσ.invol hfz2)
  have hz02 : herm σ z₀ z₂ = 0 := by simp [hz₀def, hez2, hfz2]
  have hz03 : herm σ z₀ z₃ = 0 := by simp [hz₀def, hez3, hfz3]
  have hz12 : herm σ z₁ z₂ = 0 := by simp [hz₁def, hez2, hfz2]
  have hz13 : herm σ z₁ z₃ = 0 := by simp [hz₁def, hez3, hfz3]
  have hz20 : herm σ z₂ z₀ = 0 := herm_eq_zero_comm σ hσ.invol hz02
  have hz30 : herm σ z₃ z₀ = 0 := herm_eq_zero_comm σ hσ.invol hz03
  have hz21 : herm σ z₂ z₁ = 0 := herm_eq_zero_comm σ hσ.invol hz12
  have hz31 : herm σ z₃ z₁ = 0 := herm_eq_zero_comm σ hσ.invol hz13
  have hz32 : herm σ z₃ z₂ = 0 := herm_eq_zero_comm σ hσ.invol hz23
  have hz10 : herm σ z₁ z₀ = 0 := herm_eq_zero_comm σ hσ.invol hz01
  have h0 : (![z₀, z₁, z₂, z₃] : Fin 4 → Fin 4 → F) 0 = z₀ := rfl
  have h1 : (![z₀, z₁, z₂, z₃] : Fin 4 → Fin 4 → F) 1 = z₁ := rfl
  refine ⟨![z₀, z₁, z₂, z₃], ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hz0, hz1, hz2, hz3, hz01, hz10, hz23, hz02, hz03, hz12, hz13, hz20, hz30, hz21,
        hz31, hz32]
  · intro α
    refine ⟨α + σ α, α * lam + σ (α * lam), hσ.trace_fixed α, hσ.trace_fixed (α * lam), ?_⟩
    rw [h0, h1, hz₀def, hz₁def]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_mul]
    ring

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

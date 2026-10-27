module

public import CFSG.YGroups.Y443.Native.AlignAlg
public import CFSG.YGroups.Y443.Native.AlignA

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated CFSG.Open
  CFSG.Monster.B.Short

@[expose] noncomputable def Omega : Gmat := ⟨wordLin omegaWord, wordLin_mem_Gmat _⟩

theorem coe_Omega : ((Omega : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) = wordLin omegaWord := rfl

theorem omega_comm :
    wordLin omegaWord * wordLin wcWord = tStar * wordLin omegaWord := by
  have h := align_a
  rw [wordLin_append, wordLin_append, wordLin_tWord] at h
  exact h

theorem omega_conj :
    wordLin omegaWord * ((fM y443C : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) * (wordLin omegaWord)⁻¹ =
      tStar := by
  rw [fM_y443C_eq, omega_comm, mul_assoc, mul_inv_cancel, mul_one]

theorem fM_y443C_mem_shortClass :
    ((fM y443C : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) ∈ shortClass :=
  ⟨(wordLin omegaWord)⁻¹, inv_mem (wordLin_mem_Gmat _), by rw [← omega_conj]; group⟩

theorem commute_fMc_iff
    {x : SpaceB ≃ₗ[ℚ] SpaceB} :
    x * ((fM y443C : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) = ((fM y443C : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) * x ↔
      (wordLin omegaWord * x * (wordLin omegaWord)⁻¹) * tStar =
        tStar * (wordLin omegaWord * x * (wordLin omegaWord)⁻¹) := by
  rw [← omega_conj]
  generalize wordLin omegaWord = w
  generalize ((fM y443C : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) = c
  constructor
  · intro h
    calc w * x * w⁻¹ * (w * c * w⁻¹) = w * (x * c) * w⁻¹ := by group
      _ = w * (c * x) * w⁻¹ := by rw [h]
      _ = w * c * w⁻¹ * (w * x * w⁻¹) := by group
  · intro h
    have h2 : w * (x * c) * w⁻¹ = w * (c * x) * w⁻¹ :=
      calc w * (x * c) * w⁻¹ = w * x * w⁻¹ * (w * c * w⁻¹) := by group
        _ = w * c * w⁻¹ * (w * x * w⁻¹) := h
        _ = w * (c * x) * w⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)

theorem conj_fM_commute_tStar
    {h : MonsterY443Derived} (hh : h ∈ y443H) :
    (wordLin omegaWord * ((fM h : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) * (wordLin omegaWord)⁻¹) * tStar =
      tStar * (wordLin omegaWord * ((fM h : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) *
        (wordLin omegaWord)⁻¹) := by
  rw [← commute_fMc_iff]
  have := congrArg (fun m => ((fM m : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB)) (y443C_comm_H hh)
  simpa using this

theorem conj_fM_mem_Gmat
    (h : MonsterY443Derived) :
    wordLin omegaWord * ((fM h : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) * (wordLin omegaWord)⁻¹ ∈ Gmat :=
  mul_mem (mul_mem (wordLin_mem_Gmat _) (fM h).2) (inv_mem (wordLin_mem_Gmat _))

end CFSG.YGroups.Y443

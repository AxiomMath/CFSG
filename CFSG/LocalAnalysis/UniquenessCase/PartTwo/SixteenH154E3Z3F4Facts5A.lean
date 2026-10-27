module

public import CFSG.LinearAlgebra.FixedPointFreeOrderThreeField
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LinearAlgebra

theorem s16h_e3_z3f5_card_omegaField : Nat.card OmegaField = 4 := by
  have : Module.Finite (ZMod 2) OmegaField := (AdjoinRoot.powerBasis' omegaPoly_monic).finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_omegaField, Nat.card_zmod]
  norm_num

theorem s16h_e3_z3f5_omegaField_add_self (x : OmegaField) : x + x = 0 := by
  rw [← two_mul, omegaField_two_eq_zero, zero_mul]

theorem s16h_e3_z3f5_omega_cube : omega ^ 3 = 1 := by
  rw [pow_succ, omega_sq, add_mul, one_mul, ← sq, omega_sq, add_assoc, add_comm 1 omega,
    ← add_assoc, s16h_e3_z3f5_omegaField_add_self, zero_add]

theorem s16h_e3_z3f5_cube_eq_zero_or_one (y : OmegaField) : y ^ 3 = 0 ∨ y ^ 3 = 1 := by
  obtain ⟨a, b, rfl⟩ := omegaField_eq y
  have h2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases h2 a with rfl | rfl <;> rcases h2 b with rfl | rfl <;>
    simp only [map_zero, map_one, zero_add, zero_mul, one_mul, add_zero]
  · left; simp
  · right; exact s16h_e3_z3f5_omega_cube
  · right; simp
  · right
    rw [add_comm, ← omega_sq, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul,
      s16h_e3_z3f5_omega_cube, one_pow]

private theorem s16h_e3_z3f5_zmod_two_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem s16h_e3_z3f5_root_cases (y : OmegaField) (hy : y ^ 2 + y + 1 = 0) :
    y = omega ∨ y = omega ^ 2 := by
  obtain ⟨A, B, hAB⟩ := omegaField_eq y
  rw [hAB] at hy
  rcases s16h_e3_z3f5_zmod_two_cases A with rfl | rfl <;>
    rcases s16h_e3_z3f5_zmod_two_cases B with rfl | rfl
  · exfalso; simpa using hy
  · left; simpa using hAB
  · exfalso; simpa [s16h_e3_z3f5_omegaField_add_self] using hy
  · right
    rw [hAB]
    simp only [map_one, one_mul]
    rw [omega_sq, add_comm]

theorem s16h_e3_z3f5_ringEquiv_eq_sq (σ : OmegaField ≃+* OmegaField) (hσ : σ ≠ 1) :
    ∀ x, σ x = x ^ 2 := by
  have hfix : ∀ c : ZMod 2,
      σ (algebraMap (ZMod 2) OmegaField c) = algebraMap (ZMod 2) OmegaField c := by
    intro c
    rcases s16h_e3_z3f5_zmod_two_cases c with rfl | rfl <;> simp
  have hbase : omega ^ 2 + omega + 1 = 0 := by
    rw [omega_sq, add_assoc, s16h_e3_z3f5_omegaField_add_self]
  have hroot : σ omega ^ 2 + σ omega + 1 = 0 := by
    have := congrArg σ hbase
    simpa [map_add, map_pow] using this
  have hω : σ omega ≠ omega := by
    intro h
    apply hσ
    ext x
    obtain ⟨a, b, hab⟩ := omegaField_eq x
    calc σ x = σ (algebraMap (ZMod 2) OmegaField a + algebraMap (ZMod 2) OmegaField b * omega) :=
          by rw [hab]
      _ = algebraMap (ZMod 2) OmegaField a + algebraMap (ZMod 2) OmegaField b * σ omega :=
          by simp only [map_add, map_mul, hfix]
      _ = algebraMap (ZMod 2) OmegaField a + algebraMap (ZMod 2) OmegaField b * omega :=
          by rw [h]
      _ = x := hab.symm
  have hsq : σ omega = omega ^ 2 :=
    (s16h_e3_z3f5_root_cases (σ omega) hroot).resolve_left hω
  intro x
  obtain ⟨a, b, hab⟩ := omegaField_eq x
  calc σ x = σ (algebraMap (ZMod 2) OmegaField a + algebraMap (ZMod 2) OmegaField b * omega) :=
        by rw [hab]
    _ = algebraMap (ZMod 2) OmegaField a + algebraMap (ZMod 2) OmegaField b * σ omega :=
        by simp only [map_add, map_mul, hfix]
    _ = algebraMap (ZMod 2) OmegaField a + algebraMap (ZMod 2) OmegaField b * omega ^ 2 :=
        by rw [hsq]
    _ = (algebraMap (ZMod 2) OmegaField a + algebraMap (ZMod 2) OmegaField b * omega) ^ 2 :=
        (omegaField_sq a b).symm
    _ = x ^ 2 := by rw [hab]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

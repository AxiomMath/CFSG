module

public import CFSG.RankThree.PartTwo.KFacts.KP14McLaughlin

public section

namespace CFSG.RankThree.PartTwo.KFacts.KP14

open Matrix

theorem isTransvectionGL_conj {n : ℕ} {t : GL (Fin n) (ZMod 3)} (ht : IsTransvectionGL t)
    (g : GL (Fin n) (ZMod 3)) : IsTransvectionGL (g * t * g⁻¹) := by
  obtain ⟨h1, h2, h3⟩ := ht
  have hsub : ((g * t * g⁻¹ : GL (Fin n) (ZMod 3)) : Matrix (Fin n) (Fin n) (ZMod 3)) - 1 =
      (g : Matrix (Fin n) (Fin n) (ZMod 3)) * ((t : Matrix (Fin n) (Fin n) (ZMod 3)) - 1) *
        ((g⁻¹ : GL (Fin n) (ZMod 3)) : Matrix (Fin n) (Fin n) (ZMod 3)) := by
    have hgg : (g : Matrix (Fin n) (Fin n) (ZMod 3)) *
        ((g⁻¹ : GL (Fin n) (ZMod 3)) : Matrix (Fin n) (Fin n) (ZMod 3)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    simp only [Units.val_mul, mul_sub, sub_mul, mul_one, hgg]
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply h1
    have := congrArg (fun x => g⁻¹ * x * g) h
    simpa [mul_assoc] using this
  · rw [hsub]
    have hgg : ((g⁻¹ : GL (Fin n) (ZMod 3)) : Matrix (Fin n) (Fin n) (ZMod 3)) *
        (g : Matrix (Fin n) (Fin n) (ZMod 3)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc ((g : Matrix (Fin n) (Fin n) (ZMod 3)) * ((t : Matrix (Fin n) (Fin n) (ZMod 3)) - 1) *
          ((g⁻¹ : GL (Fin n) (ZMod 3)) : Matrix (Fin n) (Fin n) (ZMod 3))) *
        ((g : Matrix (Fin n) (Fin n) (ZMod 3)) * ((t : Matrix (Fin n) (Fin n) (ZMod 3)) - 1) *
          ((g⁻¹ : GL (Fin n) (ZMod 3)) : Matrix (Fin n) (Fin n) (ZMod 3)))
        = (g : Matrix (Fin n) (Fin n) (ZMod 3)) *
          (((t : Matrix (Fin n) (Fin n) (ZMod 3)) - 1) *
            (((g⁻¹ : GL (Fin n) (ZMod 3)) : Matrix (Fin n) (Fin n) (ZMod 3)) *
              (g : Matrix (Fin n) (Fin n) (ZMod 3))) *
            ((t : Matrix (Fin n) (Fin n) (ZMod 3)) - 1)) *
          ((g⁻¹ : GL (Fin n) (ZMod 3)) : Matrix (Fin n) (Fin n) (ZMod 3)) := by
          simp only [mul_assoc]
      _ = 0 := by rw [hgg, mul_one, h2]; simp
  · rw [hsub]
    have hdet : IsUnit (g : Matrix (Fin n) (Fin n) (ZMod 3)).det :=
      (Matrix.isUnits_det_units g)
    have hdet' : IsUnit ((g⁻¹ : GL (Fin n) (ZMod 3)) : Matrix (Fin n) (Fin n) (ZMod 3)).det :=
      (Matrix.isUnits_det_units g⁻¹)
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdet', Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdet]
    exact h3

theorem pow_three_eq_one_of_isTransvectionGL {n : ℕ} {t : GL (Fin n) (ZMod 3)}
    (ht : IsTransvectionGL t) : t ^ 3 = 1 := by
  obtain ⟨-, h2, -⟩ := ht
  apply Units.ext
  set N : Matrix (Fin n) (Fin n) (ZMod 3) := (t : Matrix (Fin n) (Fin n) (ZMod 3)) - 1 with hN
  have htN : (t : Matrix (Fin n) (Fin n) (ZMod 3)) = 1 + N := by rw [hN]; abel
  have h3 : (3 : ℕ) • N = 0 := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.zero_apply, nsmul_eq_mul]
    have : ((3 : ℕ) : ZMod 3) = 0 := by decide
    rw [this, zero_mul]
  have h2' : N * N = 0 := h2
  rw [Units.val_pow_eq_pow_val, htN]
  have : (1 + N) ^ 3 = 1 + (3 : ℕ) • N + (3 : ℕ) • (N * N) + N * N * N := by
    simp only [pow_succ, pow_zero, one_mul, add_mul, mul_add, mul_one, one_mul, succ_nsmul,
      zero_smul, zero_add]
    abel
  rw [this, h3, h2']
  simp

theorem isPGroup_zpowers_of_pow_three {G : Type*} [Group G] {x : G} (hx : x ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers x) := by
  rw [IsPGroup.iff_orderOf]
  rintro ⟨g, hg⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have h1 : (⟨x ^ k, hg⟩ : Subgroup.zpowers x) ^ 3 = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, Subgroup.coe_one, ← zpow_natCast, ← _root_.zpow_mul, mul_comm,
      _root_.zpow_mul, zpow_natCast, hx, _root_.one_zpow]
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (orderOf_dvd_of_pow_eq_one (by rw [show (3 : ℕ) = 3 ^ 1 by norm_num] at h1; exact h1))
  exact ⟨i, hi⟩

theorem sylowTransvectionGL43_holds : SylowTransvectionGL43 := by
  intro W _ ⟨t, htW, ht⟩ P
  have h3 : t ^ 3 = 1 := pow_three_eq_one_of_isTransvectionGL ht
  set t' : W := ⟨t, htW⟩ with ht'
  have ht'3 : t' ^ 3 = 1 := Subtype.ext (by simpa [ht'] using h3)
  have hp : IsPGroup 3 (Subgroup.zpowers t') := isPGroup_zpowers_of_pow_three ht'3
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq W Q P
  refine ⟨g * t' * g⁻¹, ?_, ?_⟩
  · rw [← hg]
    have hmem : t' ∈ (Q : Subgroup W) := hQ (Subgroup.mem_zpowers t')
    exact ⟨t', hmem, rfl⟩
  · have : ((g * t' * g⁻¹ : W) : GL (Fin 4) (ZMod 3)) = (g : GL (Fin 4) (ZMod 3)) * t * (g : GL (Fin 4) (ZMod 3))⁻¹ := by
      simp [ht']
    rw [this]
    exact isTransvectionGL_conj ht _

end CFSG.RankThree.PartTwo.KFacts.KP14

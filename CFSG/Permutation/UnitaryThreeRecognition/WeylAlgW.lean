module

public import CFSG.Permutation.UnitaryThreeRecognition.WeylAlgZ

public section

namespace CFSG.UnitaryThreeRecognition.WeylAlg

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model

variable {K : Type*} [Field K] {J : HermitianForm 3 K}
variable {q : ℕ} {F : Coord J → Coord J} {σ : Kˣ →* Kˣ} {h : Coord J → Kˣ}

namespace SMapHyp

variable (H : SMapHyp J q F σ h)
include H

theorem exists_cube_root {ζ : K} (hζ0 : ζ ≠ 0) (hζ : ζ ^ (q + 1) = 1) :
    ∃ k : Kˣ, (k : K) ^ (q + 1) = 1 ∧ (k : K) ^ 3 = ζ := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime H.coprime
    (by have := H.q_ge; omega)
  refine ⟨Units.mk0 ζ hζ0 ^ m, ?_, ?_⟩
  · rw [Units.val_pow_eq_pow_val, Units.val_mk0, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  · rw [Units.val_pow_eq_pow_val, Units.val_mk0, ← pow_mul, mul_comm,
      ← Nat.mod_add_div (3 * m) (q + 1), hm, pow_add, pow_one, pow_mul, hζ, one_pow, mul_one]

theorem conj_eq_inv_of_pow {k : K} (hk : k ^ (q + 1) = 1) : J.conj k = k⁻¹ := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hk
    exact zero_ne_one hk
  rw [H.conj_pow]
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ, hk]

theorem torus_nrm_one {k : Kˣ} (hk : (k : K) ^ (q + 1) = 1) (z : Coord J) :
    hermitianTorusAction J k z = ⟨(z.1.1 * (k : K) ^ 3, z.1.2), by
      have hc := H.conj_eq_inv_of_pow hk
      have hk0 : (k : K) ≠ 0 := k.ne_zero
      rw [map_mul, map_pow, hc, inv_pow]
      have := coord_rel z
      field_simp
      linear_combination this⟩ := by
  have hc := H.conj_eq_inv_of_pow hk
  have hk0 : (k : K) ≠ 0 := k.ne_zero
  apply coord_ext
  · rw [torus_fst, hc, inv_inv]; ring
  · rw [torus_snd, hc, inv_inv]; field_simp

theorem sigma_eq_self {k : Kˣ} (hk : (k : K) ^ (q + 1) = 1) : σ k = k := (H.σfix k).mpr hk

theorem F_level {z w : Coord J} (hz : z.1.1 ≠ 0) (hzw : z.1.2 = w.1.2) :
    (F z).1.1 * w.1.1 = (F w).1.1 * z.1.1 ∧ (F z).1.2 = (F w).1.2 := by
  have hz1 : z ≠ 1 := fun e => hz (by rw [e]; rfl)
  set ζ := w.1.1 / z.1.1 with hζdef
  have hnz : z.1.1 * J.conj z.1.1 = w.1.1 * J.conj w.1.1 := by
    have h1 := coord_rel z
    have h2 := coord_rel w
    rw [hzw] at h1
    linear_combination h1 - h2
  have hw : w.1.1 ≠ 0 := by
    intro e
    rw [e, zero_mul] at hnz
    exact hz ((mul_eq_zero.mp hnz).resolve_right ((map_ne_zero J.conj).2 hz))
  have hζ0 : ζ ≠ 0 := div_ne_zero hw hz
  have hζn : ζ ^ (q + 1) = 1 := by
    have : ζ * J.conj ζ = 1 := by
      rw [hζdef, map_div₀, div_mul_div_comm, ← hnz]
      exact div_self (mul_ne_zero hz ((map_ne_zero J.conj).2 hz))
    rw [← nrm_eq_pow J H.conj_pow, nrm_def]
    exact this
  obtain ⟨k, hk, hk3⟩ := H.exists_cube_root hζ0 hζn
  have hkz : hermitianTorusAction J k z = w := by
    rw [H.torus_nrm_one hk z]
    apply coord_ext
    · change z.1.1 * (k : K) ^ 3 = w.1.1
      rw [hk3, hζdef]; field_simp
    · exact hzw
  have hF := H.F_torus k z hz1
  rw [hkz, H.sigma_eq_self hk, H.torus_nrm_one hk] at hF
  rw [hF]
  constructor
  · change (F z).1.1 * w.1.1 = (F z).1.1 * (k : K) ^ 3 * z.1.1
    rw [hk3, hζdef]; field_simp
  · rfl

end SMapHyp

end CFSG.UnitaryThreeRecognition.WeylAlg

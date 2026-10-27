module

public import Certificates.Certificate1089007

public section

namespace CFSG.Sporadic.J2.Sylow5

open CFSG.Sporadic.Bridge.J2
open CFSG.Sporadic.J2.Sylow5Data

theorem wordProd_a_val :
    ((Bridge.wordProd natU wP5a : GL (Fin 14) (ZMod 5)) : Matrix (Fin 14) (Fin 14) (ZMod 5)) =
      toM mP5a := by
  have h := val_natWord (Z := ZP5a) rfl
  rw [ZP5a_eq] at h
  exact h

theorem wordProd_b_val :
    ((Bridge.wordProd natU wP5b : GL (Fin 14) (ZMod 5)) : Matrix (Fin 14) (Fin 14) (ZMod 5)) =
      toM mP5b := by
  have h := val_natWord (Z := ZP5b) rfl
  rw [ZP5b_eq] at h
  exact h

theorem wordProd_g_val :
    ((Bridge.wordProd natU wg : GL (Fin 14) (ZMod 5)) : Matrix (Fin 14) (Fin 14) (ZMod 5)) =
      toM mZg := by
  have h := val_natWord (Z := Zg) rfl
  rw [show Zg = mZg from lwordL_wg] at h
  exact h

theorem wordProd_a5 : (Bridge.wordProd natU wP5a : GL (Fin 14) (ZMod 5)) ^ 5 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, wordProd_a_val]
  exact Certificates.certificate1089007.1

theorem wordProd_b5 : (Bridge.wordProd natU wP5b : GL (Fin 14) (ZMod 5)) ^ 5 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, wordProd_b_val]
  exact Certificates.certificate1089007.2.1

theorem wordProd_ab :
    (Bridge.wordProd natU wP5a : GL (Fin 14) (ZMod 5)) * Bridge.wordProd natU wP5b =
      (Bridge.wordProd natU wP5b : GL (Fin 14) (ZMod 5)) * Bridge.wordProd natU wP5a := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, wordProd_a_val, wordProd_b_val]
  exact Certificates.certificate1089007.2.2.1

theorem wordProd_g3 : (Bridge.wordProd natU wg : GL (Fin 14) (ZMod 5)) ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, wordProd_g_val]
  exact Certificates.certificate1089007.2.2.2.1

theorem wordProd_g_a :
    (Bridge.wordProd natU wg : GL (Fin 14) (ZMod 5)) * Bridge.wordProd natU wP5a =
      (Bridge.wordProd natU wP5a : GL (Fin 14) (ZMod 5)) ^ 4 *
        (Bridge.wordProd natU wP5b : GL (Fin 14) (ZMod 5)) ^ 2 * Bridge.wordProd natU wg := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val, wordProd_a_val, wordProd_b_val, wordProd_g_val]
  exact Certificates.certificate1089007.2.2.2.2.1

theorem wordProd_g_b :
    (Bridge.wordProd natU wg : GL (Fin 14) (ZMod 5)) * Bridge.wordProd natU wP5b =
      (Bridge.wordProd natU wP5a : GL (Fin 14) (ZMod 5)) ^ 2 * Bridge.wordProd natU wg := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, wordProd_a_val,
    wordProd_b_val, wordProd_g_val]
  exact Certificates.certificate1089007.2.2.2.2.2.1

theorem wordProd_a_ne_one : (Bridge.wordProd natU wP5a : GL (Fin 14) (ZMod 5)) ≠ 1 := by
  intro h
  apply Certificates.certificate1089007.2.2.2.2.2.2.1
  rw [← wordProd_a_val]
  simpa using congrArg (fun u : GL (Fin 14) (ZMod 5) =>
    (u : Matrix (Fin 14) (Fin 14) (ZMod 5))) h

theorem wordProd_b_ne_pow (j : ℕ) (hj : j < 5) :
    (Bridge.wordProd natU wP5b : GL (Fin 14) (ZMod 5)) ≠
      (Bridge.wordProd natU wP5a : GL (Fin 14) (ZMod 5)) ^ j := by
  intro h
  have hb : toM mP5b = (toM mP5a) ^ j := by
    rw [← wordProd_b_val, h, Units.val_pow_eq_pow_val, ← wordProd_a_val]
  interval_cases j
  · exact Certificates.certificate1089007.2.2.2.2.2.2.2.1 (by simpa using hb)
  · exact Certificates.certificate1089007.2.2.2.2.2.2.2.2.1 (by simpa using hb)
  · exact Certificates.certificate1089007.2.2.2.2.2.2.2.2.2.1 (by simpa using hb)
  · exact Certificates.certificate1089007.2.2.2.2.2.2.2.2.2.2.1 (by simpa using hb)
  · exact Certificates.certificate1089007.2.2.2.2.2.2.2.2.2.2.2 (by simpa using hb)

noncomputable def a0 : seedGroup := ⟨Bridge.wordProd natU wP5a, natWord_mem wP5a⟩
noncomputable def b0 : seedGroup := ⟨Bridge.wordProd natU wP5b, natWord_mem wP5b⟩
noncomputable def g0 : seedGroup := ⟨Bridge.wordProd natU wg, natWord_mem wg⟩

theorem val_a0 : ((a0 : seedGroup) : GL (Fin 14) (ZMod 5)) = Bridge.wordProd natU wP5a := Subgroup.coe_mk (H := seedGroup) (x := Bridge.wordProd natU wP5a) (hx := natWord_mem wP5a)

theorem val_b0 : ((b0 : seedGroup) : GL (Fin 14) (ZMod 5)) = Bridge.wordProd natU wP5b := Subgroup.coe_mk (H := seedGroup) (x := Bridge.wordProd natU wP5b) (hx := natWord_mem wP5b)

theorem a0_5 : a0 ^ 5 = 1 := by
  apply Subtype.ext
  simpa [a0] using wordProd_a5

theorem b0_5 : b0 ^ 5 = 1 := by
  apply Subtype.ext
  simpa [b0] using wordProd_b5

theorem a0b0_comm : a0 * b0 = b0 * a0 := by
  apply Subtype.ext
  simpa [a0, b0] using wordProd_ab

theorem g0_3 : g0 ^ 3 = 1 := by
  apply Subtype.ext
  simpa [g0] using wordProd_g3

theorem hga0 : g0 * a0 * g0⁻¹ = a0 ^ 4 * b0 ^ 2 := by
  have h : g0 * a0 = a0 ^ 4 * b0 ^ 2 * g0 := by
    apply Subtype.ext
    simpa [a0, b0, g0] using wordProd_g_a
  calc g0 * a0 * g0⁻¹ = (a0 ^ 4 * b0 ^ 2 * g0) * g0⁻¹ := by rw [h]
    _ = a0 ^ 4 * b0 ^ 2 := by group

theorem hgb0 : g0 * b0 * g0⁻¹ = a0 ^ 2 := by
  have h : g0 * b0 = a0 ^ 2 * g0 := by
    apply Subtype.ext
    simpa [a0, b0, g0] using wordProd_g_b
  calc g0 * b0 * g0⁻¹ = (a0 ^ 2 * g0) * g0⁻¹ := by rw [h]
    _ = a0 ^ 2 := by group

theorem a0_ne_one : a0 ≠ 1 := by
  intro h
  apply wordProd_a_ne_one
  have := congrArg Subtype.val h
  simpa [val_a0] using this

theorem b0_not_pow (i : ℕ) : b0 ≠ a0 ^ i := by
  have h5 : a0 ^ 5 = 1 := a0_5
  have hmod : a0 ^ i = a0 ^ (i % 5) := by
    conv_lhs => rw [← Nat.div_add_mod i 5]
    rw [pow_add, pow_mul, h5, one_pow, one_mul]
  rw [hmod]
  have hj : i % 5 < 5 := Nat.mod_lt _ (by norm_num)
  intro h
  have hb : Bridge.wordProd natU wP5b = (Bridge.wordProd natU wP5a) ^ (i % 5) := by
    have h' := congrArg Subtype.val h
    rw [val_b0, Subgroup.coe_pow, val_a0] at h'
    exact h'
  exact wordProd_b_ne_pow (i % 5) hj hb

end CFSG.Sporadic.J2.Sylow5

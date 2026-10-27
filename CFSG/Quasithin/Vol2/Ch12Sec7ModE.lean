module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModB
public import CFSG.Quasithin.Vol2.Ch12Sec7ModData2
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData2
public import Mathlib.Data.LawfulXor.Basic
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Fischer

namespace B6

theorem bitV_xor (v w i x : ℕ) : bitV (v ^^^ w) i x = bitV v i x ^^^ bitV w i x := by
  simp only [bitV, Nat.testBit_xor]
  cases v.testBit i <;> cases w.testBit i <;> simp

theorem bitV_zero_right (v i : ℕ) : bitV v i 0 = 0 := by
  simp [bitV]

theorem app_zero (B : B6) : B.app 0 = 0 := by
  simp [app, bitV]

theorem app_xor (B : B6) (v w : ℕ) : B.app (v ^^^ w) = B.app v ^^^ B.app w := by
  simp only [app, bitV_xor]
  ac_rfl

theorem app_bitV (B : B6) (v i x : ℕ) : B.app (bitV v i x) = bitV v i (B.app x) := by
  simp only [bitV]
  split_ifs
  · rfl
  · exact app_zero B

theorem app_comp (B C : B6) (v : ℕ) : (B.comp C).app v = B.app (C.app v) := by
  have e : C.app v = bitV v 0 C.c0 ^^^ bitV v 1 C.c1 ^^^ bitV v 2 C.c2 ^^^ bitV v 3 C.c3 ^^^
      bitV v 4 C.c4 ^^^ bitV v 5 C.c5 := rfl
  rw [e, app_xor, app_xor, app_xor, app_xor, app_xor, app_bitV, app_bitV, app_bitV, app_bitV,
    app_bitV, app_bitV]
  rfl

theorem comp_assoc (B C D : B6) : (B.comp C).comp D = B.comp (C.comp D) := by
  show B6.mk ((B.comp C).app D.c0) ((B.comp C).app D.c1) ((B.comp C).app D.c2)
      ((B.comp C).app D.c3) ((B.comp C).app D.c4) ((B.comp C).app D.c5) =
    B6.mk (B.app (C.app D.c0)) (B.app (C.app D.c1)) (B.app (C.app D.c2)) (B.app (C.app D.c3))
      (B.app (C.app D.c4)) (B.app (C.app D.c5))
  simp only [app_comp]

theorem bitV_lt {v i x : ℕ} (hx : x < 64) : bitV v i x < 64 := by
  unfold bitV
  split_ifs
  · exact hx
  · norm_num

theorem app_lt {B : B6} (hB : B.Valid) (v : ℕ) : B.app v < 64 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hB
  have l := fun (a b : ℕ) (ha : a < 2 ^ 6) (hb : b < 2 ^ 6) =>
    (Nat.xor_lt_two_pow ha hb : a ^^^ b < 2 ^ 6)
  simp only [app]
  exact l _ _ (l _ _ (l _ _ (l _ _ (l _ _ (bitV_lt h0) (bitV_lt h1)) (bitV_lt h2))
    (bitV_lt h3)) (bitV_lt h4)) (bitV_lt h5)

theorem comp_valid {B : B6} (hB : B.Valid) (C : B6) : (B.comp C).Valid :=
  ⟨app_lt hB _, app_lt hB _, app_lt hB _, app_lt hB _, app_lt hB _, app_lt hB _⟩

theorem id_valid : id.Valid := by decide

theorem id_app : ∀ v < 64, id.app v = v := by decide

theorem pow_valid {B : B6} (hB : B.Valid) : ∀ n, (B.pow n).Valid
  | 0 => id_valid
  | _ + 1 => comp_valid hB _

theorem pow_app (B : B6) : ∀ n v, v < 64 → (B.pow n).app v = (B.app)^[n] v
  | 0, v, hv => id_app v hv
  | n + 1, v, hv => by
    rw [pow, app_comp, pow_app B n v hv, Function.iterate_succ_apply']

theorem app_c0 (B : B6) : B.app 1 = B.c0 := by simp (config := {decide := true}) [app, bitV]

theorem app_c1 (B : B6) : B.app 2 = B.c1 := by simp (config := {decide := true}) [app, bitV]

theorem app_c2 (B : B6) : B.app 4 = B.c2 := by simp (config := {decide := true}) [app, bitV]

theorem app_c3 (B : B6) : B.app 8 = B.c3 := by simp (config := {decide := true}) [app, bitV]

theorem app_c4 (B : B6) : B.app 16 = B.c4 := by simp (config := {decide := true}) [app, bitV]

theorem app_c5 (B : B6) : B.app 32 = B.c5 := by simp (config := {decide := true}) [app, bitV]

theorem ext_app {B C : B6} (h : ∀ v < 64, B.app v = C.app v) : B = C := by
  have e0 := h 1 (by norm_num)
  have e1 := h 2 (by norm_num)
  have e2 := h 4 (by norm_num)
  have e3 := h 8 (by norm_num)
  have e4 := h 16 (by norm_num)
  have e5 := h 32 (by norm_num)
  rw [app_c0, app_c0] at e0
  rw [app_c1, app_c1] at e1
  rw [app_c2, app_c2] at e2
  rw [app_c3, app_c3] at e3
  rw [app_c4, app_c4] at e4
  rw [app_c5, app_c5] at e5
  cases B
  cases C
  simp_all

theorem comp_id {B : B6} : B.comp id = B := by
  cases B
  simp [comp, app_c0, app_c1, app_c2, app_c3, app_c4, app_c5, id]

theorem id_comp {B : B6} (hB : B.Valid) : id.comp B = B := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hB
  cases B
  simp only [comp, mk.injEq]
  exact ⟨id_app _ h0, id_app _ h1, id_app _ h2, id_app _ h3, id_app _ h4, id_app _ h5⟩

end B6

theorem sV_eq_bits : ∀ v < 64, ∀ x : ℕ,
    sV (v &&& 3) x = bitV v 0 x ^^^ bitV v 1 (wV x) ∧
    sV ((v >>> 2) &&& 3) x = bitV v 2 x ^^^ bitV v 3 (wV x) ∧
    sV ((v >>> 4) &&& 3) x = bitV v 4 x ^^^ bitV v 5 (wV x) := by
  intro v hv x
  have key : ∀ v < 64, ((v &&& 3) % 2 = 1 ↔ v.testBit 0 = true) ∧
      (((v &&& 3) >>> 1) % 2 = 1 ↔ v.testBit 1 = true) ∧
      (((v >>> 2) &&& 3) % 2 = 1 ↔ v.testBit 2 = true) ∧
      ((((v >>> 2) &&& 3) >>> 1) % 2 = 1 ↔ v.testBit 3 = true) ∧
      (((v >>> 4) &&& 3) % 2 = 1 ↔ v.testBit 4 = true) ∧
      ((((v >>> 4) &&& 3) >>> 1) % 2 = 1 ↔ v.testBit 5 = true) := by decide
  obtain ⟨k0, k1, k2, k3, k4, k5⟩ := key v hv
  simp only [sV, bitV]
  refine ⟨?_, ?_, ?_⟩
  · simp only [k0, k1]
  · simp only [k2, k3]
  · simp only [k4, k5]

theorem toB6_app (A : Mc) {v : ℕ} (hv : v < 64) : A.toB6.app v = A.app v := by
  simp only [Mc.app, (sV_eq_bits v hv A.c0).1, (sV_eq_bits v hv A.c1).2.1,
    (sV_eq_bits v hv A.c2).2.2, B6.app, Mc.toB6]
  ac_rfl

theorem toB6_valid {A : Mc} (hA : A.Valid) : A.toB6.Valid := by
  obtain ⟨h0, h1, h2⟩ := hA
  have hw : ∀ x < 64, wV x < 64 := by decide
  exact ⟨h0, hw _ h0, h1, hw _ h1, h2, hw _ h2⟩

theorem wV_eq_sV (v : ℕ) : wV v = sV 2 v := by
  simp [sV]

theorem Mc.app_wV {A : Mc} (hA : A.Valid) {v : ℕ} (hv : v < 64) :
    A.app (wV v) = wV (A.app v) := by
  have hw : ∀ x < 64, wV x < 64 := by decide
  apply decV_injective (Mc.app_lt A hA) (hw _ (Mc.app_lt A hA))
  rw [← Mc.toMat_mulVec A hA, wV_eq_sV, wV_eq_sV, decV_sV (by norm_num) hv,
    decV_sV (by norm_num) (Mc.app_lt A hA), Matrix.mulVec_smul, Mc.toMat_mulVec A hA]

theorem toB6_mul {A B : Mc} (hA : A.Valid) (hB : B.Valid) :
    (A.mul B).toB6 = A.toB6.comp B.toB6 := by
  obtain ⟨h0, h1, h2⟩ := hB
  have hw : ∀ x < 64, wV x < 64 := by decide
  have e : A.toB6.comp B.toB6 = ⟨A.toB6.app B.c0, A.toB6.app (wV B.c0), A.toB6.app B.c1,
      A.toB6.app (wV B.c1), A.toB6.app B.c2, A.toB6.app (wV B.c2)⟩ := rfl
  rw [e, toB6_app A h0, toB6_app A (hw _ h0), toB6_app A h1, toB6_app A (hw _ h1),
    toB6_app A h2, toB6_app A (hw _ h2), Mc.app_wV hA h0, Mc.app_wV hA h1, Mc.app_wV hA h2]
  rfl

theorem toB6_one : Mc.one.toB6 = B6.id := by decide

theorem toB6_injective {A B : Mc} (h : A.toB6 = B.toB6) : A = B := by
  cases A
  cases B
  simp only [Mc.toB6, B6.mk.injEq] at h
  obtain ⟨h0, -, h1, -, h2, -⟩ := h
  rw [h0, h1, h2]

end CFSG.Quasithin.H13.S127.Mod

end

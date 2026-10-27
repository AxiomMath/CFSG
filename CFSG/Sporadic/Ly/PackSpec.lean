module

public import Batteries.Data.ByteArray
public import Certificates.Data.CFSGNative.Ly.Pack
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Sporadic.Ly

open Native Finset

@[expose] def dgt (x l : ℕ) : ℕ := x / 256 ^ l % 256

theorem dgt_lt (x l : ℕ) : dgt x l < 256 := Nat.mod_lt _ (by norm_num)

theorem dgt_succ (x l : ℕ) : dgt x (l + 1) = dgt (x / 256) l := by
  unfold dgt
  rw [Nat.div_div_eq_div_mul, pow_succ, mul_comm]

theorem dgt_zero_right (x : ℕ) : dgt x 0 = x % 256 := by simp [dgt]

theorem dgt_add {x y : ℕ} : ∀ l, (∀ l' ≤ l, dgt x l' + dgt y l' < 256) →
    dgt (x + y) l = dgt x l + dgt y l
  | 0, h => by
    have h0 := h 0 le_rfl
    rw [dgt_zero_right, dgt_zero_right, dgt_zero_right] at *
    rw [Nat.add_mod, Nat.mod_eq_of_lt h0]
  | l + 1, h => by
    have h0 := h 0 (Nat.zero_le _)
    rw [dgt_zero_right, dgt_zero_right] at h0
    have hdiv : (x + y) / 256 = x / 256 + y / 256 := by
      rw [Nat.add_div (by norm_num : 0 < 256), ite_eq_right (by omega), add_zero]
    rw [dgt_succ, hdiv, dgt_add l (fun l' hl' => by
      rw [← dgt_succ, ← dgt_succ]; exact h (l' + 1) (by omega)), dgt_succ, dgt_succ]

theorem dgt_mul (c : ℕ) {x : ℕ} : ∀ l, (∀ l' ≤ l, c * dgt x l' < 256) →
    dgt (c * x) l = c * dgt x l
  | 0, h => by
    have h0 := h 0 le_rfl
    rw [dgt_zero_right] at h0
    rw [dgt_zero_right, dgt_zero_right]
    have e : c * x = c * (x % 256) + 256 * (c * (x / 256)) := by
      have := Nat.mod_add_div x 256
      calc c * x = c * (x % 256 + 256 * (x / 256)) := by rw [this]
        _ = c * (x % 256) + 256 * (c * (x / 256)) := by ring
    rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
  | l + 1, h => by
    have h0 := h 0 (Nat.zero_le _)
    rw [dgt_zero_right] at h0
    have hdiv : c * x / 256 = c * (x / 256) := by
      have e : c * x = 256 * (c * (x / 256)) + c * (x % 256) := by
        have := Nat.div_add_mod x 256
        calc c * x = c * (256 * (x / 256) + x % 256) := by rw [this]
          _ = 256 * (c * (x / 256)) + c * (x % 256) := by ring
      rw [e, Nat.add_comm, Nat.add_mul_div_left _ _ (by norm_num : 0 < 256),
        Nat.div_eq_of_lt h0, zero_add]
    rw [dgt_succ, hdiv, dgt_mul c l (fun l' hl' => by
      rw [← dgt_succ]; exact h (l' + 1) (by omega)), dgt_succ]

theorem dgt_mod_two_pow (z : ℕ) {l : ℕ} (hl : l < 8) : dgt (z % 2 ^ 64) l = dgt z l := by
  unfold dgt
  have h : (2 : ℕ) ^ 64 = 256 ^ l * 256 ^ (8 - l) := by
    rw [← pow_add, Nat.add_sub_cancel' hl.le]; norm_num
  rw [h, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  exact dvd_pow_self 256 (by omega)

theorem dgt_horner_zero {a : ℕ} (M : ℕ) (ha : a < 256) : dgt (a + 256 * M) 0 = a := by
  rw [dgt_zero_right]; omega

theorem dgt_horner_succ {a : ℕ} (M l : ℕ) (ha : a < 256) :
    dgt (a + 256 * M) (l + 1) = dgt M l := by
  rw [dgt_succ]
  congr 1
  omega

theorem byteOf_eq (w : UInt64) {l : ℕ} (hl : l < 8) : byteOf w l = dgt w.toNat l := by
  unfold byteOf
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
  have h1 : (UInt64.ofNat (8 * l)).toNat % 64 = 8 * l := by
    rw [UInt64.toNat_ofNat']; omega
  have h2 : (0xFF : UInt64).toNat = 2 ^ 8 - 1 := rfl
  rw [h1, Nat.shiftRight_eq_div_pow, h2, Nat.and_two_pow_sub_one_eq_mod, dgt, pow_mul]
  norm_num

theorem dgt_uadd {x y : UInt64} (h : ∀ l < 8, dgt x.toNat l + dgt y.toNat l < 256) {l : ℕ}
    (hl : l < 8) : dgt (x + y).toNat l = dgt x.toNat l + dgt y.toNat l := by
  rw [UInt64.toNat_add, dgt_mod_two_pow _ hl]
  exact dgt_add l fun l' hl' => h l' (by omega)

theorem dgt_umul {c x : UInt64} (h : ∀ l < 8, c.toNat * dgt x.toNat l < 256) {l : ℕ}
    (hl : l < 8) : dgt (c * x).toNat l = c.toNat * dgt x.toNat l := by
  rw [UInt64.toNat_mul, dgt_mod_two_pow _ hl]
  exact dgt_mul c.toNat l fun l' hl' => h l' (by omega)

theorem dgt_packWord {f : ℕ → ℕ} (hf : ∀ l < 8, f l < 256) {l : ℕ} (hl : l < 8) :
    dgt (packWord f).toNat l = f l := by
  have h0 := hf 0 (by norm_num)
  have h1 := hf 1 (by norm_num)
  have h2 := hf 2 (by norm_num)
  have h3 := hf 3 (by norm_num)
  have h4 := hf 4 (by norm_num)
  have h5 := hf 5 (by norm_num)
  have h6 := hf 6 (by norm_num)
  have h7 := hf 7 (by norm_num)
  unfold packWord
  rw [UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)]
  interval_cases l
  · exact dgt_horner_zero _ h0
  · rw [dgt_horner_succ _ _ h0, dgt_horner_zero _ h1]
  · rw [dgt_horner_succ _ _ h0, dgt_horner_succ _ _ h1, dgt_horner_zero _ h2]
  · rw [dgt_horner_succ _ _ h0, dgt_horner_succ _ _ h1, dgt_horner_succ _ _ h2,
      dgt_horner_zero _ h3]
  · rw [dgt_horner_succ _ _ h0, dgt_horner_succ _ _ h1, dgt_horner_succ _ _ h2,
      dgt_horner_succ _ _ h3, dgt_horner_zero _ h4]
  · rw [dgt_horner_succ _ _ h0, dgt_horner_succ _ _ h1, dgt_horner_succ _ _ h2,
      dgt_horner_succ _ _ h3, dgt_horner_succ _ _ h4, dgt_horner_zero _ h5]
  · rw [dgt_horner_succ _ _ h0, dgt_horner_succ _ _ h1, dgt_horner_succ _ _ h2,
      dgt_horner_succ _ _ h3, dgt_horner_succ _ _ h4, dgt_horner_succ _ _ h5,
      dgt_horner_zero _ h6]
  · rw [dgt_horner_succ _ _ h0, dgt_horner_succ _ _ h1, dgt_horner_succ _ _ h2,
      dgt_horner_succ _ _ h3, dgt_horner_succ _ _ h4, dgt_horner_succ _ _ h5,
      dgt_horner_succ _ _ h6, dgt_zero_right, Nat.mod_eq_of_lt h7]

theorem dgt_redWord (w : UInt64) {l : ℕ} (hl : l < 8) :
    dgt (redWord w).toNat l = dgt w.toNat l % 5 := by
  unfold redWord
  rw [dgt_packWord (fun l' _ => lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)) hl,
    byteOf_eq w hl]

namespace W14

theorem lane_eq (a : W14) (i : ℕ) : a.lane i = dgt (a.word (i / 8)).toNat (i % 8) :=
  byteOf_eq _ (Nat.mod_lt _ (by norm_num))

theorem word_add (a b : W14) {k : ℕ} (hk : k < 14) : (a.add b).word k = a.word k + b.word k := by
  interval_cases k <;> rfl

theorem word_smul (c : UInt64) (a : W14) {k : ℕ} (hk : k < 14) :
    (W14.smul c a).word k = c * a.word k := by
  interval_cases k <;> rfl

theorem word_zero (k : ℕ) : W14.zero.word k = 0 := by
  unfold W14.zero W14.word
  split <;> rfl

theorem word_red (a : W14) {k : ℕ} (hk : k < 14) : a.red.word k = redWord (a.word k) := by
  interval_cases k <;> rfl

theorem word_packW (f : ℕ → ℕ) {k : ℕ} (hk : k < 14) :
    (packW f).word k = packWord (fun l => f (8 * k + l)) := by
  interval_cases k <;> rfl

theorem lane_zero (i : ℕ) : W14.zero.lane i = 0 := by
  rw [lane_eq, word_zero]; simp [dgt]

theorem lane_add {a b : W14} (h : ∀ j < 112, a.lane j + b.lane j < 256) {i : ℕ} (hi : i < 112) :
    (a.add b).lane i = a.lane i + b.lane i := by
  rw [lane_eq, lane_eq, lane_eq, word_add _ _ (by omega)]
  refine dgt_uadd (fun l hl => ?_) (Nat.mod_lt _ (by norm_num))
  have := h (8 * (i / 8) + l) (by omega)
  rwa [lane_eq, lane_eq, show (8 * (i / 8) + l) / 8 = i / 8 by omega,
    show (8 * (i / 8) + l) % 8 = l by omega] at this

theorem lane_smul {c : UInt64} {a : W14} (h : ∀ j < 112, c.toNat * a.lane j < 256) {i : ℕ}
    (hi : i < 112) : (W14.smul c a).lane i = c.toNat * a.lane i := by
  rw [lane_eq, lane_eq, word_smul _ _ (by omega)]
  refine dgt_umul (fun l hl => ?_) (Nat.mod_lt _ (by norm_num))
  have := h (8 * (i / 8) + l) (by omega)
  rwa [lane_eq, show (8 * (i / 8) + l) / 8 = i / 8 by omega,
    show (8 * (i / 8) + l) % 8 = l by omega] at this

theorem lane_red (a : W14) {i : ℕ} (hi : i < 112) : a.red.lane i = a.lane i % 5 := by
  rw [lane_eq, lane_eq, word_red _ (by omega), dgt_redWord _ (Nat.mod_lt _ (by norm_num))]

theorem lane_packW {f : ℕ → ℕ} (hf : ∀ i < 112, f i < 256) {i : ℕ} (hi : i < 112) :
    (packW f).lane i = f i := by
  rw [lane_eq, word_packW _ (by omega),
    dgt_packWord (fun l hl => hf _ (by omega)) (Nat.mod_lt _ (by norm_num))]
  congr 1
  omega

theorem lane_lt (a : W14) (i : ℕ) : a.lane i < 256 := by
  rw [lane_eq]; exact dgt_lt _ _

end W14

theorem byteArray_get!_eq (b : ByteArray) (i : ℕ) : b.get! i = b.data[i]! := by
  cases b; rfl

theorem get!_push (b : ByteArray) (x : UInt8) (i : ℕ) :
    (b.push x).get! i = if i = b.size then x else b.get! i := by
  rw [byteArray_get!_eq, byteArray_get!_eq, ByteArray.data_push]
  have hs : b.size = b.data.size := rfl
  rw [hs]
  by_cases h : i < b.data.size
  · rw [ite_eq_right (by omega), getElem!_pos (b.data.push x) i (by simp; omega),
      getElem!_pos b.data i h, Array.getElem_push_lt h]
  · by_cases h' : i = b.data.size
    · subst h'
      rw [ite_eq_left rfl, getElem!_pos (b.data.push x) _ (by simp), Array.getElem_push_eq]
    · rw [ite_eq_right h', getElem!_neg (b.data.push x) i (by simp; omega),
        getElem!_neg b.data i h]

theorem pushRed_size (b : ByteArray) (w : UInt64) : (pushRed b w).size = b.size + 8 := by
  simp [pushRed, ByteArray.size_push]

theorem pushRed_get_lt (b : ByteArray) (w : UInt64) {j : ℕ} (hj : j < b.size) :
    (pushRed b w).get! j = b.get! j := by
  simp only [pushRed, get!_push, ByteArray.size_push]
  split_ifs <;> first | omega | rfl

theorem pushRed_get_new (b : ByteArray) (w : UInt64) {l : ℕ} (hl : l < 8) :
    (pushRed b w).get! (b.size + l) = UInt8.ofNat (byteOf w l % 5) := by
  simp only [pushRed, get!_push, ByteArray.size_push]
  interval_cases l <;> split_ifs <;> first | omega | rfl

theorem digits_fold (a : W14) : ∀ n ≤ 14,
    (Nat.fold n (fun q _ b => pushRed b (a.word q)) (ByteArray.emptyWithCapacity 112)).size =
      8 * n ∧
    ∀ j < 8 * n,
      ((Nat.fold n (fun q _ b => pushRed b (a.word q))
        (ByteArray.emptyWithCapacity 112)).get! j).toNat = a.lane j % 5 := by
  intro n
  induction n with
  | zero => intro _; simp [ByteArray.size]
  | succ n ih =>
    intro hn
    obtain ⟨hs, hg⟩ := ih (by omega)
    rw [Nat.fold_succ]
    refine ⟨by rw [pushRed_size, hs]; ring, fun j hj => ?_⟩
    by_cases h : j < 8 * n
    · rw [pushRed_get_lt _ _ (by rw [hs]; exact h)]; exact hg j h
    · obtain ⟨l, hl, rfl⟩ : ∃ l, l < 8 ∧ j = 8 * n + l := ⟨j - 8 * n, by omega, by omega⟩
      rw [← hs, pushRed_get_new _ _ hl, hs]
      rw [UInt8.toNat_ofNat_of_lt' (by
        have := Nat.mod_lt (byteOf (a.word n) l) (show 0 < 5 by norm_num)
        unfold UInt8.size; omega)]
      rw [W14.lane_eq, byteOf_eq _ hl, show (8 * n + l) / 8 = n by omega,
        show (8 * n + l) % 8 = l by omega]

theorem W14.digits_size (a : W14) : a.digits.size = 112 := (digits_fold a 14 le_rfl).1

theorem W14.digits_get (a : W14) {j : ℕ} (hj : j < 112) :
    (a.digits.get! j).toNat = a.lane j % 5 := (digits_fold a 14 le_rfl).2 j hj

end CFSG.Sporadic.Ly

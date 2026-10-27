module

public import Certificates.Data.CFSGNative.HN.F5Packed
public import CFSG.Sporadic.Th.TableSpec
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Sporadic.F5

open Native Finset
open scoped Matrix

@[expose] def dgt (x l : ℕ) : ℕ := x / 256 ^ l % 256

theorem dgt_lt (x l : ℕ) : dgt x l < 256 := Nat.mod_lt _ (by norm_num)

theorem dgt_succ (x l : ℕ) : dgt x (l + 1) = dgt (x / 256) l := by
  unfold dgt
  rw [Nat.div_div_eq_div_mul, pow_succ, mul_comm]

theorem dgt_zero_right (x : ℕ) : dgt x 0 = x % 256 := by simp [dgt]

theorem dgt_zero_left (l : ℕ) : dgt 0 l = 0 := by simp [dgt]

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

theorem dgt_mod_two_pow (z : ℕ) {l : ℕ} (hl : l < 8) : dgt (z % 2 ^ 64) l = dgt z l := by
  unfold dgt
  have h : (2 : ℕ) ^ 64 = 256 ^ l * 256 ^ (8 - l) := by
    rw [← pow_add, Nat.add_sub_cancel' hl.le]; norm_num
  rw [h, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  exact dvd_pow_self 256 (by omega)

theorem dgt_horner_zero {a : ℕ} (M : ℕ) (ha : a < 256) : dgt (a + 256 * M) 0 = a := by
  rw [dgt_zero_right]; omega

theorem dgt_horner_succ {a : ℕ} (M l : ℕ) (ha : a < 256) : dgt (a + 256 * M) (l + 1) = dgt M l := by
  rw [dgt_succ]
  congr 1
  omega

theorem lane_toNat (w : UInt64) {l : ℕ} (hl : l < 8) :
    ((w >>> UInt64.ofNat (8 * l)) &&& 0xFF).toNat = dgt w.toNat l := by
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

theorem word_add (a b : W17) {k : ℕ} (hk : k < 17) : (a.add b).word k = a.word k + b.word k := by
  interval_cases k <;> rfl

theorem word_zero (k : ℕ) : W17.zero.word k = 0 := by
  unfold W17.word
  split <;> rfl

theorem word_packW (f : ℕ → ℕ) {k : ℕ} (hk : k < 17) :
    (packW f).word k = packWord (fun l => f (8 * k + l)) := by
  interval_cases k <;> simp [packW, W17.word]

theorem lane_eq (a : W17) (i : ℕ) : a.lane i = dgt (a.word (i / 8)).toNat (i % 8) :=
  lane_toNat _ (Nat.mod_lt _ (by norm_num))

theorem lane_lt (a : W17) (i : ℕ) : a.lane i < 256 := by
  rw [lane_eq]; exact dgt_lt _ _

theorem lane_zero (i : ℕ) : W17.zero.lane i = 0 := by
  rw [lane_eq, word_zero]; exact dgt_zero_left _

theorem lane_packW {f : ℕ → ℕ} (hf : ∀ i < 136, f i < 256) {i : ℕ} (hi : i < 136) :
    (packW f).lane i = f i := by
  rw [lane_eq, word_packW _ (by omega),
    dgt_packWord (fun l hl => hf _ (by omega)) (Nat.mod_lt _ (by norm_num))]
  congr 1
  omega

theorem lane_add {a b : W17} (h : ∀ i < 136, a.lane i + b.lane i < 256) {i : ℕ} (hi : i < 136) :
    (a.add b).lane i = a.lane i + b.lane i := by
  rw [lane_eq, lane_eq, lane_eq, word_add _ _ (by omega)]
  refine dgt_uadd (fun l hl => ?_) (Nat.mod_lt _ (by norm_num))
  have := h (8 * (i / 8) + l) (by omega)
  rwa [lane_eq, lane_eq, show (8 * (i / 8) + l) / 8 = i / 8 by omega,
    show (8 * (i / 8) + l) % 8 = l by omega] at this

@[expose] def toMatR (r d : ℕ) (M : Array (Array ℕ)) : Matrix (Fin r) (Fin d) (ZMod 5) :=
  Matrix.of fun i j => ((M[i.val]!)[j.val]! : ZMod 5)

@[expose] def toVecB (d : ℕ) (v : ByteArray) : Fin d → ZMod 5 :=
  fun j => ((v.get! j.val).toNat : ZMod 5)

theorem lane_frEntry (r d : ℕ) (M : Array (Array ℕ)) (g c : ℕ) {i : ℕ} (hi : i < 136) :
    (frEntry r d M g c).lane i = if i < r then frSum d M i g c % 5 else 0 := by
  unfold frEntry
  rw [lane_packW (fun i' _ => by split_ifs <;> omega) hi]

theorem lane_frEntry_le (r d : ℕ) (M : Array (Array ℕ)) (g c : ℕ) {i : ℕ} (hi : i < 136) :
    (frEntry r d M g c).lane i ≤ 4 := by
  rw [lane_frEntry r d M g c hi]; split_ifs <;> omega

theorem frTable_get (r d : ℕ) (M : Array (Array ℕ)) {g c : ℕ} (hg : g < ngroups d) (hc : c < 125) :
    (frTable r d M)[125 * g + c]! = frEntry r d M g c := by
  unfold frTable
  rw [getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]
  have h1 : (125 * g + c) / 125 = g := by omega
  have h2 : (125 * g + c) % 125 = c := by omega
  show frEntry r d M ((125 * g + c) / 125) ((125 * g + c) % 125) = _
  rw [h1, h2]

theorem fold_frAcc (d : ℕ) (T : Array W17) (v : ByteArray)
    (hT : ∀ g < ngroups d, ∀ i < 136, (T[125 * g + grpIdx v g]!).lane i ≤ 4)
    (hng : ngroups d ≤ 45) :
    ∀ m ≤ ngroups d, ∀ i < 136,
      (Nat.fold m (fun g _ acc => acc.add T[125 * g + grpIdx v g]!) W17.zero).lane i =
        ∑ g ∈ range m, (T[125 * g + grpIdx v g]!).lane i ∧
      (Nat.fold m (fun g _ acc => acc.add T[125 * g + grpIdx v g]!) W17.zero).lane i ≤ 4 * m := by
  intro m
  induction m with
  | zero => intro _ i _; simp [lane_zero]
  | succ m ih =>
    intro hm i hi
    rw [Nat.fold_succ]
    have hprev := fun i' hi' => ih (by omega) i' hi'
    have hno : ∀ i' < 136, (Nat.fold m (fun g _ acc => acc.add T[125 * g + grpIdx v g]!)
        W17.zero).lane i' + (T[125 * m + grpIdx v m]!).lane i' < 256 := by
      intro i' hi'
      have h1 := (hprev i' hi').2
      have h2 := hT m (by omega) i' hi'
      omega
    rw [lane_add hno hi, (hprev i hi).1, sum_range_succ]
    refine ⟨rfl, ?_⟩
    have h1 := (hprev i hi).2
    have h2 := hT m (by omega) i hi
    rw [← (hprev i hi).1]
    omega

theorem canonB_spec {d : ℕ} {v : ByteArray} (h : canonB d v = true) :
    v.size = d ∧ ∀ j < d, (v.get! j).toNat < 5 := by
  unfold canonB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, fun j hj => ?_⟩
  have := (CFSG.Sporadic.Th.allIn_eq_true.1 h.2) j (Nat.zero_le _) hj
  simpa using this

theorem dig_lt {d : ℕ} {v : ByteArray} (hv : canonB d v = true) (j : ℕ) : dig v j < 5 := by
  obtain ⟨hs, hlt⟩ := canonB_spec hv
  unfold dig
  split_ifs with h
  · exact hlt j (by omega)
  · norm_num

theorem dig_eq {d : ℕ} {v : ByteArray} (hv : canonB d v = true) {j : ℕ} (hj : j < d) :
    dig v j = (v.get! j).toNat := by
  obtain ⟨hs, -⟩ := canonB_spec hv
  unfold dig
  rw [ite_eq_left (by omega)]

theorem dig_of_ge {d : ℕ} {v : ByteArray} (hv : canonB d v = true) {j : ℕ} (hj : d ≤ j) :
    dig v j = 0 := by
  obtain ⟨hs, -⟩ := canonB_spec hv
  unfold dig
  rw [ite_eq_right (by omega)]

theorem grpIdx_lt {d : ℕ} {v : ByteArray} (hv : canonB d v = true) (g : ℕ) : grpIdx v g < 125 := by
  have h0 := dig_lt hv (3 * g)
  have h1 := dig_lt hv (3 * g + 1)
  have h2 := dig_lt hv (3 * g + 2)
  unfold grpIdx
  omega

theorem frSum_grpIdx {d : ℕ} {v : ByteArray} (hv : canonB d v = true) (M : Array (Array ℕ))
    (i g : ℕ) :
    frSum d M i g (grpIdx v g) = dig v (3 * g) * ent d M i (3 * g) +
      dig v (3 * g + 1) * ent d M i (3 * g + 1) + dig v (3 * g + 2) * ent d M i (3 * g + 2) := by
  have h0 := dig_lt hv (3 * g)
  have h1 := dig_lt hv (3 * g + 1)
  have h2 := dig_lt hv (3 * g + 2)
  unfold frSum grpIdx
  congr 3 <;> omega

theorem sum_groups (f : ℕ → ZMod 5) (m : ℕ) :
    ∑ g ∈ range m, (f (3 * g) + f (3 * g + 1) + f (3 * g + 2)) = ∑ j ∈ range (3 * m), f j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih, show 3 * (m + 1) = 3 * m + 1 + 1 + 1 by ring, sum_range_succ,
      sum_range_succ, sum_range_succ]
    ring

theorem ent_cast {d : ℕ} (M : Array (Array ℕ)) (i j : ℕ) :
    ((ent d M i j : ℕ) : ZMod 5) = if j < d then ((M[i]!)[j]! : ZMod 5) else 0 := by
  unfold ent; split_ifs <;> simp

theorem mulW_size (r d : ℕ) (T : Array W17) (v : ByteArray) : (mulW r d T v).size = r := by
  show (Array.ofFn (n := r) fun i => UInt8.ofNat ((frAcc d T v).lane i.val % 5)).size = r
  simp

theorem mulW_get (r d : ℕ) (T : Array W17) (v : ByteArray) {j : ℕ} (hj : j < r) :
    ((mulW r d T v).get! j).toNat = (frAcc d T v).lane j % 5 := by
  show ((Array.ofFn (n := r) fun i => UInt8.ofNat ((frAcc d T v).lane i.val % 5))[j]!).toNat = _
  rw [getElem!_pos _ j (by simp; omega), Array.getElem_ofFn]
  have hlane : (frAcc d T v).lane j % 5 < 256 := by omega
  rw [UInt8.toNat_ofNat_of_lt' hlane]

theorem toVecB_mulW {r d : ℕ} (hr : r ≤ 136) (hd : d ≤ 135) (M : Array (Array ℕ)) {v : ByteArray}
    (hv : canonB d v = true) :
    toVecB r (mulW r d (frTable r d M) v) = toMatR r d M *ᵥ toVecB d v := by
  have hng : ngroups d ≤ 45 := by unfold ngroups; omega
  have hT : ∀ g < ngroups d, ∀ i < 136, ((frTable r d M)[125 * g + grpIdx v g]!).lane i ≤ 4 := by
    intro g hg i hi
    rw [frTable_get r d M hg (grpIdx_lt hv g)]
    exact lane_frEntry_le r d M g _ hi
  funext i
  have hi : i.val < 136 := by omega
  have hacc := (fold_frAcc d (frTable r d M) v hT hng (ngroups d) le_rfl i.val hi).1
  rw [toVecB, Matrix.mulVec, dotProduct]
  rw [mulW_get r d _ v i.isLt, ZMod.natCast_mod]
  unfold frAcc
  rw [hacc, Nat.cast_sum]
  have hterm : ∀ g ∈ range (ngroups d), (((frTable r d M)[125 * g + grpIdx v g]!.lane i.val : ℕ) :
      ZMod 5) = (dig v (3 * g) : ZMod 5) * (ent d M i.val (3 * g) : ℕ) +
        (dig v (3 * g + 1) : ZMod 5) * (ent d M i.val (3 * g + 1) : ℕ) +
        (dig v (3 * g + 2) : ZMod 5) * (ent d M i.val (3 * g + 2) : ℕ) := by
    intro g hg
    rw [frTable_get r d M (mem_range.1 hg) (grpIdx_lt hv g), lane_frEntry r d M g _ hi,
      ite_eq_left i.isLt, ZMod.natCast_mod, frSum_grpIdx hv]
    push_cast
    ring
  rw [sum_congr rfl hterm]
  rw [sum_groups (fun j => (dig v j : ZMod 5) * (ent d M i.val j : ℕ))]
  have h3 : d ≤ 3 * ngroups d := by unfold ngroups; omega
  rw [← sum_range_add_sum_Ico _ h3]
  have hzero : ∑ j ∈ Ico d (3 * ngroups d), (dig v j : ZMod 5) * (ent d M i.val j : ℕ) = 0 := by
    refine sum_eq_zero fun j hj => ?_
    rw [dig_of_ge hv (mem_Ico.1 hj).1]
    simp
  rw [hzero, add_zero, ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun j _ => ?_
  rw [toMatR, Matrix.of_apply, dig_eq hv j.isLt, ent_cast, ite_eq_left j.isLt, mul_comm]
  rfl

theorem canonB_mulW (r d : ℕ) (T : Array W17) (v : ByteArray) : canonB r (mulW r d T v) = true := by
  unfold canonB
  rw [Bool.and_eq_true, beq_iff_eq, mulW_size, CFSG.Sporadic.Th.allIn_eq_true]
  refine ⟨rfl, fun j _ hj => ?_⟩
  rw [decide_eq_true_eq, mulW_get r d T v hj]
  omega

theorem eq_of_toVecB_eq {d : ℕ} {v w : ByteArray} (hv : canonB d v = true) (hw : canonB d w = true)
    (h : toVecB d v = toVecB d w) : v = w := by
  obtain ⟨hvs, hv'⟩ := canonB_spec hv
  obtain ⟨hws, hw'⟩ := canonB_spec hw
  apply ByteArray.ext
  apply Array.ext (show v.data.size = w.data.size from hvs.trans hws.symm)
  intro j hj hj'
  have hjd : j < d := by rw [← hvs]; exact hj
  have e := congrFun h ⟨j, hjd⟩
  simp only [toVecB] at e
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hv' j hjd), Nat.mod_eq_of_lt (hw' j hjd)] at e
  have e' : v.get! j = w.get! j := UInt8.toNat_inj.1 e
  simp only [ByteArray.get!] at e'
  rwa [getElem!_pos _ j hj, getElem!_pos _ j hj'] at e'

end CFSG.Sporadic.F5

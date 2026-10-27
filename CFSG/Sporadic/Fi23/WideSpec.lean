module

public import Certificates.Data.CFSGNative.Fi23.Wide
public import Certificates.Data.CFSGNative.F3.Sep
public import CFSG.F3.ConjSpec

public section

namespace CFSG.Sporadic.Fi23.Native

open CFSG.F3.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

@[expose] def limb (x0 x1 x2 x3 : UInt64) (l : ℕ) : UInt64 :=
  if l = 0 then x0 else if l = 1 then x1 else if l = 2 then x2 else if l = 3 then x3 else 0

theorem testBit_toNat_ge (x : UInt64) {i : ℕ} (hi : 64 ≤ i) : x.toNat.testBit i = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le x.toNat_lt (Nat.pow_le_pow_right (by norm_num) hi))

theorem testBit_join (x0 x1 x2 x3 : UInt64) (j : ℕ) :
    (join x0 x1 x2 x3).testBit j = (limb x0 x1 x2 x3 (j / 64)).toNat.testBit (j % 64) := by
  unfold join limb
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases h0 : j < 64
  · have e1 : j / 64 = 0 := by omega
    have e2 : j % 64 = j := by omega
    simp [e1, e2, show ¬ j ≥ 64 by omega, show ¬ j ≥ 128 by omega, show ¬ j ≥ 192 by omega]
  by_cases h1 : j < 128
  · have e1 : j / 64 = 1 := by omega
    have e2 : j % 64 = j - 64 := by omega
    simp [e1, e2, testBit_toNat_ge x0 (by omega : 64 ≤ j), show j ≥ 64 by omega,
      show ¬ j ≥ 128 by omega, show ¬ j ≥ 192 by omega]
  by_cases h2 : j < 192
  · have e1 : j / 64 = 2 := by omega
    have e2 : j % 64 = j - 128 := by omega
    simp [e1, e2, testBit_toNat_ge x0 (by omega : 64 ≤ j),
      testBit_toNat_ge x1 (by omega : 64 ≤ j - 64), show j ≥ 64 by omega, show j ≥ 128 by omega,
      show ¬ j ≥ 192 by omega]
  by_cases h3 : j < 256
  · have e1 : j / 64 = 3 := by omega
    have e2 : j % 64 = j - 192 := by omega
    simp [e1, e2, testBit_toNat_ge x0 (by omega : 64 ≤ j),
      testBit_toNat_ge x1 (by omega : 64 ≤ j - 64), testBit_toNat_ge x2 (by omega : 64 ≤ j - 128),
      show j ≥ 64 by omega, show j ≥ 128 by omega, show j ≥ 192 by omega]
  · have e1 : ¬ j / 64 = 0 ∧ ¬ j / 64 = 1 ∧ ¬ j / 64 = 2 ∧ ¬ j / 64 = 3 := by omega
    simp [e1, testBit_toNat_ge x0 (by omega : 64 ≤ j),
      testBit_toNat_ge x1 (by omega : 64 ≤ j - 64), testBit_toNat_ge x2 (by omega : 64 ≤ j - 128),
      testBit_toNat_ge x3 (by omega : 64 ≤ j - 192)]

theorem limb_and (x0 x1 x2 x3 y0 y1 y2 y3 : UInt64) (l : ℕ) :
    limb (x0 &&& y0) (x1 &&& y1) (x2 &&& y2) (x3 &&& y3) l =
      limb x0 x1 x2 x3 l &&& limb y0 y1 y2 y3 l := by
  unfold limb; split_ifs <;> simp

theorem limb_or (x0 x1 x2 x3 y0 y1 y2 y3 : UInt64) (l : ℕ) :
    limb (x0 ||| y0) (x1 ||| y1) (x2 ||| y2) (x3 ||| y3) l =
      limb x0 x1 x2 x3 l ||| limb y0 y1 y2 y3 l := by
  unfold limb; split_ifs <;> simp

theorem limb_xor (x0 x1 x2 x3 y0 y1 y2 y3 : UInt64) (l : ℕ) :
    limb (x0 ^^^ y0) (x1 ^^^ y1) (x2 ^^^ y2) (x3 ^^^ y3) l =
      limb x0 x1 x2 x3 l ^^^ limb y0 y1 y2 y3 l := by
  unfold limb; split_ifs <;> simp

theorem join_and (x0 x1 x2 x3 y0 y1 y2 y3 : UInt64) :
    join x0 x1 x2 x3 &&& join y0 y1 y2 y3 =
      join (x0 &&& y0) (x1 &&& y1) (x2 &&& y2) (x3 &&& y3) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, testBit_join, testBit_join, testBit_join, limb_and, UInt64.toNat_and,
    Nat.testBit_and]

theorem join_or (x0 x1 x2 x3 y0 y1 y2 y3 : UInt64) :
    join x0 x1 x2 x3 ||| join y0 y1 y2 y3 =
      join (x0 ||| y0) (x1 ||| y1) (x2 ||| y2) (x3 ||| y3) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, testBit_join, testBit_join, testBit_join, limb_or, UInt64.toNat_or,
    Nat.testBit_or]

theorem join_xor (x0 x1 x2 x3 y0 y1 y2 y3 : UInt64) :
    join x0 x1 x2 x3 ^^^ join y0 y1 y2 y3 =
      join (x0 ^^^ y0) (x1 ^^^ y1) (x2 ^^^ y2) (x3 ^^^ y3) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, testBit_join, testBit_join, testBit_join, limb_xor, UInt64.toNat_xor,
    Nat.testBit_xor]

theorem join_zero : join 0 0 0 0 = 0 := by decide

theorem limb_eq_of_join {x0 x1 x2 x3 y0 y1 y2 y3 : UInt64}
    (h : join x0 x1 x2 x3 = join y0 y1 y2 y3) (l : ℕ) :
    limb x0 x1 x2 x3 l = limb y0 y1 y2 y3 l := by
  apply UInt64.toNat_inj.1
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · have e := congrArg (fun x => Nat.testBit x (64 * l + i)) h
    simp only [testBit_join] at e
    rwa [show (64 * l + i) / 64 = l by omega, show (64 * l + i) % 64 = i by omega] at e
  · rw [testBit_toNat_ge _ (by omega), testBit_toNat_ge _ (by omega)]

theorem join_inj {x0 x1 x2 x3 y0 y1 y2 y3 : UInt64} (h : join x0 x1 x2 x3 = join y0 y1 y2 y3) :
    x0 = y0 ∧ x1 = y1 ∧ x2 = y2 ∧ x3 = y3 :=
  ⟨by simpa [limb] using limb_eq_of_join h 0, by simpa [limb] using limb_eq_of_join h 1,
    by simpa [limb] using limb_eq_of_join h 2, by simpa [limb] using limb_eq_of_join h 3⟩

theorem W.toV_add (a b : W) : (a.add b).toV = a.toV.add b.toV := by
  simp only [W.add, W.toV, V.add, addP, addM, join_and, join_or, join_xor]

theorem W.toV_neg (a : W) : a.neg.toV = a.toV.neg := rfl

theorem W.toV_sub (a b : W) : (a.sub b).toV = a.toV.sub b.toV := by
  rw [W.sub, W.toV_add, W.toV_neg, V.sub]

theorem W.toV_zero : W.zero.toV = V.zero := by
  simp only [W.zero, W.toV, join_zero, V.zero]

theorem W.toV_default : (default : W).toV = (default : V) := W.toV_zero

theorem W.toV_inj {a b : W} (h : a.toV = b.toV) : a = b := by
  simp only [W.toV, V.mk.injEq] at h
  obtain ⟨hp0, hp1, hp2, hp3⟩ := join_inj h.1
  obtain ⟨hm0, hm1, hm2, hm3⟩ := join_inj h.2
  cases a; cases b
  simp_all

theorem uint64_ne_zero (y : UInt64) : (y != 0) = (y.toNat != 0) := by
  by_cases h : y = 0
  · subst h; rfl
  · have : y.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.1 (by rw [e]; rfl))
    rw [bne_iff_ne.2 h, bne_iff_ne.2 this]

theorem uint64_bit (x : UInt64) (j : ℕ) :
    ((x >>> (j &&& 63).toUInt64) &&& 1 != 0) = x.toNat.testBit (j % 64) := by
  have hj : j &&& 63 = j % 64 := by
    rw [show (63 : ℕ) = 2 ^ 6 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  have hs : ((j &&& 63).toUInt64).toNat % 64 = j % 64 := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', hj, Nat.mod_eq_of_lt (by omega : j % 64 < 2 ^ 64)]
    omega
  have h1 : ((x >>> (j &&& 63).toUInt64) &&& 1).toNat = x.toNat >>> (j % 64) &&& 1 := by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight, hs, UInt64.toNat_one]
  unfold Nat.testBit
  rw [Nat.land_comm 1, ← h1, uint64_ne_zero]

theorem shiftRight_six (j : ℕ) : j >>> 6 = j / 64 := by
  rw [Nat.shiftRight_eq_div_pow]

theorem W.limbP_eq (a : W) (l : ℕ) : a.limbP l = limb a.p0 a.p1 a.p2 a.p3 l := rfl

theorem W.limbM_eq (a : W) (l : ℕ) : a.limbM l = limb a.m0 a.m1 a.m2 a.m3 l := rfl

theorem W.bitP_eq (a : W) (j : ℕ) : a.bitP j = a.toV.p.testBit j := by
  rw [W.bitP, uint64_bit, W.toV, testBit_join, shiftRight_six, W.limbP_eq]

theorem W.bitM_eq (a : W) (j : ℕ) : a.bitM j = a.toV.m.testBit j := by
  rw [W.bitM, uint64_bit, W.toV, testBit_join, shiftRight_six, W.limbM_eq]

theorem toVM_getElem! (X : Array W) (j : ℕ) : (toVM X)[j]! = X[j]!.toV := by
  unfold toVM
  by_cases hj : j < X.size
  · rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map, getElem!_pos X j hj]
  · rw [getElem!_neg _ j (by simpa using hj), getElem!_neg X j hj, W.toV_default]

theorem toVM_size (X : Array W) : (toVM X).size = X.size := Array.size_map

theorem fold_toV {f : ℕ → W → W} {g : ℕ → V → V} (h : ∀ j a, (f j a).toV = g j a.toV) (n : ℕ)
    (init : W) :
    (Nat.fold n (fun j _ a => f j a) init).toV = Nat.fold n (fun j _ b => g j b) init.toV := by
  induction n with
  | zero => rw [Nat.fold_zero, Nat.fold_zero]
  | succ n ih => rw [Nat.fold_succ, Nat.fold_succ, h, ih]

theorem toV_combW (d : ℕ) (Y : Array W) (r : W) : (combW d Y r).toV = comb d (toVM Y) r.toV := by
  unfold combW comb
  rw [← W.toV_zero]
  apply fold_toV
  intro j acc
  rw [W.bitP_eq, W.bitM_eq, toVM_getElem!]
  split_ifs
  · exact W.toV_add _ _
  · exact W.toV_sub _ _
  · rfl

theorem toVM_mulW (d : ℕ) (X Y : Array W) : toVM (mulW d X Y) = mul d (toVM X) (toVM Y) := by
  unfold toVM mulW CFSG.F3.Native.mul
  rw [Array.map_map, Array.map_map]
  congr 1
  funext r
  exact toV_combW d Y r

theorem toVM_conjW (d : ℕ) (g gi X : Array W) :
    toVM (conjW d g gi X) = conjM d (toVM g) (toVM gi) (toVM X) := by
  unfold conjW conjM
  rw [toVM_mulW, toVM_mulW]

theorem toVM_inj {X Y : Array W} (h : toVM X = toVM Y) : X = Y := by
  unfold toVM at h
  apply Array.ext (by simpa using congrArg Array.size h)
  intro i hi hi'
  have := congrArg (fun Z : Array V => Z[i]!) h
  rw [getElem!_pos _ i (by simpa using hi), getElem!_pos _ i (by simpa using hi'),
    Array.getElem_map, Array.getElem_map] at this
  exact W.toV_inj this

theorem eq_of_eqW {d : ℕ} {X Y : Array W} (h : eqW d X Y = true) : X.size = d ∧ X = Y := by
  unfold eqW at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact h

theorem testBit_ofNat_shift (x : ℕ) (k i : ℕ) (hi : i < 64) :
    (UInt64.ofNat (x >>> k)).toNat.testBit i = x.testBit (k + i) := by
  rw [UInt64.toNat_ofNat', Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp [hi]

theorem join_ofV (x : ℕ) (hx : x < 2 ^ 256) :
    join (UInt64.ofNat x) (UInt64.ofNat (x >>> 64)) (UInt64.ofNat (x >>> 128))
      (UInt64.ofNat (x >>> 192)) = x := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_join]
  have hm : j % 64 < 64 := Nat.mod_lt _ (by norm_num)
  unfold limb
  by_cases h0 : j / 64 = 0
  · rw [ite_eq_left h0, UInt64.toNat_ofNat', Nat.testBit_mod_two_pow]
    simp only [hm, decide_true, Bool.true_and]
    congr 1; omega
  rw [ite_eq_right h0]
  by_cases h1 : j / 64 = 1
  · rw [ite_eq_left h1, testBit_ofNat_shift _ _ _ hm]; congr 1; omega
  rw [ite_eq_right h1]
  by_cases h2 : j / 64 = 2
  · rw [ite_eq_left h2, testBit_ofNat_shift _ _ _ hm]; congr 1; omega
  rw [ite_eq_right h2]
  by_cases h3 : j / 64 = 3
  · rw [ite_eq_left h3, testBit_ofNat_shift _ _ _ hm]; congr 1; omega
  rw [ite_eq_right h3]
  have hj : 256 ≤ j := by omega
  rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hj))]
  simp

theorem W.toV_ofV {v : V} (hp : v.p < 2 ^ 256) (hm : v.m < 2 ^ 256) : (ofV v).toV = v := by
  simp only [ofV, W.toV, join_ofV _ hp, join_ofV _ hm]

theorem toVM_map_ofV {X : Array V} (h : ∀ v ∈ X, v.p < 2 ^ 256 ∧ v.m < 2 ^ 256) :
    toVM (X.map ofV) = X := by
  unfold toVM
  rw [Array.map_map]
  conv_rhs => rw [← Array.map_id X]
  apply Array.map_congr_left
  intro v hv
  exact W.toV_ofV (h v hv).1 (h v hv).2

theorem V.ofFn_lt (d : ℕ) (f : ℕ → ℕ) : (V.ofFn d f).p < 2 ^ d ∧ (V.ofFn d f).m < 2 ^ d := by
  have key : ∀ x : ℕ, (∀ j, x.testBit j = true → j < d) → x < 2 ^ d := by
    intro x hx
    apply Nat.lt_pow_two_of_testBit
    intro j hj
    by_contra hc
    have := hx j (by simpa using hc)
    omega
  rw [ofFn_eq_fold]
  constructor
  · apply key
    intro j hj
    rw [(fold_ofFnStep_bits f j d).1] at hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
    exact hj.1
  · apply key
    intro j hj
    rw [(fold_ofFnStep_bits f j d).2] at hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
    exact hj.1

theorem toVM_rowsOf {d : ℕ} (hd : d ≤ 256) (s : String) :
    toVM ((CFSG.F3.Native.rowsOf d s).map ofV) = CFSG.F3.Native.rowsOf d s := by
  apply toVM_map_ofV
  intro v hv
  unfold CFSG.F3.Native.rowsOf at hv
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hv
  rw [Array.getElem_ofFn]
  obtain ⟨h1, h2⟩ := V.ofFn_lt d _
  exact ⟨lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) hd),
    lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by norm_num) hd)⟩

theorem toVM_idW {d : ℕ} (hd : d ≤ 256) : toVM (idW d) = idM d := by
  apply toVM_map_ofV
  intro v hv
  unfold idM at hv
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hv
  rw [Array.getElem_ofFn]
  simp only [Array.size_ofFn] at hi
  refine ⟨?_, by simp⟩
  rw [Nat.one_shiftLeft]
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem toVM_powW {d : ℕ} (hd : d ≤ 256) (M : Array W) (e : ℕ) :
    toVM (powW d M e) = powM d (toVM M) e := by
  induction e with
  | zero => exact toVM_idW hd
  | succ e ih => rw [powW, powM, toVM_mulW, ih]

theorem toVM_prodW {d : ℕ} (hd : d ≤ 256) (mats : Array (Array W)) (word : List ℕ) :
    toVM (prodW d mats word) = prodM d (mats.map toVM) word := by
  unfold prodW prodM
  rw [← toVM_idW hd]
  generalize idW d = M
  induction word generalizing M with
  | nil => rfl
  | cons x w ih =>
    rw [List.foldl_cons, List.foldl_cons, ih, toVM_mulW]
    congr 2
    by_cases hx : x < mats.size
    · rw [getElem!_pos (mats.map toVM) x (by simpa using hx), Array.getElem_map,
        getElem!_pos mats x hx]
    · rw [getElem!_neg (mats.map toVM) x (by simpa using hx), getElem!_neg mats x hx]
      show toVM #[] = #[]
      simp [toVM]

theorem W.wf_spec {a : W} (h : a.wf = true) : a.toV.wf = true := by
  unfold W.wf at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  unfold V.wf W.toV
  simp only [join_and, h0, h1, h2, h3, join_zero, beq_self_eq_true]

theorem shiftRight_join_eq_zero {x0 x1 x2 x3 : UInt64} {d : ℕ} (hd : 192 ≤ d) (hd' : d < 256)
    (h : x3 >>> (d - 192).toUInt64 = 0) : join x0 x1 x2 x3 >>> d = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_shiftRight, Nat.zero_testBit, testBit_join]
  have h3 : ∀ t, d - 192 ≤ t → x3.toNat.testBit t = false := by
    intro t ht
    have e := congrArg (fun y : UInt64 => y.toNat.testBit (t - (d - 192))) h
    simp only [UInt64.toNat_shiftRight, Nat.testBit_shiftRight, UInt64.toNat_zero,
      Nat.zero_testBit] at e
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : d - 192 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : d - 192 < 64)] at e
    rwa [show d - 192 + (t - (d - 192)) = t by omega] at e
  unfold limb
  by_cases h4 : (d + i) / 64 = 3
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left h4]
    exact h3 _ (by omega)
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right h4]
    simp

theorem W.canon_spec {d : ℕ} (hd : 192 ≤ d) (hd' : d < 256) {a : W} (h : a.canon d = true) :
    (a.toV.wf && a.toV.p >>> d == 0 && a.toV.m >>> d == 0) = true := by
  unfold W.canon at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h ⊢
  obtain ⟨⟨hw, hp⟩, hm⟩ := h
  exact ⟨⟨W.wf_spec hw, shiftRight_join_eq_zero hd hd' hp⟩, shiftRight_join_eq_zero hd hd' hm⟩

theorem canonM_of_canonW {d : ℕ} (hd : 192 ≤ d) (hd' : d < 256) {X : Array W}
    (h : canonW d X = true) : canonM d (toVM X) = true := by
  unfold canonW at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true] at h
  unfold canonM
  rw [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]
  refine ⟨by rw [toVM_size]; exact h.1, fun i hi => ?_⟩
  simp only [toVM, Array.getElem_map]
  exact W.canon_spec hd hd' (h.2 i (by simpa [toVM] using hi))

noncomputable abbrev toMatW (d : ℕ) (X : Array W) : Matrix (Fin d) (Fin d) (ZMod 3) :=
  toMat d (toVM X)

structure WConjFacts (d : ℕ) (R A Ai B Bi : Array W) (O : WOrbit) : Prop where
  size_pos : 0 < O.keys.size
  size_lt : O.keys.size < 2 ^ 32
  canon : ∀ k < O.keys.size, canonW d O.keys[k]! = true
  alpha : ∀ k < O.keys.size, ap O.alpha k < O.keys.size ∧
    toMatW d O.keys[ap O.alpha k]! = toMatW d A * toMatW d O.keys[k]! * toMatW d Ai
  beta : ∀ k < O.keys.size, ap O.beta k < O.keys.size ∧
    toMatW d O.keys[ap O.beta k]! = toMatW d B * toMatW d O.keys[k]! * toMatW d Bi
  inj : ∀ i < O.keys.size, ∀ j < O.keys.size, toMatW d O.keys[i]! = toMatW d O.keys[j]! → i = j
  tree : ∀ k < O.keys.size, 0 < k → ap O.par k < k ∧
    ((ap O.lab k = 1 ∧ ap O.alpha (ap O.par k) = k) ∨ (ap O.lab k = 2 ∧ ap O.beta (ap O.par k) = k))
  root : O.keys[0]! = R

theorem toMatW_conjW {d : ℕ} {g gi X : Array W} (hgs : g.size = d) (hg : RowsWF (toVM g))
    (hgi : RowsWF (toVM gi)) (hX : RowsWF (toVM X)) :
    toMatW d (conjW d g gi X) = toMatW d g * toMatW d X * toMatW d gi := by
  rw [toMatW, toVM_conjW, toMat_conjM (by rw [toVM_size, hgs]) hg hgi hX]

theorem conjOrbitOKW_facts {d : ℕ} (hd : 192 ≤ d) (hd' : d < 256) {R A Ai B Bi : Array W}
    {O : WOrbit} {c : ℕ} (hAs : A.size = d) (hA : RowsWF (toVM A)) (hAi : RowsWF (toVM Ai))
    (hBs : B.size = d) (hB : RowsWF (toVM B)) (hBi : RowsWF (toVM Bi))
    (hA2 : toMatW d A * toMatW d A = 1) (hAi2 : toMatW d Ai * toMatW d Ai = 1)
    (hB3 : toMatW d B ^ 3 = 1) (hBi3 : toMatW d Bi ^ 3 = 1)
    (h : conjOrbitOKW d R A Ai B Bi O c = true) : WConjFacts d R A Ai B Bi O := by
  unfold conjOrbitOKW at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hpos, hlt⟩, hroot⟩, hinvo⟩, hord3⟩, hall⟩ := h
  set pos : Array W → ℕ := fun X => (indexOfW O.keys).getD X O.keys.size
  have hat := parAll_eq_true hall
  have hk : ∀ k < O.keys.size, canonW d O.keys[k]! = true ∧ pos O.keys[k]! = k ∧
      ap O.alpha k < O.keys.size ∧ ap O.beta k < O.keys.size ∧
      (ap O.alpha k < k ∨ eqW d (conjW d A Ai O.keys[k]!) O.keys[ap O.alpha k]! = true) ∧
      ((ap O.beta k < k ∧ ap O.beta (ap O.beta k) < k) ∨
        eqW d (conjW d B Bi O.keys[k]!) O.keys[ap O.beta k]! = true) ∧
      (k = 0 ∨ (ap O.par k < k ∧ ((ap O.lab k = 1 ∧ ap O.alpha (ap O.par k) = k) ∨
        (ap O.lab k = 2 ∧ ap O.beta (ap O.par k) = k)))) := by
    intro k hk
    have := hat k hk
    simp only [conjCheckAtW, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true]
      at this
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := this
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have hwf : ∀ k < O.keys.size, RowsWF (toVM O.keys[k]!) := fun k hk' =>
    RowsWF.of_canonM (canonM_of_canonW hd hd' (hk k hk').1)
  have hinvo' : ∀ k < O.keys.size, ap O.alpha (ap O.alpha k) = k := fun k hk' => by
    have := (allIn_eq_true.1 hinvo) k (Nat.zero_le _) hk'
    simpa using this
  have hord3' : ∀ k < O.keys.size, ap O.beta (ap O.beta (ap O.beta k)) = k := fun k hk' => by
    have := (allIn_eq_true.1 hord3) k (Nat.zero_le _) hk'
    simpa using this
  have hdirA : ∀ k < O.keys.size, ¬ ap O.alpha k < k →
      toMatW d O.keys[ap O.alpha k]! = toMatW d A * toMatW d O.keys[k]! * toMatW d Ai := by
    intro k hk' hnot
    rcases (hk k hk').2.2.2.2.1 with h0 | he
    · exact absurd h0 hnot
    · rw [← (eq_of_eqW he).2, toMatW_conjW hAs hA hAi (hwf k hk')]
  have hdirB : ∀ k < O.keys.size, ¬ (ap O.beta k < k ∧ ap O.beta (ap O.beta k) < k) →
      toMatW d O.keys[ap O.beta k]! = toMatW d B * toMatW d O.keys[k]! * toMatW d Bi := by
    intro k hk' hnot
    rcases (hk k hk').2.2.2.2.2.1 with h0 | he
    · exact absurd h0 hnot
    · rw [← (eq_of_eqW he).2, toMatW_conjW hBs hB hBi (hwf k hk')]
  refine ⟨hpos, hlt, fun k hk' => (hk k hk').1, ?_, ?_, ?_, ?_, (eq_of_eqW hroot).2⟩
  · intro k hk'
    refine ⟨(hk k hk').2.2.1, ?_⟩
    by_cases hlk : ap O.alpha k < k
    ·
      have hjN : ap O.alpha k < O.keys.size := (hk k hk').2.2.1
      have hjk : ap O.alpha (ap O.alpha k) = k := hinvo' k hk'
      have e := hdirA (ap O.alpha k) hjN (by rw [hjk]; omega)
      rw [hjk] at e
      rw [e, ← mul_assoc, ← mul_assoc, hA2, one_mul, mul_assoc, hAi2, mul_one]
    · exact hdirA k hk' hlk
  · intro k hk'
    refine ⟨(hk k hk').2.2.2.1, ?_⟩
    by_cases hlk : ap O.beta k < k ∧ ap O.beta (ap O.beta k) < k
    ·
      have hpN : ap O.beta k < O.keys.size := (hk k hk').2.2.2.1
      have hqN : ap O.beta (ap O.beta k) < O.keys.size := (hk _ hpN).2.2.2.1
      have hqk : ap O.beta (ap O.beta (ap O.beta k)) = k := hord3' k hk'
      have e1 := hdirB (ap O.beta k) hpN (fun h => by rw [hqk] at h; omega)
      have e2 := hdirB (ap O.beta (ap O.beta k)) hqN (fun h => by rw [hqk] at h; omega)
      rw [hqk] at e2
      rw [e2, e1]
      symm
      calc toMatW d B * (toMatW d B * (toMatW d B * toMatW d O.keys[ap O.beta k]! *
            toMatW d Bi) * toMatW d Bi) * toMatW d Bi
          = toMatW d B ^ 3 * toMatW d O.keys[ap O.beta k]! * toMatW d Bi ^ 3 := by
            simp only [pow_three, mul_assoc]
        _ = toMatW d O.keys[ap O.beta k]! := by rw [hB3, hBi3, one_mul, mul_one]
    · exact hdirB k hk' hlk
  · intro i hi j hj hij
    have e := toVM_inj (eq_of_canonM (canonM_of_canonW hd hd' (hk i hi).1)
      (canonM_of_canonW hd hd' (hk j hj).1) hij)
    rw [← (hk i hi).2.1, ← (hk j hj).2.1, e]
  · intro k hk' hk0
    rcases (hk k hk').2.2.2.2.2.2 with h0 | h1
    · omega
    · exact h1

end CFSG.Sporadic.Fi23.Native

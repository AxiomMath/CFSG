module

public import Certificates.Data.CFSGNative.Suz.W64
public import CFSG.F3.ConjSpec

public section

namespace CFSG.Sporadic.Suz.Native

open CFSG.F3.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

theorem W.toV_add (a b : W) : (a.add b).toV = a.toV.add b.toV := by
  simp only [W.add, W.toV, V.add, UInt64.toNat_or, UInt64.toNat_and, UInt64.toNat_xor]

theorem W.toV_neg (a : W) : a.neg.toV = a.toV.neg := rfl

theorem W.toV_sub (a b : W) : (a.sub b).toV = a.toV.sub b.toV := by
  rw [W.sub, W.toV_add, W.toV_neg, V.sub]

theorem W.toV_zero : W.zero.toV = V.zero := rfl

theorem W.toV_default : (default : W).toV = (default : V) := rfl

theorem W.toV_inj {a b : W} (h : a.toV = b.toV) : a = b := by
  obtain ⟨ap, am⟩ := a
  obtain ⟨bp, bm⟩ := b
  simp only [W.toV, V.mk.injEq] at h
  rw [UInt64.toNat_inj.1 h.1, UInt64.toNat_inj.1 h.2]

theorem testBit_toNat_ge (x : UInt64) {i : ℕ} (hi : 64 ≤ i) : x.toNat.testBit i = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le x.toNat_lt (Nat.pow_le_pow_right (by norm_num) hi))

theorem uint64_ne_zero (y : UInt64) : (y != 0) = (y.toNat != 0) := by
  by_cases h : y = 0
  · subst h; rfl
  · have : y.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.1 (by rw [e]; rfl))
    rw [bne_iff_ne.2 h, bne_iff_ne.2 this]

theorem uint64_bit (x : UInt64) {j : ℕ} (hj : j < 64) :
    ((x >>> j.toUInt64) &&& 1 != 0) = x.toNat.testBit j := by
  have hs : (j.toUInt64).toNat % 64 = j := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : j < 2 ^ 64)]
    omega
  have h1 : ((x >>> j.toUInt64) &&& 1).toNat = x.toNat >>> j &&& 1 := by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight, hs, UInt64.toNat_one]
  unfold Nat.testBit
  rw [Nat.land_comm 1, ← h1, uint64_ne_zero]

theorem W.bitP_eq (a : W) (j : ℕ) : a.bitP j = a.toV.p.testBit j := by
  unfold W.bitP W.toV
  split_ifs with hj
  · exact uint64_bit a.p hj
  · exact (testBit_toNat_ge a.p (by omega)).symm

theorem W.bitM_eq (a : W) (j : ℕ) : a.bitM j = a.toV.m.testBit j := by
  unfold W.bitM W.toV
  split_ifs with hj
  · exact uint64_bit a.m hj
  · exact (testBit_toNat_ge a.m (by omega)).symm

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

theorem W.toV_ofV {v : V} (hp : v.p < 2 ^ 64) (hm : v.m < 2 ^ 64) : (ofV v).toV = v := by
  simp only [ofV, W.toV, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hm]

theorem toVM_map_ofV {X : Array V} (h : ∀ v ∈ X, v.p < 2 ^ 64 ∧ v.m < 2 ^ 64) :
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

theorem toVM_rowsOf {d : ℕ} (hd : d ≤ 64) (s : String) :
    toVM ((CFSG.F3.Native.rowsOf d s).map ofV) = CFSG.F3.Native.rowsOf d s := by
  apply toVM_map_ofV
  intro v hv
  unfold CFSG.F3.Native.rowsOf at hv
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hv
  rw [Array.getElem_ofFn]
  obtain ⟨h1, h2⟩ := V.ofFn_lt d _
  exact ⟨lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) hd),
    lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by norm_num) hd)⟩

theorem toVM_idW {d : ℕ} (hd : d ≤ 64) : toVM (idW d) = idM d := by
  apply toVM_map_ofV
  intro v hv
  unfold idM at hv
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hv
  rw [Array.getElem_ofFn]
  simp only [Array.size_ofFn] at hi
  refine ⟨?_, by simp⟩
  rw [Nat.one_shiftLeft]
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem toVM_powW {d : ℕ} (hd : d ≤ 64) (M : Array W) (e : ℕ) :
    toVM (powW d M e) = powM d (toVM M) e := by
  induction e with
  | zero => exact toVM_idW hd
  | succ e ih => rw [powW, powM, toVM_mulW, ih]

theorem W.wf_spec {a : W} (h : a.wf = true) : a.toV.wf = true := by
  unfold W.wf at h
  rw [beq_iff_eq] at h
  unfold V.wf W.toV
  rw [beq_iff_eq, ← UInt64.toNat_and, h]
  rfl

theorem toNat_shiftRight_64 (x : UInt64) : x.toNat >>> 64 = 0 := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt x.toNat_lt

theorem canonM_of_canonW {X : Array W} (h : canonW X = true) : canonM 64 (toVM X) = true := by
  unfold canonW at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true] at h
  unfold canonM
  rw [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]
  refine ⟨by rw [toVM_size]; exact h.1, fun i hi => ?_⟩
  simp only [toVM, Array.getElem_map]
  have hw := W.wf_spec (h.2 i (by simpa [toVM] using hi))
  unfold W.toV at hw
  simp only [W.toV, toNat_shiftRight_64, beq_self_eq_true, Bool.and_true]
  exact hw

noncomputable abbrev toMatW (X : Array W) : Matrix (Fin 64) (Fin 64) (ZMod 3) :=
  toMat 64 (toVM X)

structure WConjFacts (R A Ai B Bi : Array W) (O : WOrbit) : Prop where
  size_pos : 0 < O.keys.size
  size_lt : O.keys.size < 2 ^ 32
  canon : ∀ k < O.keys.size, canonW O.keys[k]! = true
  alpha : ∀ k < O.keys.size, ap O.alpha k < O.keys.size ∧
    toMatW O.keys[ap O.alpha k]! = toMatW A * toMatW O.keys[k]! * toMatW Ai
  beta : ∀ k < O.keys.size, ap O.beta k < O.keys.size ∧
    toMatW O.keys[ap O.beta k]! = toMatW B * toMatW O.keys[k]! * toMatW Bi
  inj : ∀ i < O.keys.size, ∀ j < O.keys.size, toMatW O.keys[i]! = toMatW O.keys[j]! → i = j
  tree : ∀ k < O.keys.size, 0 < k → ap O.par k < k ∧
    ((ap O.lab k = 1 ∧ ap O.alpha (ap O.par k) = k) ∨ (ap O.lab k = 2 ∧ ap O.beta (ap O.par k) = k))
  root : O.keys[0]! = R

theorem toMatW_conjW {g gi X : Array W} (hgs : g.size = 64) (hg : RowsWF (toVM g))
    (hgi : RowsWF (toVM gi)) (hX : RowsWF (toVM X)) :
    toMatW (conjW 64 g gi X) = toMatW g * toMatW X * toMatW gi := by
  rw [toMatW, toVM_conjW, toMat_conjM (by rw [toVM_size, hgs]) hg hgi hX]

theorem conjOrbitOKW_facts {R A Ai B Bi : Array W} {O : WOrbit} {c : ℕ} (hAs : A.size = 64)
    (hA : RowsWF (toVM A)) (hAi : RowsWF (toVM Ai)) (hBs : B.size = 64) (hB : RowsWF (toVM B))
    (hBi : RowsWF (toVM Bi)) (hA2 : toMatW A * toMatW A = 1) (hAi2 : toMatW Ai * toMatW Ai = 1)
    (hB3 : toMatW B ^ 3 = 1) (hBi3 : toMatW Bi ^ 3 = 1)
    (h : conjOrbitOKW 64 R A Ai B Bi O c = true) : WConjFacts R A Ai B Bi O := by
  unfold conjOrbitOKW at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hpos, hlt⟩, hroot⟩, hinvo⟩, hord3⟩, hall⟩ := h
  set pos : Array W → ℕ := fun X => (indexOfW O.keys).getD X O.keys.size
  have hat := parAll_eq_true hall
  have hk : ∀ k < O.keys.size, canonW O.keys[k]! = true ∧ pos O.keys[k]! = k ∧
      ap O.alpha k < O.keys.size ∧ ap O.beta k < O.keys.size ∧
      (ap O.alpha k < k ∨ eqW 64 (conjW 64 A Ai O.keys[k]!) O.keys[ap O.alpha k]! = true) ∧
      ((ap O.beta k < k ∧ ap O.beta (ap O.beta k) < k) ∨
        eqW 64 (conjW 64 B Bi O.keys[k]!) O.keys[ap O.beta k]! = true) ∧
      (k = 0 ∨ (ap O.par k < k ∧ ((ap O.lab k = 1 ∧ ap O.alpha (ap O.par k) = k) ∨
        (ap O.lab k = 2 ∧ ap O.beta (ap O.par k) = k)))) := by
    intro k hk
    have := hat k hk
    simp only [conjCheckAtW, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true]
      at this
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := this
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have hwf : ∀ k < O.keys.size, RowsWF (toVM O.keys[k]!) := fun k hk' =>
    RowsWF.of_canonM (canonM_of_canonW (hk k hk').1)
  have hinvo' : ∀ k < O.keys.size, ap O.alpha (ap O.alpha k) = k := fun k hk' => by
    have := (allIn_eq_true.1 hinvo) k (Nat.zero_le _) hk'
    simpa using this
  have hord3' : ∀ k < O.keys.size, ap O.beta (ap O.beta (ap O.beta k)) = k := fun k hk' => by
    have := (allIn_eq_true.1 hord3) k (Nat.zero_le _) hk'
    simpa using this
  have hdirA : ∀ k < O.keys.size, ¬ ap O.alpha k < k →
      toMatW O.keys[ap O.alpha k]! = toMatW A * toMatW O.keys[k]! * toMatW Ai := by
    intro k hk' hnot
    rcases (hk k hk').2.2.2.2.1 with h0 | he
    · exact absurd h0 hnot
    · rw [← (eq_of_eqW he).2, toMatW_conjW hAs hA hAi (hwf k hk')]
  have hdirB : ∀ k < O.keys.size, ¬ (ap O.beta k < k ∧ ap O.beta (ap O.beta k) < k) →
      toMatW O.keys[ap O.beta k]! = toMatW B * toMatW O.keys[k]! * toMatW Bi := by
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
      calc toMatW B * (toMatW B * (toMatW B * toMatW O.keys[ap O.beta k]! *
            toMatW Bi) * toMatW Bi) * toMatW Bi
          = toMatW B ^ 3 * toMatW O.keys[ap O.beta k]! * toMatW Bi ^ 3 := by
            simp only [pow_three, mul_assoc]
        _ = toMatW O.keys[ap O.beta k]! := by rw [hB3, hBi3, one_mul, mul_one]
    · exact hdirB k hk' hlk
  · intro i hi j hj hij
    have e := toVM_inj (eq_of_canonM (canonM_of_canonW (hk i hi).1)
      (canonM_of_canonW (hk j hj).1) hij)
    rw [← (hk i hi).2.1, ← (hk j hj).2.1, e]
  · intro k hk' hk0
    rcases (hk k hk').2.2.2.2.2.2 with h0 | h1
    · omega
    · exact h1

end CFSG.Sporadic.Suz.Native

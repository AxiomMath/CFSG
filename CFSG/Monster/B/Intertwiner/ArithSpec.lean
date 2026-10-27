module

public import Certificates.Data.CFSGNative.MonsterB.IntertwinerArith
public import Batteries.Data.ByteArray
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
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Monster.B.Bin

open Matrix Finset

@[expose] noncomputable def rowVec (n : ℕ) (r : Row) : Fin n → ZMod 2 :=
  fun j => if bitOf r j then 1 else 0

@[expose] noncomputable def cmat (n : ℕ) (X : Mat) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun i j => rowVec n (X.getD i #[]) j

theorem cmat_apply (n : ℕ) (X : Mat) (i j : Fin n) : cmat n X i j = rowVec n (X.getD i #[]) j :=
  rfl

theorem rowVec_ext {n : ℕ} {r s : Row} (h : ∀ j < n, bitOf r j = bitOf s j) :
    rowVec n r = rowVec n s := by
  funext j
  simp only [rowVec, h j j.2]

theorem bitOf_def (r : Row) (j : ℕ) : bitOf r j = (r.getD (j / 56) 0).testBit (j % 56) := rfl

theorem bitOf_empty (j : ℕ) : bitOf #[] j = false := by
  simp [bitOf_def]

theorem rowVec_empty (n : ℕ) : rowVec n #[] = 0 := by
  funext j
  simp [rowVec, bitOf_empty]

theorem nch_spec {n j : ℕ} (hj : j < n) : j / 56 < nch n := by
  unfold nch
  omega

theorem getD_setIfInBounds (a : Row) (w v c : ℕ) :
    (a.setIfInBounds w v).getD c 0 = if c = w ∧ w < a.size then v else a.getD c 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases hcw : w = c
  · subst hcw
    by_cases hw : w < a.size
    · simp [hw]
    · simp [hw]
  · simp [hcw, Ne.symm hcw]

theorem xorGo_size (s : Row) (m w : ℕ) (a : Row) : (xorGo s m w a).size = a.size := by
  induction w, a using xorGo.induct s m with
  | case1 w a hw ih =>
    rw [xorGo, ite_eq_left hw, ih, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
  | case2 w a hw => rw [xorGo, ite_eq_right hw]

theorem xorGo_getD (s : Row) (m w : ℕ) (a : Row) (c : ℕ) :
    (xorGo s m w a).getD c 0 =
      if w ≤ c ∧ c < m ∧ c < a.size then a.getD c 0 ^^^ s.getD c 0 else a.getD c 0 := by
  induction w, a using xorGo.induct s m with
  | case1 w a hw ih =>
    rw [xorGo, ite_eq_left hw, ih, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds,
      getD_setIfInBounds]
    by_cases hcw : c = w
    · subst hcw
      by_cases hc : c < a.size <;> simp [hc, hw]
    · have : (w ≤ c ∧ c < m ∧ c < a.size) ↔ (w + 1 ≤ c ∧ c < m ∧ c < a.size) := by omega
      simp only [hcw, false_and, ite_false]
      by_cases h : w + 1 ≤ c ∧ c < m ∧ c < a.size
      · rw [ite_eq_left h, ite_eq_left (this.2 h)]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h (this.1 h'))]
  | case2 w a hw =>
    rw [xorGo, ite_eq_right hw]
    by_cases h : w ≤ c ∧ c < m ∧ c < a.size
    · omega
    · rw [ite_eq_right h]

theorem xorRow_size (m : ℕ) (a s : Row) : (xorRow m a s).size = a.size := xorGo_size _ _ _ _

theorem bitOf_xorRow {m : ℕ} {a : Row} (ha : a.size = m) (s : Row) {j : ℕ} (hj : j / 56 < m) :
    bitOf (xorRow m a s) j = (bitOf a j ^^ bitOf s j) := by
  unfold xorRow
  rw [bitOf_def, xorGo_getD, ite_eq_left ⟨Nat.zero_le _, hj, ha ▸ hj⟩, Nat.testBit_xor]
  rfl

theorem rowVec_xorRow {n : ℕ} {a : Row} (ha : a.size = nch n) (s : Row) :
    rowVec n (xorRow (nch n) a s) = rowVec n a + rowVec n s := by
  funext j
  simp only [rowVec, Pi.add_apply, bitOf_xorRow ha s (nch_spec j.2)]
  cases bitOf a j <;> cases bitOf s j <;> decide

theorem zeros_size (m : ℕ) : (zeros m).size = m := by simp [zeros]

theorem getD_zeros (m c : ℕ) : (zeros m).getD c 0 = 0 := by
  simp only [zeros, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split_ifs <;> rfl

theorem bitOf_zeros (m j : ℕ) : bitOf (zeros m) j = false := by
  rw [bitOf_def, getD_zeros, Nat.zero_testBit]

theorem rowVec_zeros (n m : ℕ) : rowVec n (zeros m) = 0 := by
  funext j
  simp [rowVec, bitOf_zeros]

@[expose] noncomputable def yv (n : ℕ) (Y : Mat) (j : ℕ) : Fin n → ZMod 2 := rowVec n (Y.getD j #[])

theorem rowVec_getD_zeros (n m : ℕ) (Y : Mat) (j : ℕ) :
    rowVec n (Y.getD j (zeros m)) = yv n Y j := by
  unfold yv
  simp only [Array.getD_eq_getD_getElem?]
  cases Y[j]? with
  | none => simp [rowVec_zeros, rowVec_empty]
  | some r => rfl

theorem rowVec_getElem?_getD_zeros (n m : ℕ) (Y : Mat) (j : ℕ) :
    rowVec n (Y[j]?.getD (zeros m)) = yv n Y j := by
  rw [← Array.getD_eq_getD_getElem?]
  exact rowVec_getD_zeros n m Y j

theorem testBit_sub_two_pow {c i₀ : ℕ} (h₁ : 2 ^ i₀ ≤ c) (h₂ : c < 2 ^ (i₀ + 1)) :
    c.testBit i₀ = true ∧ ∀ i < i₀, (c - 2 ^ i₀).testBit i = c.testBit i := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h₁
  have hd : d < 2 ^ i₀ := by rw [pow_succ] at h₂; omega
  refine ⟨?_, fun i hi => ?_⟩
  · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hd]
    rfl
  · rw [Nat.add_sub_cancel_left, Nat.testBit_two_pow_add_gt hi]

theorem testBit_of_lt_two_pow {c i₀ : ℕ} (h : c < 2 ^ i₀) : c.testBit i₀ = false :=
  Nat.testBit_lt_two_pow h

@[expose] def TabInv (n : ℕ) (Y : Mat) (k i₀ : ℕ) (t : Array Row) : Prop :=
  t.size = 2 ^ i₀ ∧ ∀ c < 2 ^ i₀, (t.getD c #[]).size = nch n ∧
    rowVec n (t.getD c #[]) = ∑ i ∈ range i₀, if c.testBit i then yv n Y (8 * k + i) else 0

theorem tabInv_zero (n : ℕ) (Y : Mat) (k : ℕ) : TabInv n Y k 0 #[zeros (nch n)] := by
  refine ⟨rfl, fun c hc => ?_⟩
  have hc0 : c = 0 := by simpa using hc
  subst hc0
  refine ⟨by simp [zeros_size], ?_⟩
  simp [rowVec_zeros]

theorem tabInv_dbl {n : ℕ} {Y : Mat} {k i₀ : ℕ} {t : Array Row} (ht : TabInv n Y k i₀ t) :
    TabInv n Y k (i₀ + 1) (dbl (nch n) (Y.getD (8 * k + i₀) (zeros (nch n))) t) := by
  obtain ⟨hsz, hent⟩ := ht
  refine ⟨by simp [dbl, hsz, pow_succ]; ring, fun c hc => ?_⟩
  simp only [dbl, Array.getD_eq_getD_getElem?, Array.getElem?_append,
    Array.getElem?_map, hsz]
  rw [Finset.sum_range_succ]
  by_cases hlt : c < 2 ^ i₀
  · rw [ite_eq_left hlt]
    have h := hent c hlt
    simp only [Array.getD_eq_getD_getElem?] at h
    refine ⟨h.1, ?_⟩
    rw [h.2, testBit_of_lt_two_pow hlt]
    simp
  · rw [ite_eq_right hlt]
    have hge : 2 ^ i₀ ≤ c := by omega
    obtain ⟨hb, hlow⟩ := testBit_sub_two_pow hge hc
    have hlt' : c - 2 ^ i₀ < 2 ^ i₀ := by rw [pow_succ] at hc; omega
    have h := hent (c - 2 ^ i₀) hlt'
    simp only [Array.getD_eq_getD_getElem?] at h
    have hget : t[c - 2 ^ i₀]? = some (t[c - 2 ^ i₀]?.getD #[]) := by
      rw [Array.getElem?_eq_getElem (by omega)]
      rfl
    rw [hget, Option.map_some, Option.getD_some]
    refine ⟨by rw [xorRow_size]; exact h.1, ?_⟩
    rw [rowVec_xorRow h.1, h.2, rowVec_getElem?_getD_zeros, hb, ite_eq_left rfl]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hlow i (Finset.mem_range.1 hi)]

theorem tabInv_foldl (n : ℕ) (Y : Mat) (k : ℕ) :
    ∀ i₀, TabInv n Y k i₀ ((List.range i₀).foldl
      (fun t i => dbl (nch n) (Y.getD (8 * k + i) (zeros (nch n))) t) #[zeros (nch n)])
  | 0 => tabInv_zero n Y k
  | i₀ + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact tabInv_dbl (tabInv_foldl n Y k i₀)

theorem blockTable_spec (n : ℕ) (Y : Mat) (k c : ℕ) (hc : c < 256) :
    ((blockTable (nch n) Y k).getD c #[]).size = nch n ∧
    rowVec n ((blockTable (nch n) Y k).getD c #[]) =
      ∑ i ∈ range 8, if c.testBit i then yv n Y (8 * k + i) else 0 :=
  (tabInv_foldl n Y k 8).2 c hc

theorem tableRange_getD (m : ℕ) (Y : Mat) (lo hi k : ℕ) :
    (tableRange m Y lo hi).getD k #[] = if k < hi - lo then blockTable m Y (lo + k) else #[] := by
  simp only [tableRange, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
  split_ifs <;> rfl

theorem tableRange_size (m : ℕ) (Y : Mat) (lo hi : ℕ) : (tableRange m Y lo hi).size = hi - lo := by
  simp [tableRange]

theorem tableRange_append (m : ℕ) (Y : Mat) {lo mid hi : ℕ} (h₁ : lo ≤ mid) (h₂ : mid ≤ hi) :
    tableRange m Y lo mid ++ tableRange m Y mid hi = tableRange m Y lo hi := by
  apply Array.ext
  · simp [tableRange_size]; omega
  · intro i hi₁ hi₂
    have e₁ := tableRange_getD m Y lo hi i
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi₂, Option.getD_some] at e₁
    rw [e₁, ite_eq_left (by rw [tableRange_size] at hi₂; exact hi₂)]
    rw [Array.getElem_append]
    split_ifs with hlt
    · have e₂ := tableRange_getD m Y lo mid i
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt, Option.getD_some] at e₂
      rw [e₂, ite_eq_left (by rw [tableRange_size] at hlt; exact hlt)]
    · have hlt' : i - (tableRange m Y lo mid).size < (tableRange m Y mid hi).size := by
        simp only [Array.size_append] at hi₁; omega
      have e₂ := tableRange_getD m Y mid hi (i - (tableRange m Y lo mid).size)
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt', Option.getD_some] at e₂
      rw [e₂, ite_eq_left (by rw [tableRange_size m Y mid hi] at hlt'; exact hlt')]
      congr 1
      rw [tableRange_size] at hlt ⊢
      omega

theorem tables_eq (m nb : ℕ) (Y : Mat) : tables m nb Y = tableRange m Y 0 nb := by
  unfold tables tableTasks
  rw [← Array.foldl_toList]
  change #[] ++ tableRange m Y 0 (min ((nb + 3) / 4) nb) ++
      tableRange m Y (min ((nb + 3) / 4) nb) (min (2 * ((nb + 3) / 4)) nb) ++
      tableRange m Y (min (2 * ((nb + 3) / 4)) nb) (min (3 * ((nb + 3) / 4)) nb) ++
      tableRange m Y (min (3 * ((nb + 3) / 4)) nb) nb = _
  rw [Array.empty_append, tableRange_append m Y (by omega) (by omega),
    tableRange_append m Y (by omega) (by omega), tableRange_append m Y (by omega) (by omega)]

theorem tables_getD (m nb : ℕ) (Y : Mat) {k : ℕ} (hk : k < nb) :
    (tables m nb Y).getD k #[] = blockTable m Y k := by
  rw [tables_eq, tableRange_getD, ite_eq_left (by omega), Nat.zero_add]

theorem testBit_byteOf (x : Row) (k : ℕ) {i : ℕ} (hi : i < 8) :
    (byteOf x k).testBit i = bitOf x (8 * k + i) := by
  unfold byteOf
  rw [bitOf_def, show (256 : ℕ) = 2 ^ 8 by norm_num, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight]
  have e₁ : (8 * k + i) / 56 = k / 7 := by omega
  have e₂ : (8 * k + i) % 56 = 8 * (k % 7) + i := by omega
  rw [e₁, e₂]
  simp [hi]

theorem byteOf_lt (x : Row) (k : ℕ) : byteOf x k < 256 := Nat.mod_lt _ (by norm_num)

theorem entry_spec (n : ℕ) (Y : Mat) (nb : ℕ) {k : ℕ} (hk : k < nb) (x : Row) :
    (((tables (nch n) nb Y).getD k #[]).getD (byteOf x k) #[]).size = nch n ∧
    rowVec n (((tables (nch n) nb Y).getD k #[]).getD (byteOf x k) #[]) =
      ∑ i ∈ range 8, if bitOf x (8 * k + i) then yv n Y (8 * k + i) else 0 := by
  rw [tables_getD _ _ _ hk]
  obtain ⟨h1, h2⟩ := blockTable_spec n Y k (byteOf x k) (byteOf_lt x k)
  refine ⟨h1, h2.trans (Finset.sum_congr rfl fun i hi => ?_)⟩
  rw [testBit_byteOf x k (Finset.mem_range.1 hi)]

theorem applyGo_spec (n : ℕ) (Y : Mat) (nb : ℕ) (x : Row) :
    ∀ d k (acc : Row), nb - k = d → acc.size = nch n →
      (applyGo (tables (nch n) nb Y) (nch n) nb x k acc).size = nch n ∧
      rowVec n (applyGo (tables (nch n) nb Y) (nch n) nb x k acc) = rowVec n acc +
        ∑ l ∈ Finset.Ico k nb, ∑ i ∈ range 8, if bitOf x (8 * l + i) then yv n Y (8 * l + i) else 0 := by
  intro d
  induction d with
  | zero =>
    intro k acc hd hacc
    rw [applyGo, ite_eq_right (by omega), Finset.Ico_eq_empty (by omega), Finset.sum_empty, add_zero]
    exact ⟨hacc, rfl⟩
  | succ d ih =>
    intro k acc hd hacc
    have hk : k < nb := by omega
    rw [applyGo, ite_eq_left hk]
    obtain ⟨he1, he2⟩ := entry_spec n Y nb hk x
    have hnext : (if byteOf x k = 0 then acc else xorRow (nch n) acc
          (((tables (nch n) nb Y).getD k #[]).getD (byteOf x k) #[])).size = nch n ∧
        rowVec n (if byteOf x k = 0 then acc else xorRow (nch n) acc
          (((tables (nch n) nb Y).getD k #[]).getD (byteOf x k) #[])) = rowVec n acc +
          ∑ i ∈ range 8, if bitOf x (8 * k + i) then yv n Y (8 * k + i) else 0 := by
      split_ifs with h0
      · refine ⟨hacc, ?_⟩
        rw [← he2, h0]
        have h00 := blockTable_spec n Y k 0 (by norm_num)
        rw [tables_getD _ _ _ hk, h00.2]
        simp
      · exact ⟨by rw [xorRow_size]; exact hacc, by rw [rowVec_xorRow hacc, he2]⟩
    obtain ⟨h1, h2⟩ := ih (k + 1) _ (by omega) hnext.1
    refine ⟨h1, ?_⟩
    rw [h2, hnext.2, add_assoc, Finset.sum_eq_sum_Ico_succ_bot hk]

theorem sum_range_blocks' {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k : ℕ) :
    ∀ n : ℕ, ∑ l ∈ range n, ∑ i ∈ range k, f (k * l + i) = ∑ j ∈ range (k * n), f j
  | 0 => by simp
  | n + 1 => by
    rw [sum_range_succ, sum_range_blocks' f k n, Nat.mul_succ, sum_range_add]

theorem rowVec_applyRow (n : ℕ) (Y : Mat) (hY : Y.size ≤ n) (x : Row) :
    (applyRow (tables (nch n) ((n + 7) / 8) Y) (nch n) ((n + 7) / 8) x).size = nch n ∧
    rowVec n (applyRow (tables (nch n) ((n + 7) / 8) Y) (nch n) ((n + 7) / 8) x) =
      rowVec n x ᵥ* cmat n Y := by
  obtain ⟨h1, h2⟩ := applyGo_spec n Y ((n + 7) / 8) x _ 0 (zeros (nch n)) rfl (zeros_size _)
  refine ⟨h1, ?_⟩
  unfold applyRow
  rw [h2, rowVec_zeros, zero_add, ← Finset.range_eq_Ico,
    sum_range_blocks' (fun j => if bitOf x j then yv n Y j else 0) 8]
  have htail : ∑ j ∈ range (8 * ((n + 7) / 8)), (if bitOf x j then yv n Y j else 0) =
      ∑ j ∈ range n, (if bitOf x j then yv n Y j else 0) := by
    obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (show n ≤ 8 * ((n + 7) / 8) by omega)
    rw [he, sum_range_add]
    have : ∑ j ∈ range e, (if bitOf x (n + j) then yv n Y (n + j) else 0) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      have : yv n Y (n + j) = 0 := by
        unfold yv
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none,
          rowVec_empty]
      simp [this]
    rw [this, add_zero]
  rw [htail]
  funext l
  rw [Finset.sum_apply, vecMul, dotProduct, ← Fin.sum_univ_eq_sum_range
    (fun j => (if bitOf x j then yv n Y j else 0) l)]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold yv
  rw [cmat_apply]
  by_cases hb : bitOf x j <;> simp [rowVec, hb]

theorem mapRange_eq (f : Row → Row) (X : Mat) (lo hi : ℕ) :
    mapRange f X lo hi = (X.extract lo hi).map f := rfl

theorem parMap_eq (f : Row → Row) (X : Mat) : parMap f X = X.map f := by
  unfold parMap parTasks
  rw [← Array.foldl_toList]
  change #[] ++ mapRange f X 0 ((X.size + 3) / 4) ++ mapRange f X ((X.size + 3) / 4) (2 * ((X.size + 3) / 4)) ++
      mapRange f X (2 * ((X.size + 3) / 4)) (3 * ((X.size + 3) / 4)) ++
      mapRange f X (3 * ((X.size + 3) / 4)) (4 * ((X.size + 3) / 4)) = _
  simp only [Array.empty_append, mapRange_eq, ← Array.map_append]
  congr 1
  have hcat : ∀ a b c : ℕ, a ≤ b → b ≤ c → X.extract a b ++ X.extract b c = X.extract a c := by
    intro a b c hab hbc
    rw [Array.extract_append_extract]
    congr 1 <;> omega
  rw [hcat _ _ _ (by omega) (by omega), hcat _ _ _ (by omega) (by omega),
    hcat _ _ _ (by omega) (by omega)]
  exact Array.extract_eq_self_of_le (by omega)

theorem mulP_eq (n : ℕ) (X Y : Mat) :
    mulP n X Y = X.map (applyRow (tables (nch n) ((n + 7) / 8) Y) (nch n) ((n + 7) / 8)) := by
  unfold mulP
  exact parMap_eq _ _

theorem mulP_size (n : ℕ) (X Y : Mat) : (mulP n X Y).size = X.size := by
  rw [mulP_eq, Array.size_map]

theorem cmat_mulP (n : ℕ) (X Y : Mat) (hY : Y.size ≤ n) :
    cmat n (mulP n X Y) = cmat n X * cmat n Y := by
  ext i j
  rw [mulP_eq, cmat_apply, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases hx : X[(i : ℕ)]? with
  | none =>
    simp only [Option.map_none, Option.getD_none, rowVec_empty, Pi.zero_apply]
    rw [Matrix.mul_apply]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    rw [cmat_apply, Array.getD_eq_getD_getElem?, hx, Option.getD_none, rowVec_empty]
    simp
  | some x =>
    simp only [Option.map_some, Option.getD_some]
    rw [(rowVec_applyRow n Y hY x).2]
    have hrow : rowVec n x = fun k => cmat n X i k := by
      funext k
      rw [cmat_apply, Array.getD_eq_getD_getElem?, hx, Option.getD_some]
    rw [hrow]
    rfl

theorem mulP_row_size (n : ℕ) (X Y : Mat) (hY : Y.size ≤ n) {i : ℕ} (hi : i < (mulP n X Y).size) :
    (mulP n X Y)[i].size = nch n := by
  simp only [mulP_eq, Array.getElem_map]
  exact (rowVec_applyRow n Y hY _).1

theorem getD_unitRow (n i c : ℕ) :
    (unitRow n i).getD c 0 = if c = i / 56 ∧ i / 56 < nch n then 2 ^ (i % 56) else 0 := by
  unfold unitRow
  rw [Array.set!_eq_setIfInBounds, getD_setIfInBounds, zeros_size, getD_zeros]

theorem bitOf_unitRow {n i : ℕ} (hi : i < n) (j : ℕ) : bitOf (unitRow n i) j = decide (j = i) := by
  rw [bitOf_def, getD_unitRow]
  have hi' := nch_spec hi
  by_cases hj : j / 56 = i / 56
  · rw [ite_eq_left ⟨hj, hi'⟩, Nat.testBit_two_pow]
    by_cases hji : j = i
    · subst hji; simp
    · have : i % 56 ≠ j % 56 := fun h => hji (by omega)
      simp [this, hji]
  · rw [ite_eq_right (fun h => hj h.1), Nat.zero_testBit]
    have : j ≠ i := fun h => hj (h ▸ rfl)
    simp [this]

theorem unitRow_size (n i : ℕ) : (unitRow n i).size = nch n := by
  simp [unitRow, zeros_size]

theorem idMat_size (n : ℕ) : (idMat n).size = n := by simp [idMat]

theorem idMat_getD {n i : ℕ} (hi : i < n) : (idMat n).getD i #[] = unitRow n i := by
  simp [idMat, Array.getD_eq_getD_getElem?, hi]

theorem cmat_idMat (n : ℕ) : cmat n (idMat n) = 1 := by
  ext i j
  rw [cmat_apply, idMat_getD i.2, rowVec, bitOf_unitRow i.2, Matrix.one_apply]
  by_cases h : j = i
  · subst h; simp
  · have h' : (j : ℕ) ≠ i := fun e => h (Fin.ext e)
    simp [h', Ne.symm h]

theorem powM_spec {n : ℕ} :
    ∀ (e : ℕ) {X : Mat}, X.size ≤ n → (powM n X e).size ≤ n ∧ cmat n (powM n X e) = cmat n X ^ e := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro X hX
    rw [powM]
    by_cases he : e = 0
    · rw [ite_eq_left he, he, pow_zero]
      exact ⟨(idMat_size n).le, cmat_idMat n⟩
    rw [ite_eq_right he]
    by_cases he1 : e = 1
    · rw [ite_eq_left he1, he1, pow_one]
      exact ⟨hX, rfl⟩
    rw [ite_eq_right he1]
    have hXX : (mulP n X X).size ≤ n := by rw [mulP_size]; exact hX
    obtain ⟨hY, hYm⟩ := ih (e / 2) (by omega) hXX
    rw [cmat_mulP n X X hX, ← sq, ← pow_mul] at hYm
    by_cases ho : e % 2 = 1
    · rw [ite_eq_left ho]
      refine ⟨by rw [mulP_size]; exact hX, ?_⟩
      rw [cmat_mulP n X _ hY, hYm, ← pow_succ']
      congr 1
      omega
    · rw [ite_eq_right ho]
      refine ⟨hY, ?_⟩
      rw [hYm]
      congr 1
      omega

theorem cmat_powM {n : ℕ} {X : Mat} (hX : X.size ≤ n) (e : ℕ) :
    cmat n (powM n X e) = cmat n X ^ e :=
  (powM_spec e hX).2

theorem powM_size {n : ℕ} {X : Mat} (hX : X.size ≤ n) (e : ℕ) : (powM n X e).size ≤ n :=
  (powM_spec e hX).1

theorem vecGo_spec (n : ℕ) (v : Row) (Y : Mat) :
    ∀ d i (acc : Row), n - i = d → acc.size = nch n →
      (vecGo n (nch n) v Y i acc).size = nch n ∧
      rowVec n (vecGo n (nch n) v Y i acc) =
        rowVec n acc + ∑ j ∈ Finset.Ico i n, if bitOf v j then yv n Y j else 0 := by
  intro d
  induction d with
  | zero =>
    intro i acc hd hacc
    rw [vecGo, ite_eq_right (by omega), Finset.Ico_eq_empty (by omega), Finset.sum_empty, add_zero]
    exact ⟨hacc, rfl⟩
  | succ d ih =>
    intro i acc hd hacc
    have hi : i < n := by omega
    rw [vecGo, ite_eq_left hi]
    have hnext : (if bitOf v i then xorRow (nch n) acc (Y.getD i #[]) else acc).size = nch n ∧
        rowVec n (if bitOf v i then xorRow (nch n) acc (Y.getD i #[]) else acc) =
          rowVec n acc + if bitOf v i then yv n Y i else 0 := by
      split_ifs with hb
      · exact ⟨by rw [xorRow_size]; exact hacc, by rw [rowVec_xorRow hacc]; rfl⟩
      · exact ⟨hacc, by rw [add_zero]⟩
    obtain ⟨h1, h2⟩ := ih (i + 1) _ (by omega) hnext.1
    refine ⟨h1, ?_⟩
    rw [h2, hnext.2, add_assoc, Finset.sum_eq_sum_Ico_succ_bot hi]

theorem rowVec_vecMulC (n : ℕ) (v : Row) (Y : Mat) :
    rowVec n (vecMulC n v Y) = rowVec n v ᵥ* cmat n Y := by
  obtain ⟨-, h⟩ := vecGo_spec n v Y _ 0 (zeros (nch n)) rfl (zeros_size _)
  unfold vecMulC
  rw [h, rowVec_zeros, zero_add, ← Finset.range_eq_Ico]
  funext l
  rw [Finset.sum_apply, vecMul, dotProduct, ← Fin.sum_univ_eq_sum_range
    (fun j => (if bitOf v j then yv n Y j else 0) l)]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold yv
  rw [cmat_apply]
  by_cases hb : bitOf v j <;> simp [rowVec, hb]

theorem vecMulC_size (n : ℕ) (v : Row) (Y : Mat) : (vecMulC n v Y).size = nch n :=
  (vecGo_spec n v Y _ 0 (zeros (nch n)) rfl (zeros_size _)).1

theorem cmat_addM {n : ℕ} {X : Mat} (hX : X.size = n) (hXr : ∀ r ∈ X, r.size = nch n) (Y : Mat) :
    cmat n (addM n X Y) = cmat n X + cmat n Y := by
  ext i j
  rw [Matrix.add_apply, cmat_apply, cmat_apply, cmat_apply]
  have hi : (i : ℕ) < X.size := hX ▸ i.2
  have e1 : (addM n X Y).getD i #[] = xorRow (nch n) X[(i : ℕ)] (Y.getD i #[]) := by
    simp [addM, Array.getD_eq_getD_getElem?, hi]
  have e2 : X.getD i #[] = X[(i : ℕ)] := by
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
  rw [e1, e2, rowVec_xorRow (hXr _ (Array.getElem_mem hi))]
  rfl

theorem diagM_getD {n r i : ℕ} (hi : i < n) :
    (diagM n r).getD i #[] = if i < r then unitRow n i else zeros (nch n) := by
  simp [diagM, Array.getD_eq_getD_getElem?, hi]

theorem cmat_diagM (n r : ℕ) :
    cmat n (diagM n r) = Matrix.diagonal fun i : Fin n => if (i : ℕ) < r then 1 else 0 := by
  ext i j
  rw [cmat_apply, diagM_getD i.2, Matrix.diagonal_apply]
  by_cases hr : (i : ℕ) < r
  · rw [ite_eq_left hr, ite_eq_left hr, rowVec, bitOf_unitRow i.2]
    by_cases h : i = j
    · subst h; simp
    · have h' : (j : ℕ) ≠ i := fun e => h (Fin.ext e).symm
      simp [h', h]
  · rw [ite_eq_right hr, ite_eq_right hr, rowVec_zeros]
    simp

theorem cmat_eq_of_beq {n : ℕ} {X Y : Mat} (h : (X == Y) = true) : cmat n X = cmat n Y := by
  rw [eq_of_beq h]

theorem testBit_orFold (byte : ℕ → ℕ) (hb : ∀ t, byte t < 256) :
    ∀ (t₀ p : ℕ), ((List.range t₀).foldl (fun acc t => acc ||| (byte t <<< (8 * t))) 0).testBit p =
      (decide (p / 8 < t₀) && (byte (p / 8)).testBit (p % 8))
  | 0, p => by simp
  | t₀ + 1, p => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.testBit_or,
      testBit_orFold byte hb t₀ p, Nat.testBit_shiftLeft]
    by_cases h1 : p / 8 < t₀
    · have : ¬ (8 * t₀ ≤ p) := by omega
      simp [h1, show p / 8 < t₀ + 1 by omega, this]
    · by_cases h2 : p / 8 = t₀
      · have e : p - 8 * t₀ = p % 8 := by omega
        simp [h2, e, show 8 * t₀ ≤ p by omega]
      · have h3 : 8 ≤ p - 8 * t₀ := by omega
        have : (byte t₀).testBit (p - 8 * t₀) = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le (hb t₀)
            (by calc 256 = 2 ^ 8 := by norm_num
              _ ≤ 2 ^ (p - 8 * t₀) := Nat.pow_le_pow_right (by norm_num) h3))
        simp [h1, show ¬ p / 8 < t₀ + 1 by omega, this]

theorem byte_toNat_lt (b : UInt8) : b.toNat < 256 := b.toNat_lt

theorem bitOf_rowOfBytes {n : ℕ} (hn : n ≤ 4416) (b : ByteArray) (o : ℕ) {j : ℕ} (hj : j < n) :
    bitOf (rowOfBytes n b o) j = (b.get! (o + j / 8)).toNat.testBit (j % 8) := by
  rw [bitOf_def]
  have hw := nch_spec hj
  have e1 : (rowOfBytes n b o).getD (j / 56) 0 = chunkOfBytes n b o (j / 56) := by
    simp [rowOfBytes, Array.getD_eq_getD_getElem?, hw]
  rw [e1, chunkOfBytes, Nat.testBit_mod_two_pow]
  have hlt : j % 56 < min 56 (n - 56 * (j / 56)) := by omega
  rw [decide_eq_true hlt, Bool.true_and]
  rw [testBit_orFold (fun t => if 7 * (j / 56) + t < 552 then (b.get! (o + 7 * (j / 56) + t)).toNat
      else 0) (fun t => by split_ifs <;> [exact byte_toNat_lt _; norm_num]) 7 (j % 56)]
  have h7 : j % 56 / 8 < 7 := by omega
  have e2 : 7 * (j / 56) + j % 56 / 8 = j / 8 := by omega
  have e3 : j % 56 % 8 = j % 8 := by omega
  have h552 : j / 8 < 552 := by omega
  simp only [h7, decide_true, Bool.true_and, e2, e3, h552, ite_true]
  rw [Nat.add_assoc, e2]

theorem cmat_matOfPayload {n : ℕ} (hn : n ≤ 4416) (P : ByteArray) (idx : ℕ) (i j : Fin n) :
    cmat n (matOfPayload n P idx) i j =
      if (P.get! (16 + 552 * (n * idx + i) + j / 8)).toNat.testBit (j % 8) then 1 else 0 := by
  rw [cmat_apply]
  have e : (matOfPayload n P idx).getD i #[] = rowOfBytes n P (16 + 552 * (n * idx + i)) := by
    simp [matOfPayload, Array.getD_eq_getD_getElem?, i.2]
  rw [e, rowVec, bitOf_rowOfBytes hn _ _ j.2]

theorem matOfPayload_size (n : ℕ) (P : ByteArray) (idx : ℕ) : (matOfPayload n P idx).size = n := by
  simp [matOfPayload]

theorem matOfPayload_row_size (n : ℕ) (P : ByteArray) (idx : ℕ) :
    ∀ r ∈ matOfPayload n P idx, r.size = nch n := by
  intro r hr
  simp only [matOfPayload, Array.mem_ofFn] at hr
  obtain ⟨k, rfl⟩ := hr
  simp [rowOfBytes]

theorem testBit_byteOfRow (x : Row) (j : ℕ) :
    (byteOfRow x (j / 8)).toNat.testBit (j % 8) = bitOf x j := by
  unfold byteOfRow
  rw [UInt8.toNat_ofNat_of_lt' (lt_of_lt_of_le (byteOf_lt x _) (by decide)),
    testBit_byteOf x _ (Nat.mod_lt _ (by norm_num))]
  congr 1
  omega

theorem get!_mk_ofFn {N : ℕ} (f : Fin N → UInt8) {i : ℕ} (hi : i < N) :
    (ByteArray.mk (Array.ofFn f)).get! i = f ⟨i, hi⟩ := by
  show (Array.ofFn f)[i]! = f ⟨i, hi⟩
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

theorem payload_bit (n : ℕ) (Ms : Array Mat) {g k j : ℕ} (hg : g < Ms.size) (hk : k < n)
    (hj : j < 4416) :
    ((payload n Ms).get! (16 + 552 * (n * g + k) + j / 8)).toNat.testBit (j % 8) =
      bitOf ((Ms.getD g #[]).getD k #[]) j := by
  have hpos : 16 + 552 * (n * g + k) + j / 8 < 16 + Ms.size * n * 552 := by
    have h1 : n * g + k < n * Ms.size := by
      calc n * g + k < n * g + n := by omega
        _ = n * (g + 1) := by ring
        _ ≤ n * Ms.size := Nat.mul_le_mul_left _ hg
    have h2 : j / 8 < 552 := by omega
    have h3 : 552 * (n * g + k + 1) ≤ 552 * (n * Ms.size) := Nat.mul_le_mul_left _ h1
    have h4 : Ms.size * n * 552 = 552 * (n * Ms.size) := by ring
    omega
  have hget : (payload n Ms).get! (16 + 552 * (n * g + k) + j / 8) =
      byteOfRow ((Ms.getD g #[]).getD k #[]) (j / 8) := by
    unfold payload
    rw [get!_mk_ofFn _ hpos]
    simp only
    rw [ite_eq_right (by omega)]
    have e1 : (16 + 552 * (n * g + k) + j / 8 - 16) / 552 = n * g + k := by omega
    have e2 : (16 + 552 * (n * g + k) + j / 8 - 16) % 552 = j / 8 := by omega
    have hn : 0 < n := by omega
    have e3 : (n * g + k) / n = g := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hk, Nat.zero_add]
    have e4 : (n * g + k) % n = k := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
    rw [e1, e2, e3, e4]
  rw [hget, testBit_byteOfRow]

theorem bitOf_chunksOfNat {n : ℕ} (x : ℕ) {j : ℕ} (hj : j < n) :
    bitOf (chunksOfNat (nch n) x) j = x.testBit j := by
  rw [bitOf_def]
  have hw := nch_spec hj
  have e : (chunksOfNat (nch n) x).getD (j / 56) 0 = (x >>> (56 * (j / 56))) % 2 ^ 56 := by
    simp [chunksOfNat, Array.getD_eq_getD_getElem?, hw]
  rw [e, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  have : 56 * (j / 56) + j % 56 = j := by omega
  simp [Nat.mod_lt j (by norm_num : 56 > 0), this]

theorem cmat_matOfRows (n : ℕ) (X : Array ℕ) (i j : Fin n) :
    cmat n (matOfRows n X) i j = if (X[(i : ℕ)]?.getD 0).testBit j then 1 else 0 := by
  rw [cmat_apply]
  simp only [matOfRows, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases X[(i : ℕ)]? with
  | none => simp [rowVec_empty]
  | some x => simp [rowVec, bitOf_chunksOfNat x j.2]

theorem matOfRows_size (n : ℕ) (X : Array ℕ) : (matOfRows n X).size = X.size := by
  simp [matOfRows]

theorem matOfRows_row_size (n : ℕ) (X : Array ℕ) : ∀ r ∈ matOfRows n X, r.size = nch n := by
  intro r hr
  simp only [matOfRows, Array.mem_map] at hr
  obtain ⟨x, -, rfl⟩ := hr
  simp [chunksOfNat]

theorem cmat_ne_of_neM {n : ℕ} {X Y : Mat} (h : neM n X Y = true) : cmat n X ≠ cmat n Y := by
  unfold neM at h
  rw [List.any_eq_true] at h
  obtain ⟨i, hi, hrow⟩ := h
  unfold rowNe at hrow
  rw [List.any_eq_true] at hrow
  obtain ⟨j, hj, hb⟩ := hrow
  rw [List.mem_range] at hi hj
  intro heq
  have := congrFun (congrFun heq ⟨i, hi⟩) ⟨j, hj⟩
  rw [cmat_apply, cmat_apply] at this
  simp only [rowVec] at this
  revert hb this
  cases bitOf (X.getD i #[]) j <;> cases bitOf (Y.getD i #[]) j <;> decide

theorem swapAt_size (X : Mat) (i j : ℕ) : (swapAt X i j).size = X.size := by
  unfold swapAt
  split_ifs <;> simp

theorem clearCol_size (m n r c : ℕ) (pl pr : Row) :
    ∀ (i : ℕ) (L R : Mat), (clearCol m n r c pl pr i L R).1.size = L.size ∧
      (clearCol m n r c pl pr i L R).2.size = R.size := by
  intro i L R
  induction i, L, R using clearCol.induct m n r c pl pr with
  | case1 i L R hi hb ih => rw [clearCol, ite_eq_left hi, ite_eq_left hb]; simpa using ih
  | case2 i L R hi hb ih => rw [clearCol, ite_eq_left hi, ite_eq_right hb]; exact ih
  | case3 i L R hi => rw [clearCol, ite_eq_right hi]; exact ⟨rfl, rfl⟩

theorem gjGo_size (m n : ℕ) :
    ∀ (c r : ℕ) (L R : Mat) (piv : Array ℕ), (gjGo m n c r L R piv).2.1.size = R.size := by
  intro c r L R piv
  induction c, r, L, R, piv using gjGo.induct m n with
  | case1 c r L R piv hc p hp L' R' pl pr LR ih =>
    rw [gjGo, ite_eq_left hc]
    simp only
    rw [ite_eq_left hp, ih, (clearCol_size _ _ _ _ _ _ _ _ _).2, swapAt_size]
  | case2 c r L R piv hc p hp ih =>
    rw [gjGo, ite_eq_left hc]
    simp only
    rw [ite_eq_right hp, ih]
  | case3 c r L R piv hc => rw [gjGo, ite_eq_right hc]

theorem invM_size (n : ℕ) (X : Mat) : (invM n X).size = n := by
  rw [invM, gjGo_size, idMat_size]

end CFSG.Monster.B.Bin

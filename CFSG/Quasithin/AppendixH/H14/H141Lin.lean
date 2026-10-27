module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.LawfulXor.Basic
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.AppendixH.H14

@[expose] def col (st i : ℕ) : ℕ := (st >>> (6 * i)) % 64

@[expose] def packSt (a b c d e f : ℕ) : ℕ :=
  a + 64 * (b + 64 * (c + 64 * (d + 64 * (e + 64 * f))))

@[expose] def idSt : ℕ := packSt 1 2 4 8 16 32

@[expose] def linAct (M n : ℕ) : ℕ :=
  (if n.testBit 0 then col M 0 else 0) ^^^ (if n.testBit 1 then col M 1 else 0) ^^^
    (if n.testBit 2 then col M 2 else 0) ^^^ (if n.testBit 3 then col M 3 else 0) ^^^
    (if n.testBit 4 then col M 4 else 0) ^^^ (if n.testBit 5 then col M 5 else 0)

@[expose] def compSt (M st : ℕ) : ℕ :=
  packSt (linAct M (col st 0)) (linAct M (col st 1)) (linAct M (col st 2))
    (linAct M (col st 3)) (linAct M (col st 4)) (linAct M (col st 5))

theorem col_lt (st i : ℕ) : col st i < 64 := by
  exact Nat.mod_lt _ (by norm_num)

theorem linAct_lt (M n : ℕ) : linAct M n < 64 := by
  have key : ∀ i, (if n.testBit i then col M i else 0) < 2 ^ 6 := by
    intro i
    split
    · have := col_lt M i; omega
    · norm_num
  have h := Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow
    (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (key 0) (key 1)) (key 2)) (key 3)) (key 4))
    (key 5)
  have : (2 : ℕ) ^ 6 = 64 := by norm_num
  rw [this] at h
  simpa only [linAct] using h

theorem packSt_lt {a b c d e f : ℕ} (ha : a < 64) (hb : b < 64) (hc : c < 64) (hd : d < 64)
    (he : e < 64) (hf : f < 64) : packSt a b c d e f < 2 ^ 36 := by
  simp only [packSt]
  omega

theorem col_packSt {a b c d e f : ℕ} (ha : a < 64) (hb : b < 64) (hc : c < 64) (hd : d < 64)
    (he : e < 64) (hf : f < 64) :
    col (packSt a b c d e f) 0 = a ∧ col (packSt a b c d e f) 1 = b ∧
      col (packSt a b c d e f) 2 = c ∧ col (packSt a b c d e f) 3 = d ∧
      col (packSt a b c d e f) 4 = e ∧ col (packSt a b c d e f) 5 = f := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [col, packSt, Nat.shiftRight_eq_div_pow]; norm_num; omega)

theorem st_eq_packSt {st : ℕ} (h : st < 2 ^ 36) :
    st = packSt (col st 0) (col st 1) (col st 2) (col st 3) (col st 4) (col st 5) := by
  simp only [col, packSt, Nat.shiftRight_eq_div_pow]
  norm_num
  omega

theorem eq_of_col_eq {st st' : ℕ} (h : st < 2 ^ 36) (h' : st' < 2 ^ 36)
    (hc : ∀ i < 6, col st i = col st' i) : st = st' := by
  rw [st_eq_packSt h, st_eq_packSt h']
  rw [hc 0 (by norm_num), hc 1 (by norm_num), hc 2 (by norm_num), hc 3 (by norm_num),
    hc 4 (by norm_num), hc 5 (by norm_num)]

theorem compSt_lt (M st : ℕ) : compSt M st < 2 ^ 36 := by
  simpa only [compSt] using
    packSt_lt (linAct_lt M (col st 0)) (linAct_lt M (col st 1)) (linAct_lt M (col st 2))
      (linAct_lt M (col st 3)) (linAct_lt M (col st 4)) (linAct_lt M (col st 5))

theorem col_compSt (M st : ℕ) {i : ℕ} (hi : i < 6) : col (compSt M st) i = linAct M (col st i) := by
  have h := col_packSt (linAct_lt M (col st 0)) (linAct_lt M (col st 1)) (linAct_lt M (col st 2))
    (linAct_lt M (col st 3)) (linAct_lt M (col st 4)) (linAct_lt M (col st 5))
  simp only [compSt]
  interval_cases i <;>
    first
    | exact h.1
    | exact h.2.1
    | exact h.2.2.1
    | exact h.2.2.2.1
    | exact h.2.2.2.2.1
    | exact h.2.2.2.2.2

theorem if_bool_xor (b c : Bool) (x : ℕ) :
    (if (b ^^ c) then x else 0) = (if b then x else 0) ^^^ (if c then x else 0) := by
  cases b <;> cases c <;> simp

theorem linAct_xor (M n m : ℕ) : linAct M (n ^^^ m) = linAct M n ^^^ linAct M m := by
  simp only [linAct, Nat.testBit_xor, if_bool_xor]
  ac_rfl

theorem linAct_zero (M : ℕ) : linAct M 0 = 0 := by
  simp [linAct]

theorem linAct_if (M x : ℕ) (b : Bool) :
    linAct M (if b then x else 0) = if b then linAct M x else 0 := by
  cases b <;> simp [linAct]

theorem linAct_two_pow (M : ℕ) {i : ℕ} (hi : i < 6) : linAct M (2 ^ i) = col M i := by
  have h0 : (2 ^ i).testBit 0 = decide (i = 0) := Nat.testBit_two_pow
  have h1 : (2 ^ i).testBit 1 = decide (i = 1) := Nat.testBit_two_pow
  have h2 : (2 ^ i).testBit 2 = decide (i = 2) := Nat.testBit_two_pow
  have h3 : (2 ^ i).testBit 3 = decide (i = 3) := Nat.testBit_two_pow
  have h4 : (2 ^ i).testBit 4 = decide (i = 4) := Nat.testBit_two_pow
  have h5 : (2 ^ i).testBit 5 = decide (i = 5) := Nat.testBit_two_pow
  simp only [linAct, h0, h1, h2, h3, h4, h5, decide_eq_true_eq]
  interval_cases i <;> simp

theorem linAct_idSt {n : ℕ} (hn : n < 64) : linAct idSt n = n := by
  have h : ∀ m : Fin 64, linAct idSt (m : ℕ) = (m : ℕ) := by decide
  exact h ⟨n, hn⟩

theorem linAct_compSt (M st n : ℕ) : linAct (compSt M st) n = linAct M (linAct st n) := by
  have h0 : col (compSt M st) 0 = linAct M (col st 0) := col_compSt M st (by norm_num)
  have h1 : col (compSt M st) 1 = linAct M (col st 1) := col_compSt M st (by norm_num)
  have h2 : col (compSt M st) 2 = linAct M (col st 2) := col_compSt M st (by norm_num)
  have h3 : col (compSt M st) 3 = linAct M (col st 3) := col_compSt M st (by norm_num)
  have h4 : col (compSt M st) 4 = linAct M (col st 4) := col_compSt M st (by norm_num)
  have h5 : col (compSt M st) 5 = linAct M (col st 5) := col_compSt M st (by norm_num)
  conv_lhs => simp only [linAct]
  conv_lhs => rw [h0, h1, h2, h3, h4, h5]
  conv_lhs => simp only [← linAct_if]
  conv_lhs => simp only [← linAct_xor]
  rfl

inductive StReach (gm : List ℕ) : ℕ → Prop
  | base : StReach gm idSt
  | step {j s : ℕ} : j < gm.length → StReach gm s → StReach gm (compSt (gm.getD j 0) s)

theorem StReach.lt {gm : List ℕ} {st : ℕ} (h : StReach gm st) : st < 2 ^ 36 := by
  induction h with
  | base => norm_num [idSt, packSt]
  | step hj hs ih => exact compSt_lt _ _

inductive Trie : Type
  | nil : Trie
  | node (m : Bool) (l r : Trie) : Trie

@[expose] def Trie.mem : ℕ → Trie → ℕ → Bool
  | 0, .node m _ _, _ => m
  | 0, .nil, _ => false
  | d + 1, .node _ l r, k => if k % 2 = 0 then Trie.mem d l (k / 2) else Trie.mem d r (k / 2)
  | _ + 1, .nil, _ => false

@[expose] def Trie.ins : ℕ → Trie → ℕ → Trie
  | 0, _, _ => .node true .nil .nil
  | d + 1, .nil, k =>
      if k % 2 = 0 then .node false (Trie.ins d .nil (k / 2)) .nil
      else .node false .nil (Trie.ins d .nil (k / 2))
  | d + 1, .node m l r, k =>
      if k % 2 = 0 then .node m (Trie.ins d l (k / 2)) r else .node m l (Trie.ins d r (k / 2))

theorem Trie.mem_nil (d x : ℕ) : Trie.mem d Trie.nil x = false := by
  cases d <;> rfl

theorem Trie.mem_ins {d : ℕ} (t : Trie) {k x : ℕ} (hk : k < 2 ^ d) (hx : x < 2 ^ d) :
    Trie.mem d (Trie.ins d t k) x = (decide (x = k) || Trie.mem d t x) := by
  induction d generalizing t k x with
  | zero =>
      rw [pow_zero] at hk hx
      rw [Nat.lt_one_iff] at hk hx
      subst hk; subst hx
      cases t <;> rfl
  | succ d ih =>
      have hk2 : k / 2 < 2 ^ d := by
        have h2 : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
        omega
      have hx2 : x / 2 < 2 ^ d := by
        have h2 : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
        omega
      cases t with
      | nil =>
        rcases Nat.mod_two_eq_zero_or_one k with hk0 | hk1 <;>
          rcases Nat.mod_two_eq_zero_or_one x with hx0 | hx1
        ·
          simp only [Trie.ins]
          simp only [if_pos hk0]
          simp only [Trie.mem]
          simp only [if_pos hx0]
          rw [ih Trie.nil hk2 hx2]
          simp only [Trie.mem_nil, Bool.or_false]
          have hiff : x / 2 = k / 2 ↔ x = k := by omega
          simp only [hiff]
        ·
          have hne : x ≠ k := by omega
          have hxne : ¬(x % 2 = 0) := by omega
          simp only [Trie.ins]
          simp only [if_pos hk0]
          simp only [Trie.mem]
          simp only [if_neg hxne]
          simp only [Trie.mem_nil, Bool.or_false]
          rw [decide_eq_false_iff_not.mpr hne]
        ·
          have hne : x ≠ k := by omega
          have hkne : ¬(k % 2 = 0) := by omega
          simp only [Trie.ins]
          simp only [if_neg hkne]
          simp only [Trie.mem]
          simp only [if_pos hx0]
          simp only [Trie.mem_nil, Bool.or_false]
          rw [decide_eq_false_iff_not.mpr hne]
        ·
          have hkne : ¬(k % 2 = 0) := by omega
          have hxne : ¬(x % 2 = 0) := by omega
          simp only [Trie.ins]
          simp only [if_neg hkne]
          simp only [Trie.mem]
          simp only [if_neg hxne]
          rw [ih Trie.nil hk2 hx2]
          simp only [Trie.mem_nil, Bool.or_false]
          have hiff : x / 2 = k / 2 ↔ x = k := by omega
          simp only [hiff]
      | node m l r =>
        rcases Nat.mod_two_eq_zero_or_one k with hk0 | hk1 <;>
          rcases Nat.mod_two_eq_zero_or_one x with hx0 | hx1
        ·
          simp only [Trie.ins]
          simp only [if_pos hk0]
          simp only [Trie.mem]
          simp only [if_pos hx0]
          rw [ih l hk2 hx2]
          have hiff : x / 2 = k / 2 ↔ x = k := by omega
          simp only [hiff]
        ·
          have hne : x ≠ k := by omega
          have hxne : ¬(x % 2 = 0) := by omega
          simp only [Trie.ins]
          simp only [if_pos hk0]
          simp only [Trie.mem]
          simp only [if_neg hxne]
          rw [decide_eq_false_iff_not.mpr hne]
          simp only [Bool.false_or]
        ·
          have hne : x ≠ k := by omega
          have hkne : ¬(k % 2 = 0) := by omega
          simp only [Trie.ins]
          simp only [if_neg hkne]
          simp only [Trie.mem]
          simp only [if_pos hx0]
          rw [decide_eq_false_iff_not.mpr hne]
          simp only [Bool.false_or]
        ·
          have hkne : ¬(k % 2 = 0) := by omega
          have hxne : ¬(x % 2 = 0) := by omega
          simp only [Trie.ins]
          simp only [if_neg hkne]
          simp only [Trie.mem]
          simp only [if_neg hxne]
          rw [ih r hk2 hx2]
          have hiff : x / 2 = k / 2 ↔ x = k := by omega
          simp only [hiff]

def SbfsInv (gm : List ℕ) (t : Trie) (A : List ℕ) : Prop :=
  A.Nodup ∧ (∀ x ∈ A, StReach gm x) ∧ (∀ x ∈ A, x < 2 ^ 36) ∧
    ∀ x < 2 ^ 36, Trie.mem 36 t x = decide (x ∈ A)

@[expose] def sbfsGo (gm : List ℕ) : Trie → List (ℕ × ℕ × ℕ) → Bool
  | _, [] => true
  | t, (st, j, p) :: l =>
      decide (j < gm.length) && decide (st < 2 ^ 36) && decide (p < 2 ^ 36) &&
        Trie.mem 36 t p && (st == compSt (gm.getD j 0) p) && !(Trie.mem 36 t st) &&
        sbfsGo gm (Trie.ins 36 t st) l

theorem sbfsGo_sound {gm : List ℕ} {t : Trie} {A : List ℕ} {L : List (ℕ × ℕ × ℕ)}
    (h : sbfsGo gm t L = true) (hI : SbfsInv gm t A) :
    (A ++ L.map Prod.fst).Nodup ∧ ∀ e ∈ L, StReach gm e.1 := by
  induction L generalizing t A with
  | nil =>
      refine ⟨?_, ?_⟩
      · simpa using hI.1
      · intro e he; simp at he
  | cons e l ih =>
      obtain ⟨st, j, p⟩ := e
      simp only [sbfsGo, Bool.and_eq_true, and_assoc, decide_eq_true_eq, beq_iff_eq,
        Bool.not_eq_true', true_and] at h
      obtain ⟨hj, hst_lt, hp_lt, htp, hstp, hnot, hgo⟩ := h
      have hpA : p ∈ A := by
        have hp := hI.2.2.2 p hp_lt
        rw [hp] at htp
        exact of_decide_eq_true htp
      have hpreach : StReach gm p := hI.2.1 p hpA
      have hstreach : StReach gm st := by
        rw [hstp]
        exact StReach.step hj hpreach
      have hstA : st ∉ A := by
        have hs := hI.2.2.2 st hst_lt
        rw [hs] at hnot
        intro hmem
        simpa [hmem] using hnot
      have hI' : SbfsInv gm (Trie.ins 36 t st) (A ++ [st]) := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [List.nodup_append]
          refine ⟨hI.1, List.nodup_singleton st, ?_⟩
          intro a ha b hb
          simp only [List.mem_singleton] at hb
          subst hb
          intro hab
          exact hstA (hab ▸ ha)
        · intro x hx
          rw [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact hI.2.1 x hx
          · exact hstreach
        · intro x hx
          rw [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact hI.2.2.1 x hx
          · exact hst_lt
        · intro x hx
          rw [Trie.mem_ins t hst_lt hx, hI.2.2.2 x hx]
          by_cases hxk : x = st <;> simp [hxk, List.mem_append, List.mem_singleton]
      obtain ⟨hnd, hreach⟩ := ih (t := Trie.ins 36 t st) (A := A ++ [st]) hgo hI'
      refine ⟨?_, ?_⟩
      · simpa [List.append_assoc] using hnd
      · intro e he
        rcases List.mem_cons.mp he with rfl | hel
        · exact hstreach
        · exact hreach e hel

@[expose] def sbfsOK (gm : List ℕ) (L : List (ℕ × ℕ × ℕ)) : Bool :=
  match L with
  | [] => false
  | (st, _, _) :: l => (st == idSt) && sbfsGo gm (Trie.ins 36 .nil idSt) l

theorem sbfsOK_sound {gm : List ℕ} {L : List (ℕ × ℕ × ℕ)} (h : sbfsOK gm L = true) :
    (L.map Prod.fst).head? = some idSt ∧ (L.map Prod.fst).Nodup ∧
      ∀ e ∈ L, StReach gm e.1 := by
  cases L with
  | nil => simp [sbfsOK] at h
  | cons e l =>
      obtain ⟨st, j, p⟩ := e
      simp only [sbfsOK, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hst, hgo⟩ := h
      have hid : idSt < 2 ^ 36 := by norm_num [idSt, packSt]
      have hI : SbfsInv gm (Trie.ins 36 Trie.nil idSt) [idSt] := by
        refine ⟨List.nodup_singleton _, ?_, ?_, ?_⟩
        · intro x hx
          rw [List.mem_singleton] at hx
          exact hx ▸ StReach.base
        · intro x hx
          rw [List.mem_singleton] at hx
          exact hx ▸ hid
        · intro x hx
          rw [Trie.mem_ins Trie.nil hid hx, Trie.mem_nil]
          by_cases hxid : x = idSt <;> simp [hxid, List.mem_singleton]
      obtain ⟨hnd, hreach⟩ := sbfsGo_sound hgo hI
      refine ⟨?_, ?_, ?_⟩
      · simp [hst]
      · simpa [hst] using hnd
      · intro e he
        rcases List.mem_cons.mp he with rfl | hel
        · rw [hst]; exact StReach.base
        · exact hreach e hel

end CFSG.Quasithin.AppendixH.H14

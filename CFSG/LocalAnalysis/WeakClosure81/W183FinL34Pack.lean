module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsWords

public section

namespace CFSG.LocalAnalysis.WeakClosure81.W183L34

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts

@[expose] def getN (p i : Nat) : Nat := (p >>> (6 * i)) &&& 63

@[expose] def compN (p q : Nat) : Nat :=
  (List.range 42).foldl (fun acc i => acc ||| ((getN p (getN q i)) <<< (6 * i))) 0

private theorem testBit_getN (p i k : Nat) :
    (getN p i).testBit k = (decide (k < 6) && p.testBit (6 * i + k)) := by
  unfold getN
  rw [Nat.testBit_and, Nat.testBit_shiftRight]
  have h63 : (63 : Nat).testBit k = decide (k < 6) := by
    have := Nat.testBit_two_pow_sub_one 6 k
    simpa using this
  rw [h63]
  simp [Bool.and_comm]

private theorem testBit_foldl (f : Nat → Nat) (l : List Nat) (acc m : Nat) :
    (l.foldl (fun a j => a ||| f j) acc).testBit m =
      (acc.testBit m || l.any (fun j => (f j).testBit m)) := by
  induction l generalizing acc with
  | nil => simp
  | cons j l ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, List.any_cons]
    cases acc.testBit m <;> cases (f j).testBit m <;> simp

private theorem testBit_term (p q j m : Nat) :
    ((getN p (getN q j)) <<< (6 * j)).testBit m =
      (decide (6 * j ≤ m) &&
        (decide (m - 6 * j < 6) && p.testBit (6 * getN q j + (m - 6 * j)))) := by
  rw [Nat.testBit_shiftLeft, testBit_getN]

theorem getN_compN (p q i : Nat) (hi : i < 42) : getN (compN p q) i = getN p (getN q i) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_getN, testBit_getN]
  by_cases hk : k < 6
  · simp only [hk, decide_true, Bool.true_and]
    unfold compN
    rw [testBit_foldl]
    simp only [testBit_term, Nat.zero_testBit, Bool.false_or]
    cases hb : p.testBit (6 * getN q i + k)
    · simp only [List.any_eq_false, List.mem_range]
      intro j hj
      by_cases hji : j = i
      · subst hji
        have : 6 * j + k - 6 * j = k := by omega
        simp [this, hk, hb]
      · have h1 : ¬ (6 * j ≤ 6 * i + k ∧ 6 * i + k - 6 * j < 6) := by omega
        by_cases h2 : 6 * j ≤ 6 * i + k
        · have h3 : ¬ (6 * i + k - 6 * j < 6) := fun h => h1 ⟨h2, h⟩
          simp [h3]
        · simp [h2]
    · simp only [List.any_eq_true, List.mem_range]
      refine ⟨i, hi, ?_⟩
      have : 6 * i + k - 6 * i = k := by omega
      simp [this, hk, hb]
  · simp [hk]


@[expose] def idN : Nat := (List.range 42).foldl (fun acc i => acc ||| (i <<< (6 * i))) 0

@[expose] def eqN (p q : Nat) : Bool := (List.range 42).all fun i => getN p i == getN q i

theorem eqN_iff {p q : Nat} : eqN p q = true ↔ ∀ i < 42, getN p i = getN q i := by
  simp [eqN, List.all_eq_true, List.mem_range]

@[expose] def RepN (p : Nat) (g : Equiv.Perm (Fin 42)) : Prop :=
  ∀ i : Fin 42, getN p i = (g i : Nat)

theorem RepN.comp {p q : Nat} {g h : Equiv.Perm (Fin 42)} (hp : RepN p g) (hq : RepN q h) :
    RepN (compN p q) (g * h) := by
  intro i
  rw [getN_compN p q i i.2, hq i]
  exact hp (h i)

theorem RepN.eq_iff {p q : Nat} {g h : Equiv.Perm (Fin 42)} (hp : RepN p g) (hq : RepN q h) :
    eqN p q = true ↔ g = h := by
  rw [eqN_iff]
  constructor
  · intro H
    ext i
    have := H i i.2
    rw [hp i, hq i] at this
    exact this
  · rintro rfl i hi
    rw [hp ⟨i, hi⟩, hq ⟨i, hi⟩]

theorem RepN.one : RepN idN 1 := by
  intro i
  have : getN idN i = i := by unfold idN; revert i; decide +kernel
  exact this


theorem repN_of_tab {t : Tab} {g : Equiv.Perm (Fin 42)} (h : TabRep t g) {p : Nat}
    (hp : ∀ i < 42, getN p i = t[i]!) : RepN p g := by
  intro i
  rw [hp i i.2]
  exact h.apply i

@[expose] def g1N : Nat :=
  4029333375731133465266316549235792858047137147608942922134369139076081147909

@[expose] def g2N : Nat :=
  4248481535043882067047787218270844552694957965727465989626547830875589747264

@[expose] def g3N : Nat :=
  3788989062659729603762423655064869909684031809255659659146552634837763179584

theorem repN_g1 : RepN g1N g₁ := repN_of_tab tabRep_g₁ (by decide +kernel)

theorem repN_g2 : RepN g2N g₂ := repN_of_tab tabRep_g₂ (by decide +kernel)

theorem repN_g3 : RepN g3N g₃ := repN_of_tab tabRep_g₃ (by decide +kernel)

@[expose] def genN (j : ℕ) : Nat := if j = 0 then g1N else if j = 1 then g2N else g3N

theorem repN_genN (j : ℕ) : RepN (genN j) (genS j) := by
  unfold genN genS
  split_ifs
  · exact repN_g1
  · exact repN_g2
  · exact repN_g3

@[expose] def wN (w : List ℕ) : Nat := w.foldl (fun acc j => compN acc (genN j)) idN

theorem repN_foldl (w : List ℕ) {p : Nat} {g : Equiv.Perm (Fin 42)} (h : RepN p g) :
    RepN (w.foldl (fun acc j => compN acc (genN j)) p) (w.foldl (fun g j => g * genS j) g) := by
  induction w generalizing p g with
  | nil => exact h
  | cons j w ih => exact ih (h.comp (repN_genN j))

theorem repN_wN (w : List ℕ) : RepN (wN w) (wordPerm w) := repN_foldl w RepN.one

@[expose] def c1W : List (List ℕ) :=
  [[], [0, 0, 1, 0], [0, 0, 2, 0], [0, 0, 1, 2, 0], [1, 0, 0, 1, 0, 1], [1, 0, 0, 2, 0, 1],
   [2, 0, 0, 1, 0, 2], [2, 0, 0, 2, 0, 2], [1, 0, 0, 1, 2, 0, 1], [2, 0, 0, 1, 2, 0, 2],
   [1, 2, 0, 0, 1, 0, 1, 2], [1, 2, 0, 0, 2, 0, 1, 2], [0, 1, 0, 1, 0, 0, 1, 0, 0],
   [0, 1, 0, 2, 0, 0, 1, 0, 0], [0, 2, 0, 1, 0, 0, 2, 0, 0], [0, 2, 0, 2, 0, 0, 2, 0, 0],
   [1, 2, 0, 0, 1, 2, 0, 1, 2], [0, 0, 1, 0, 1, 0, 0, 1, 0, 1], [0, 0, 1, 0, 2, 0, 0, 1, 0, 2],
   [0, 0, 2, 0, 2, 0, 0, 2, 0, 2], [0, 1, 0, 1, 0, 0, 1, 0, 1, 0],
   [0, 1, 0, 1, 0, 0, 1, 0, 2, 0], [0, 1, 0, 1, 2, 0, 0, 1, 0, 0],
   [0, 1, 0, 2, 0, 0, 1, 0, 1, 0], [0, 1, 0, 2, 0, 0, 1, 0, 2, 0],
   [0, 2, 0, 2, 0, 0, 2, 0, 2, 0], [0, 1, 0, 1, 0, 0, 1, 0, 1, 2, 0],
   [0, 1, 0, 1, 2, 0, 0, 1, 0, 2, 0], [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1],
   [0, 2, 0, 0, 2, 0, 2, 0, 2, 0, 0, 2], [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1],
   [0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 0, 1], [0, 2, 0, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2],
   [0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 0, 2], [1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0],
   [2, 0, 2, 0, 0, 2, 0, 0, 2, 0, 2, 0, 0], [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 2, 0, 1],
   [0, 1, 0, 0, 1, 0, 2, 0, 1, 0, 2, 0, 0, 2], [0, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 0, 0, 1],
   [0, 2, 0, 0, 2, 0, 2, 0, 2, 0, 1, 2, 0, 2], [0, 2, 0, 1, 2, 0, 2, 0, 2, 0, 2, 0, 0, 2],
   [1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 2, 0], [2, 0, 2, 0, 0, 2, 0, 0, 2, 0, 2, 0, 1, 0],
   [0, 1, 0, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2], [0, 1, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 2],
   [0, 1, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 2], [0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 0, 2],
   [0, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1], [0, 1, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 1],
   [0, 1, 0, 2, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 2], [0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 2, 0, 1],
   [0, 2, 0, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1], [0, 2, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 1],
   [0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 2, 0, 2], [0, 2, 0, 1, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2],
   [0, 2, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 1], [0, 2, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0, 1],
   [0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 0, 1], [1, 0, 0, 1, 0, 1, 0, 2, 0, 2, 0, 0, 2, 0, 0],
   [1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 2, 0], [1, 0, 2, 0, 1, 2, 0, 1, 2, 0, 2, 0, 1, 0, 0],
   [1, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 2, 0, 0], [2, 0, 0, 2, 0, 2, 0, 1, 0, 1, 0, 0, 1, 0, 0],
   [2, 0, 1, 0, 1, 2, 0, 1, 2, 0, 1, 0, 2, 0, 0]]

end CFSG.LocalAnalysis.WeakClosure81.W183L34

end

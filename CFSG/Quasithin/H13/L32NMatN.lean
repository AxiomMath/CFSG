module

public import CFSG.Quasithin.H13.L32NMatNInputs
public import CFSG.Quasithin.H13.L32NMat8
public import CFSG.Quasithin.H13.L32NItems1442Models
public import Mathlib.Data.LawfulXor.Basic
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.Quasithin.H13.MatNCert

open Mat8Cert (b2z b2z_xor b2z_and b2z_inj)

variable {n : ℕ}

@[expose] def vecN (n k : ℕ) : Fin n → ZMod 2 := fun i => b2z (k.testBit i)

@[expose] def codeB : List (ZMod 2) → ℕ
  | [] => 0
  | a :: l => a.val + 2 * codeB l

@[expose] def codeN (v : Fin n → ZMod 2) : ℕ := codeB (List.ofFn v)

theorem testBit_codeB (l : List (ZMod 2)) (i : ℕ) :
    (codeB l).testBit i = decide (l.getD i 0 = 1) := by
  induction l generalizing i with
  | nil => simp [codeB]
  | cons a l ih =>
    have ha := ZMod.val_lt a
    cases i with
    | zero =>
      have key : ∀ b : ZMod 2, decide (b.val = 1) = decide (b = 1) := by decide
      simp only [codeB, Nat.testBit_zero, List.getD_cons_zero]
      rw [show (a.val + 2 * codeB l) % 2 = a.val by omega]
      exact key a
    | succ j =>
      simp only [codeB, Nat.testBit_succ, List.getD_cons_succ, ← ih j]
      congr 1
      omega

theorem codeB_lt (l : List (ZMod 2)) : codeB l < 2 ^ l.length := by
  induction l with
  | nil => simp [codeB]
  | cons a l ih =>
    have ha := ZMod.val_lt a
    simp only [codeB, List.length_cons, pow_succ]
    omega

theorem vecN_codeN (v : Fin n → ZMod 2) : vecN n (codeN v) = v := by
  ext i
  have key : ∀ a : ZMod 2, b2z (decide (a = 1)) = a := by decide
  simp only [vecN, codeN, testBit_codeB]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  exact key (v i)

theorem codeN_lt (v : Fin n → ZMod 2) : codeN v < 2 ^ n := by
  have := codeB_lt (List.ofFn v)
  rwa [List.length_ofFn] at this

theorem vecN_inj {m k : ℕ} (hm : m < 2 ^ n) (hk : k < 2 ^ n) (h : vecN n m = vecN n k) :
    m = k := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · exact b2z_inj (congrFun h ⟨i, hi⟩)
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num)
      (by omega))), Nat.testBit_lt_two_pow (lt_of_lt_of_le hk (Nat.pow_le_pow_right
      (by norm_num) (by omega)))]

theorem codeN_vecN {k : ℕ} (hk : k < 2 ^ n) : codeN (vecN n k) = k :=
  vecN_inj (codeN_lt _) hk (vecN_codeN _)

theorem vecN_xor (a b : ℕ) : vecN n (a ^^^ b) = vecN n a + vecN n b := by
  ext i
  simp only [vecN, Nat.testBit_xor, b2z_xor, Pi.add_apply]

theorem vecN_zero : vecN n 0 = 0 := by
  ext i
  simp [vecN, b2z]

theorem b2z_testBit_mvN (A : List ℕ) (v i : ℕ) :
    b2z ((mvN A v).testBit i) = ∑ j ∈ Finset.range A.length,
      b2z (v.testBit j) * b2z ((A.getD j 0).testBit i) := by
  induction A generalizing v with
  | nil => simp [mvN, b2z]
  | cons c A ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [mvN, Nat.testBit_xor, b2z_xor, ih (v / 2), List.getD_cons_succ,
      List.getD_cons_zero, Nat.testBit_succ]
    rw [add_comm]
    congr 1
    cases v.testBit 0 <;> simp [b2z]

theorem mvN_zero (A : List ℕ) : mvN A 0 = 0 := by
  induction A with
  | nil => rfl
  | cons c A ih => simp [mvN, ih]

theorem mvN_xor (A : List ℕ) (a b : ℕ) : mvN A (a ^^^ b) = mvN A a ^^^ mvN A b := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply b2z_inj
  rw [Nat.testBit_xor, b2z_xor, b2z_testBit_mvN, b2z_testBit_mvN, b2z_testBit_mvN,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.testBit_xor, b2z_xor, add_mul]

theorem mvN_ite (A : List ℕ) (p : Bool) (c : ℕ) :
    mvN A (if p then c else 0) = if p then mvN A c else 0 := by
  cases p
  · exact mvN_zero A
  · rfl

theorem mvN_mulN (A B : List ℕ) (v : ℕ) : mvN (mulN A B) v = mvN A (mvN B v) := by
  induction B generalizing v with
  | nil => exact (mvN_zero A).symm
  | cons c B ih =>
    simp only [mulN, List.map_cons] at ih ⊢
    simp only [mvN] at ih ⊢
    rw [ih, mvN_xor, mvN_ite]

@[expose] def decN (n : ℕ) (A : List ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun i j => vecN n (A.getD j 0) i

theorem decN_mulVec {A : List ℕ} (hA : A.length = n) (v : ℕ) :
    (decN n A).mulVec (vecN n v) = vecN n (mvN A v) := by
  ext i
  have h := b2z_testBit_mvN A v i
  rw [hA, Finset.sum_range] at h
  simp only [Matrix.mulVec, dotProduct, decN, Matrix.of_apply, vecN, h]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem getD_mulN {A B : List ℕ} {j : ℕ} (hj : j < B.length) :
    (mulN A B).getD j 0 = mvN A (B.getD j 0) := by
  simp only [mulN, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
    Option.map_some, Option.getD_some]

theorem decN_mulN {A B : List ℕ} (hA : A.length = n) (hB : B.length = n) :
    decN n (mulN A B) = decN n A * decN n B := by
  ext i j
  have hj : (j : ℕ) < B.length := by rw [hB]; exact j.isLt
  simp only [decN, Matrix.of_apply, Matrix.mul_apply]
  rw [getD_mulN hj, ← decN_mulVec hA]
  simp only [Matrix.mulVec, dotProduct, decN, Matrix.of_apply]

theorem decN_oneN : decN n (oneN n) = 1 := by
  ext i j
  have hj : (j : ℕ) < (oneN n).length := by simp [oneN]
  simp only [decN, Matrix.of_apply, Matrix.one_apply, vecN]
  rw [List.getD_eq_getElem _ _ hj]
  simp only [oneN, List.getElem_map, List.getElem_range, Nat.testBit_two_pow]
  by_cases h : i = j
  · subst h
    simp [b2z]
  · have h' : (j : ℕ) ≠ i := fun h' => h (Fin.ext h'.symm)
    simp [b2z, h, h']

@[expose] def ValidN (n : ℕ) (A : List ℕ) : Prop := A.length = n ∧ ∀ c ∈ A, c < 2 ^ n

theorem getD_lt_of_validN {A : List ℕ} (hA : ValidN n A) (j : ℕ) : A.getD j 0 < 2 ^ n := by
  by_cases hj : j < A.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact hA.2 _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.two_pow_pos n

theorem decN_injOn {A A' : List ℕ} (hA : ValidN n A) (hA' : ValidN n A')
    (h : decN n A = decN n A') : A = A' := by
  apply List.ext_getElem (hA.1.trans hA'.1.symm)
  intro j hj hj'
  have hjn : j < n := hA.1 ▸ hj
  have hcol : vecN n (A.getD j 0) = vecN n (A'.getD j 0) := by
    ext i
    have := congrFun (congrFun h i) ⟨j, hjn⟩
    simpa [decN] using this
  have h1 := vecN_inj (getD_lt_of_validN hA j) (getD_lt_of_validN hA' j) hcol
  rwa [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj'] at h1

@[expose] def colsN (M : Matrix (Fin n) (Fin n) (ZMod 2)) : List ℕ :=
  List.ofFn fun j => codeN fun i => M i j

theorem validN_colsN (M : Matrix (Fin n) (Fin n) (ZMod 2)) : ValidN n (colsN M) := by
  refine ⟨List.length_ofFn, fun c hc => ?_⟩
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
  exact codeN_lt _

theorem decN_colsN (M : Matrix (Fin n) (Fin n) (ZMod 2)) : decN n (colsN M) = M := by
  ext i j
  simp only [decN, colsN, Matrix.of_apply]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  exact congrFun (vecN_codeN _) i

theorem colsN_decN {A : List ℕ} (hA : ValidN n A) : colsN (decN n A) = A :=
  decN_injOn (validN_colsN _) hA (decN_colsN _)

theorem colsN_eq_iff {M : Matrix (Fin n) (Fin n) (ZMod 2)} {A : List ℕ} (hA : ValidN n A) :
    colsN M = A ↔ decN n A = M := by
  constructor
  · rintro rfl
    exact decN_colsN M
  · rintro rfl
    exact colsN_decN hA

theorem length_mulN (A B : List ℕ) : (mulN A B).length = B.length := List.length_map _

theorem mvN_lt {A : List ℕ} (hA : ∀ c ∈ A, c < 2 ^ n) (v : ℕ) : mvN A v < 2 ^ n := by
  induction A generalizing v with
  | nil => exact Nat.two_pow_pos n
  | cons c A ih =>
    simp only [mvN]
    refine Nat.xor_lt_two_pow ?_ (ih (fun c' hc' => hA c' (List.mem_cons_of_mem _ hc')) _)
    split
    · exact hA c List.mem_cons_self
    · exact Nat.two_pow_pos n

theorem validN_mulN {A B : List ℕ} (hA : ValidN n A) (hB : ValidN n B) :
    ValidN n (mulN A B) := by
  refine ⟨(length_mulN A B).trans hB.1, fun c hc => ?_⟩
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp hc
  exact mvN_lt hA.2 v

theorem colsN_mul (M N : Matrix (Fin n) (Fin n) (ZMod 2)) :
    colsN (M * N) = mulN (colsN M) (colsN N) := by
  refine decN_injOn (validN_colsN _) (validN_mulN (validN_colsN _) (validN_colsN _)) ?_
  rw [decN_colsN, decN_mulN (validN_colsN M).1 (validN_colsN N).1, decN_colsN, decN_colsN]

theorem validN_oneN : ValidN n (oneN n) := by
  refine ⟨by simp [oneN], fun c hc => ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
  exact Nat.pow_lt_pow_right (by norm_num) (List.mem_range.mp hj)

theorem colsN_one : colsN (1 : Matrix (Fin n) (Fin n) (ZMod 2)) = oneN n := by
  rw [colsN_eq_iff validN_oneN, decN_oneN]

theorem mulVec_vecN (M : Matrix (Fin n) (Fin n) (ZMod 2)) (v : ℕ) :
    M.mulVec (vecN n v) = vecN n (mvN (colsN M) v) := by
  rw [← decN_mulVec (validN_colsN M).1, decN_colsN]

theorem b2z_dotN (k v w : ℕ) :
    b2z (dotN k v w) = ∑ i ∈ Finset.range k, b2z (v.testBit i) * b2z (w.testBit i) := by
  induction k generalizing v w with
  | zero => simp [dotN, b2z]
  | succ k ih =>
    rw [Finset.sum_range_succ']
    simp only [dotN, b2z_xor, b2z_and, ih, Nat.testBit_succ]
    ring

theorem dotN_spec (v w : ℕ) : b2z (dotN n v w) = vecN n v ⬝ᵥ vecN n w := by
  rw [b2z_dotN, Finset.sum_range]
  rfl

theorem quadN_spec {Q : List ℕ} (hQ : Q.length = n) (v : ℕ) :
    b2z (quadN n Q v) = L1442M.quadOf (decN n Q) (vecN n v) := by
  rw [quadN, dotN_spec, L1442M.quadOf, decN_mulVec hQ]

@[expose] def polV (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (v w : Fin n → ZMod 2) : ZMod 2 :=
  L1442M.quadOf Q (v + w) + L1442M.quadOf Q v + L1442M.quadOf Q w

theorem polN_spec {Q : List ℕ} (hQ : Q.length = n) (v w : ℕ) :
    b2z (polN n Q v w) = polV (decN n Q) (vecN n v) (vecN n w) := by
  simp only [polN, b2z_xor, quadN_spec hQ, vecN_xor, polV]

theorem spanN_mem (vs : List ℕ) (W : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hW : ∀ v ∈ vs, vecN n v ∈ W) : ∀ c ∈ spanN vs, vecN n c ∈ W := by
  unfold spanN
  suffices key : ∀ (vs' : List ℕ) (S : List ℕ), (∀ v ∈ vs', vecN n v ∈ W) →
      (∀ c ∈ S, vecN n c ∈ W) → ∀ c ∈ vs'.foldl
        (fun S v => if S.contains v then S else S ++ S.map (· ^^^ v)) S, vecN n c ∈ W by
    refine key vs [0] hW ?_
    intro c hc
    rw [List.mem_singleton.mp hc, vecN_zero]
    exact W.zero_mem
  intro vs'
  induction vs' with
  | nil => intro S _ hS; exact hS
  | cons v vs' ih =>
    intro S hv hS
    rw [List.foldl_cons]
    refine ih _ (fun w hw => hv w (List.mem_cons_of_mem _ hw)) ?_
    split
    · exact hS
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hS c hc
      · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
        rw [vecN_xor]
        exact W.add_mem (hS c' hc') (hv v List.mem_cons_self)

end CFSG.Quasithin.H13.MatNCert

module

public import CFSG.Quasithin.Recognition.M12AmalAutCheck2
public import CFSG.Quasithin.Recognition.M12AmalAutJData
public import CFSG.Quasithin.Recognition.M12AmalAutJPack
public import CFSG.Quasithin.Recognition.M12AmalAutJMul

public section

namespace CFSG.Quasithin.M12AmalAut

open CFSG.Sporadic.Bridge Equiv

@[expose] def telMul (i j : ℕ) : ℕ := (telMulTab.getD i []).getD j 0

@[expose] def telInv (i : ℕ) : ℕ := telInvTab.getD i 0

@[expose] def MulRowOK (i : ℕ) : Prop :=
  ∀ j < 128, telMul i j < 128 ∧ compL (tl i) (tl j) = tl (telMul i j)

instance (i : ℕ) : Decidable (MulRowOK i) := by unfold MulRowOK; infer_instance

theorem telMul_c0 : ∀ i, 0 ≤ i → i < 16 → MulRowOK i := by
  have h : ∀ i, 0 ≤ i → i < 16 → JPack.rowB JMul.mK i = true := by decide +kernel
  have e : telMul = JMul.mK := funext fun i => funext fun j => JMul.getD_mK i j
  intro i h0 h1
  unfold MulRowOK
  rw [e]
  exact JPack.row_spec JMul.mK (by omega) (h i h0 h1)

theorem telMul_c1 : ∀ i, 16 ≤ i → i < 32 → MulRowOK i := by
  have h : ∀ i, 16 ≤ i → i < 32 → JPack.rowB JMul.mK i = true := by decide +kernel
  have e : telMul = JMul.mK := funext fun i => funext fun j => JMul.getD_mK i j
  intro i h0 h1
  unfold MulRowOK
  rw [e]
  exact JPack.row_spec JMul.mK (by omega) (h i h0 h1)

theorem telMul_c2 : ∀ i, 32 ≤ i → i < 48 → MulRowOK i := by
  have h : ∀ i, 32 ≤ i → i < 48 → JPack.rowB JMul.mK i = true := by decide +kernel
  have e : telMul = JMul.mK := funext fun i => funext fun j => JMul.getD_mK i j
  intro i h0 h1
  unfold MulRowOK
  rw [e]
  exact JPack.row_spec JMul.mK (by omega) (h i h0 h1)

theorem telMul_c3 : ∀ i, 48 ≤ i → i < 64 → MulRowOK i := by
  have h : ∀ i, 48 ≤ i → i < 64 → JPack.rowB JMul.mK i = true := by decide +kernel
  have e : telMul = JMul.mK := funext fun i => funext fun j => JMul.getD_mK i j
  intro i h0 h1
  unfold MulRowOK
  rw [e]
  exact JPack.row_spec JMul.mK (by omega) (h i h0 h1)

theorem telMul_c4 : ∀ i, 64 ≤ i → i < 80 → MulRowOK i := by
  have h : ∀ i, 64 ≤ i → i < 80 → JPack.rowB JMul.mK i = true := by decide +kernel
  have e : telMul = JMul.mK := funext fun i => funext fun j => JMul.getD_mK i j
  intro i h0 h1
  unfold MulRowOK
  rw [e]
  exact JPack.row_spec JMul.mK (by omega) (h i h0 h1)

theorem telMul_c5 : ∀ i, 80 ≤ i → i < 96 → MulRowOK i := by
  have h : ∀ i, 80 ≤ i → i < 96 → JPack.rowB JMul.mK i = true := by decide +kernel
  have e : telMul = JMul.mK := funext fun i => funext fun j => JMul.getD_mK i j
  intro i h0 h1
  unfold MulRowOK
  rw [e]
  exact JPack.row_spec JMul.mK (by omega) (h i h0 h1)

theorem telMul_c6 : ∀ i, 96 ≤ i → i < 112 → MulRowOK i := by
  have h : ∀ i, 96 ≤ i → i < 112 → JPack.rowB JMul.mK i = true := by decide +kernel
  have e : telMul = JMul.mK := funext fun i => funext fun j => JMul.getD_mK i j
  intro i h0 h1
  unfold MulRowOK
  rw [e]
  exact JPack.row_spec JMul.mK (by omega) (h i h0 h1)

theorem telMul_c7 : ∀ i, 112 ≤ i → i < 128 → MulRowOK i := by
  have h : ∀ i, 112 ≤ i → i < 128 → JPack.rowB JMul.mK i = true := by decide +kernel
  have e : telMul = JMul.mK := funext fun i => funext fun j => JMul.getD_mK i j
  intro i h0 h1
  unfold MulRowOK
  rw [e]
  exact JPack.row_spec JMul.mK (by omega) (h i h0 h1)

theorem telMul_chk (i : ℕ) (hi : i < 128) : MulRowOK i := by
  by_cases h0 : i < 16
  · exact telMul_c0 i (by omega) h0
  by_cases h1 : i < 32
  · exact telMul_c1 i (by omega) h1
  by_cases h2 : i < 48
  · exact telMul_c2 i (by omega) h2
  by_cases h3 : i < 64
  · exact telMul_c3 i (by omega) h3
  by_cases h4 : i < 80
  · exact telMul_c4 i (by omega) h4
  by_cases h5 : i < 96
  · exact telMul_c5 i (by omega) h5
  by_cases h6 : i < 112
  · exact telMul_c6 i (by omega) h6
  exact telMul_c7 i (by omega) hi

theorem telInv_chk : ∀ i < 128, telInv i < 128 ∧ compL (tl i) (tl (telInv i)) = idl := by
  decide +kernel

theorem tl_zero : tl 0 = idl := by decide +kernel

theorem invIdx_chk : ∀ u < 128, (u ≠ 0 ∧ telMul u u = 0) ↔ u ∈ invIdx := by
  have e : telMul = JMul.mK := funext fun i => funext fun j => JMul.getD_mK i j
  rw [e]
  decide +kernel

theorem eIdx_chk : eIdx.length = 16 ∧ eIdx.Nodup ∧ (∀ i ∈ eIdx, i < 128) ∧ 0 ∈ eIdx ∧
    ∀ i ∈ eIdx, ∀ j ∈ eIdx, telMul i j ∈ eIdx ∧ telMul i j = telMul j i ∧ telMul i i = 0 := by
  have e : telMul = JMul.mK := funext fun i => funext fun j => JMul.getD_mK i j
  rw [e]
  decide +kernel

theorem eIdx_inv_chk : ∀ i ∈ eIdx, telInv i ∈ eIdx := by decide +kernel

theorem rIdx_chk : rIdx.length = 64 ∧ rIdx.Nodup ∧ (∀ i ∈ rIdx, i < 128) ∧ 0 ∈ rIdx ∧
    ∀ i ∈ rIdx, ∀ j ∈ rIdx, telMul i j ∈ rIdx := by
  have e : telMul = JMul.mK := funext fun i => funext fun j => JMul.getD_mK i j
  have h1 : JPack.incB rIdx 0 = true := by decide +kernel
  have h2 : JPack.allL (fun i => JPack.allL (fun j => JPack.memN (JMul.mK i j) rIdx) rIdx) rIdx =
      true := by decide +kernel
  rw [e]
  exact ⟨by decide +kernel, (JPack.nodup_of_incB h1).2, by decide +kernel, by decide +kernel,
    fun i hi j hj => JPack.memN_iff.1 (JPack.allL_iff.1 (JPack.allL_iff.1 h2 i hi) j hj)⟩

theorem rIdx_inv_chk : ∀ i ∈ rIdx, telInv i ∈ rIdx := by decide +kernel

theorem erIdx_chk : ∀ i < 128, i ∈ erIdx ↔ (i ∈ eIdx ∧ i ∈ rIdx) := by decide +kernel

theorem eNotR_chk : ∃ i ∈ eIdx, i ∉ rIdx := by decide +kernel

@[expose] def NormOK (L : List ℕ) : Prop :=
  ∀ k ∈ [0, 1, 2, 4], ∀ j ∈ L,
    (∃ i' ∈ L, compL (compL (gl k) (tl j)) (gil k) = tl i') ∧
      (∃ i' ∈ L, compL (compL (gil k) (tl j)) (gl k) = tl i')

instance (L : List ℕ) : Decidable (NormOK L) := by unfold NormOK; infer_instance

theorem E_norm_chk : NormOK eIdx := by decide +kernel

theorem ER_norm_chk : NormOK erIdx := by decide +kernel

theorem famTab_zero_chk : [0] ∈ famTab := by decide +kernel

theorem famTab_bound_chk : ∀ X ∈ famTab, X.length ≤ 16 ∧ (X.length = 16 → X = eIdx) ∧ X.Nodup ∧
    (∀ i ∈ X, i < 128) ∧ 0 ∈ X := by
  decide +kernel

@[expose] def insSorted (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b :: l => if a ≤ b then a :: b :: l else b :: insSorted a l

@[expose] def sortList : List ℕ → List ℕ
  | [] => []
  | a :: l => insSorted a (sortList l)

theorem mem_insSorted (a i : ℕ) (l : List ℕ) : i ∈ insSorted a l ↔ i = a ∨ i ∈ l := by
  induction l with
  | nil => simp [insSorted]
  | cons b l ih =>
    unfold insSorted
    split_ifs
    · simp
    · simp only [List.mem_cons, ih]
      tauto

theorem mem_sortList (i : ℕ) (l : List ℕ) : i ∈ sortList l ↔ i ∈ l := by
  induction l with
  | nil => simp [sortList]
  | cons a l ih =>
    unfold sortList
    rw [mem_insSorted, ih]
    simp

@[expose] def extList (X : List ℕ) (u : ℕ) : List ℕ :=
  sortList (X ++ X.map (fun j => telMul j u))

theorem famTab_ext_chk : ∀ X ∈ famTab, ∀ u ∈ invIdx, u ∉ X → (∀ j ∈ X, telMul u j = telMul j u) →
    extList X u ∈ famTab := by
  have e : telMul = JMul.mK := funext fun i => funext fun j => JMul.getD_mK i j
  have hins : ∀ a l, insSorted a l = JPack.insK a l := by
    intro a l
    induction l with
    | nil => rfl
    | cons b l ih => rw [insSorted, JPack.insK_cons, ih]
  have hsort : ∀ l, sortList l = JPack.sortK l := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [sortList, ih, hins]
      rfl
  have hB : JPack.famB JMul.mK famTab invIdx JMul.famK = true := by decide +kernel
  intro X hX u hu hn hc
  rw [e] at hc
  unfold extList
  rw [hsort, e, JPack.sortK_ext]
  exact JPack.famB_spec hB X hX u hu hn hc

@[expose] def StepOK (s : ℕ) (st : ℕ × ℕ × ℕ × ℕ × ℕ) : Prop :=
  s < 128 ∧ st.1 < 128 ∧ st.2.2.1 < 128 ∧ st.2.2.2.2 < 128 ∧ st.2.2.2.1 < 28 ∧
    ((st.2.1 = 0 ∧ (st.2.2.2.1 = 0 ∨ st.2.2.2.1 = 1)) ∨
      (st.2.1 = 1 ∧ (st.2.2.2.1 = 0 ∨ st.2.2.2.1 = 2))) ∧
    compL (compL (compL (compL (tl st.2.2.1) (dTab.getD st.2.2.2.1 [])) (tl st.2.2.2.2)) (tl s))
        (compL (compL (tl (telInv st.2.2.2.2)) (dInvTab.getD st.2.2.2.1 []))
          (tl (telInv st.2.2.1))) = tl st.1

instance (s : ℕ) (st : ℕ × ℕ × ℕ × ℕ × ℕ) : Decidable (StepOK s st) := by
  unfold StepOK; infer_instance

@[expose] def pathEndB : ℕ → List (ℕ × ℕ × ℕ × ℕ × ℕ) → Bool
  | s, [] => decide (s ∈ erIdx)
  | s, st :: rest => decide (StepOK s st) && pathEndB st.1 rest

theorem pathEndB_nil {s : ℕ} (h : pathEndB s [] = true) : s ∈ erIdx := by
  simpa [pathEndB] using h

theorem pathEndB_cons {s : ℕ} {st : ℕ × ℕ × ℕ × ℕ × ℕ} {rest : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
    (h : pathEndB s (st :: rest) = true) : StepOK s st ∧ pathEndB st.1 rest = true := by
  simpa [pathEndB] using h

theorem invRIdx_len : invRIdx.length = 27 ∧ fuseTab.length = 27 := by decide +kernel

theorem fuse_chk : ∀ k < 27, pathEndB (invRIdx.getD k 0) (fuseTab.getD k []) = true := by
  decide +kernel

theorem rInv_chk : ∀ i ∈ rIdx, telMul i i = 0 → i = 0 ∨ i ∈ invRIdx := by
  have e : telMul = JMul.mK := funext fun i => funext fun j => JMul.getD_mK i j
  rw [e]
  decide +kernel

theorem erIdx_lt_chk : ∀ i ∈ erIdx, i < 128 := by decide +kernel

theorem tl_mem_chk : ∀ i < 128, tl i ∈ telTab := by decide +kernel

@[expose] def LBq (i : ℕ) : Prop :=
  compL (compL (gl 4) (tl i)) (gil 4) ∈ telTab ∧ compL (compL (gil 4) (tl i)) (gl 4) ∈ telTab

instance (i : ℕ) : Decidable (LBq i) := by unfold LBq; infer_instance

theorem B_central_chk : ∀ i < 128, LBq i →
    (compL (tl 111) (tl i) = compL (tl i) (tl 111)) ∧ (compL (tl 36) (tl i) = compL (tl i) (tl 36)) := by
  decide +kernel

theorem tl_ne_chk : tl 111 ≠ tl 36 ∧ tl 111 ≠ idl ∧ tl 36 ≠ idl := by decide +kernel

end CFSG.Quasithin.M12AmalAut

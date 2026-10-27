module

public import CFSG.RankThree.PartOne.KE.E8TwelveLattice
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartOne.KE8F

open CFSG.Blueprint.Chevalley Matrix CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE

@[expose] def e8P4V : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ := e8T12U ^ 6

@[expose] def e8P4VList : List (List ℤ) := lpow Tag.E8.rank e8T12UList 6

@[expose] def e8P4WW : List (Fin Tag.E8.rank) :=
  e8T12Word ++ e8T12Word ++ e8T12Word ++ e8T12Word ++ e8T12Word ++ e8T12Word

@[expose] def e8P4BRows : List (List ℤ) :=
  [[1, 1, 0, 1, 1, 0, 0, 1], [0, 1, 0, 2, 1, 1, 1, 1], [0, 2, 1, 2, 1, 1, 1, 1],
    [0, 2, 1, 3, 1, 2, 2, 2], [0, 2, 1, 2, 1, 2, 2, 1], [0, 2, 0, 1, 1, 2, 1, 1],
    [0, 1, 0, 1, 0, 1, 1, 1], [0, 1, 0, 0, 0, 1, 0, 0]]

@[expose] def e8P4BinvRows : List (List ℤ) :=
  [[1, 0, -1, 0, 1, -1, 0, 1], [0, 0, 1, -1, 0, 0, 1, 0], [0, -1, 0, 1, 0, 0, -1, 0],
    [0, 1, 0, 0, 0, -1, 0, 1], [0, 0, 0, 0, 0, 1, -1, -1], [0, 0, -1, 1, 0, 0, -1, 1],
    [0, 0, 0, -1, 1, 0, 1, -1], [0, -1, 0, 1, -1, 1, 0, -1]]

@[expose] def e8P4JRows : List (List ℤ) :=
  [[0, -1, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 1, 0]]

@[expose] def e8P4B : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ := toMat Tag.E8.rank e8P4BRows

@[expose] def e8P4Binv : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  toMat Tag.E8.rank e8P4BinvRows

@[expose] def e8P4J : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ := toMat Tag.E8.rank e8P4JRows

theorem e8P4V_eq : e8P4V = toMat Tag.E8.rank e8P4VList := by
  rw [e8P4V, e8P4VList, toMat_lpow, e8T12U_eq]

theorem e8P4V_sq : e8P4V * e8P4V = -1 := by
  have hL : ladd Tag.E8.rank (lmul Tag.E8.rank e8P4VList e8P4VList) (lid Tag.E8.rank) =
      lofFn Tag.E8.rank (fun _ _ => 0) := by
    decide +kernel
  have h := congrArg (toMat Tag.E8.rank) hL
  rw [toMat_ladd, toMat_lmul, toMat_lid, toMat_lofFn, ← e8P4V_eq] at h
  have h0 : (Matrix.of fun (_ _ : Fin Tag.E8.rank) => (0 : ℤ)) = 0 := rfl
  rw [h0] at h
  exact eq_neg_of_add_eq_zero_left h

theorem e8P4_wordMat : wordMat Tag.E8 e8P4WW = e8P4V := by
  have h : wordMat Tag.E8 e8T12Word = e8T12U := rfl
  simp only [e8P4WW, wordMat_append, h, e8P4V]
  simp only [pow_succ, pow_zero, one_mul]

theorem e8P4B_mul_Binv : e8P4B * e8P4Binv = 1 := by
  have hL : lmul Tag.E8.rank e8P4BRows e8P4BinvRows = lid Tag.E8.rank := by decide +kernel
  have h := congrArg (toMat Tag.E8.rank) hL
  rw [toMat_lmul, toMat_lid] at h
  exact h

theorem e8P4Binv_mul_B : e8P4Binv * e8P4B = 1 := by
  have hL : lmul Tag.E8.rank e8P4BinvRows e8P4BRows = lid Tag.E8.rank := by decide +kernel
  have h := congrArg (toMat Tag.E8.rank) hL
  rw [toMat_lmul, toMat_lid] at h
  exact h

theorem e8P4V_mul_B : e8P4V * e8P4B = e8P4B * e8P4J := by
  have hL : lmul Tag.E8.rank e8P4VList e8P4BRows = lmul Tag.E8.rank e8P4BRows e8P4JRows := by
    decide +kernel
  have h := congrArg (toMat Tag.E8.rank) hL
  rw [toMat_lmul, toMat_lmul, ← e8P4V_eq] at h
  exact h


section Roots

@[expose] def e8P4Coord (l : List ℤ) : List ℤ := lmulVec Tag.E8.rank e8P4BinvRows l

@[expose] def e8P4Neg (l : List ℤ) : List ℤ := l.map fun x => -x

@[expose] def e8P4SameClass (l l' : List ℤ) : Bool :=
  l' == l || l' == e8P4Neg l || l' == lmulVec Tag.E8.rank e8P4VList l ||
    l' == e8P4Neg (lmulVec Tag.E8.rank e8P4VList l)

@[expose] def e8P4Nrm (c : List ℤ) (j : ℕ) : ℤ :=
  c.getD (2 * j) 0 * c.getD (2 * j) 0 + c.getD (2 * j + 1) 0 * c.getD (2 * j + 1) 0

theorem e8P4_coord_nonzero_list : ∀ l ∈ Tag.E8.artifactRoots,
    (List.range 4).any (fun j => decide (1 ≤ e8P4Nrm (e8P4Coord l) j ∧
      e8P4Nrm (e8P4Coord l) j ≤ 4)) = true := by
  decide +kernel

abbrev GZ := ℤ × ℤ

abbrev GRow := GZ × GZ × GZ × GZ

@[expose] def e8P4G (c : List ℤ) : GRow :=
  ((c.getD 0 0, c.getD 1 0), (c.getD 2 0, c.getD 3 0), (c.getD 4 0, c.getD 5 0),
    (c.getD 6 0, c.getD 7 0))

@[expose] def gminorNorm (z z' w w' : GZ) : ℤ :=
  (z.1 * w'.1 - z.2 * w'.2 - (z'.1 * w.1 - z'.2 * w.2)) ^ 2 +
    (z.1 * w'.2 + z.2 * w'.1 - (z'.1 * w.2 + z'.2 * w.1)) ^ 2

@[expose] def gRowMinorOK (u w : GRow) : Bool :=
  decide (gminorNorm u.1 u.2.1 w.1 w.2.1 = 1 ∨ gminorNorm u.1 u.2.1 w.1 w.2.1 = 2) ||
  decide (gminorNorm u.1 u.2.2.1 w.1 w.2.2.1 = 1 ∨ gminorNorm u.1 u.2.2.1 w.1 w.2.2.1 = 2) ||
  decide (gminorNorm u.1 u.2.2.2 w.1 w.2.2.2 = 1 ∨ gminorNorm u.1 u.2.2.2 w.1 w.2.2.2 = 2) ||
  decide (gminorNorm u.2.1 u.2.2.1 w.2.1 w.2.2.1 = 1 ∨ gminorNorm u.2.1 u.2.2.1 w.2.1 w.2.2.1 = 2) ||
  decide (gminorNorm u.2.1 u.2.2.2 w.2.1 w.2.2.2 = 1 ∨ gminorNorm u.2.1 u.2.2.2 w.2.1 w.2.2.2 = 2) ||
  decide (gminorNorm u.2.2.1 u.2.2.2 w.2.2.1 w.2.2.2 = 1 ∨
    gminorNorm u.2.2.1 u.2.2.2 w.2.2.1 w.2.2.2 = 2)

@[expose] def e8P4Entry (l : List ℤ) : List ℤ × GRow × List ℤ :=
  (l, e8P4G (e8P4Coord l), lmulVec Tag.E8.rank e8P4VList l)

@[expose] def e8P4Table : List (List ℤ × GRow × List ℤ) :=
  Tag.E8.artifactRoots.map e8P4Entry

@[expose] def e8P4PairOK (x y : List ℤ × GRow × List ℤ) : Bool :=
  (y.1 == x.1 || y.1 == e8P4Neg x.1 || y.1 == x.2.2 || y.1 == e8P4Neg x.2.2) ||
    gRowMinorOK x.2.1 y.2.1

set_option maxHeartbeats 0 in
theorem e8P4_minor_chunk0 : ∀ x ∈ (e8P4Table.drop 0).take 30, ∀ y ∈ e8P4Table,
    e8P4PairOK x y = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem e8P4_minor_chunk1 : ∀ x ∈ (e8P4Table.drop 30).take 30, ∀ y ∈ e8P4Table,
    e8P4PairOK x y = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem e8P4_minor_chunk2 : ∀ x ∈ (e8P4Table.drop 60).take 30, ∀ y ∈ e8P4Table,
    e8P4PairOK x y = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem e8P4_minor_chunk3 : ∀ x ∈ (e8P4Table.drop 90).take 30, ∀ y ∈ e8P4Table,
    e8P4PairOK x y = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem e8P4_minor_chunk4 : ∀ x ∈ (e8P4Table.drop 120).take 30, ∀ y ∈ e8P4Table,
    e8P4PairOK x y = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem e8P4_minor_chunk5 : ∀ x ∈ (e8P4Table.drop 150).take 30, ∀ y ∈ e8P4Table,
    e8P4PairOK x y = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem e8P4_minor_chunk6 : ∀ x ∈ (e8P4Table.drop 180).take 30, ∀ y ∈ e8P4Table,
    e8P4PairOK x y = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem e8P4_minor_chunk7 : ∀ x ∈ (e8P4Table.drop 210).take 30, ∀ y ∈ e8P4Table,
    e8P4PairOK x y = true := by
  decide +kernel

theorem forall_mem_of_chunks {α : Type*} {P : α → Prop} (L : List α) (n : ℕ)
    (h1 : ∀ x ∈ L.take n, P x) (h2 : ∀ x ∈ L.drop n, P x) : ∀ x ∈ L, P x := by
  intro x hx
  rw [← List.take_append_drop n L, List.mem_append] at hx
  rcases hx with hx | hx
  exacts [h1 x hx, h2 x hx]

theorem e8P4_minor_table : ∀ x ∈ e8P4Table, ∀ y ∈ e8P4Table, e8P4PairOK x y = true := by
  have hlen : e8P4Table.length = 240 := by decide +kernel
  have key : ∀ k : ℕ, k ≤ 8 → ∀ x ∈ e8P4Table.drop (30 * k), ∀ y ∈ e8P4Table,
      e8P4PairOK x y = true := by
    intro k
    induction' h : 8 - k with m ih generalizing k
    · intro hk x hx
      have : k = 8 := by omega
      subst this
      rw [List.drop_eq_nil_of_le (by omega)] at hx
      simp at hx
    · intro hk
      have hch : ∀ x ∈ (e8P4Table.drop (30 * k)).take 30, ∀ y ∈ e8P4Table,
          e8P4PairOK x y = true := by
        interval_cases k
        · exact e8P4_minor_chunk0
        · exact e8P4_minor_chunk1
        · exact e8P4_minor_chunk2
        · exact e8P4_minor_chunk3
        · exact e8P4_minor_chunk4
        · exact e8P4_minor_chunk5
        · exact e8P4_minor_chunk6
        · exact e8P4_minor_chunk7
        · omega
      refine forall_mem_of_chunks _ 30 hch (fun x hx => ?_)
      rw [List.drop_drop] at hx
      have := ih (k + 1) (by omega) (by omega)
      rw [show 30 * k + 30 = 30 * (k + 1) by ring] at hx
      exact this x hx
  exact fun x hx => key 0 (by omega) x (by simpa using hx)

end Roots

end CFSG.RankThree.PartOne.KE8F

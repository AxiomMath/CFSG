module

public import CFSG.Quasithin.AppendixH.H16.OctadZData

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24
  CFSG.Monster.Code CFSG.ASVolI.AppH CFSG.Quasithin.H156

@[expose] def dSubList : List ℕ := [1, 3, 5, 9, 15, 17, 33, 51, 65, 85, 105, 129, 153, 165, 195, 255]

@[expose] def dSubBasis : ℕ → List ℕ
  | 1 => [3, 5, 9, 17, 160, 352, 512]
  | 3 => [3, 5, 9, 17, 160, 512]
  | 5 => [3, 5, 9, 17, 448, 512]
  | 9 => [3, 5, 9, 17, 352, 512]
  | 15 => [3, 5, 9, 17, 512]
  | 17 => [3, 12, 20, 160, 352, 512]
  | 33 => [3, 12, 20, 160, 357, 512]
  | 51 => [3, 12, 20, 160, 512]
  | 65 => [3, 12, 20, 165, 357, 512]
  | 85 => [3, 12, 20, 448, 512]
  | 105 => [3, 12, 20, 357, 512]
  | 129 => [3, 12, 20, 165, 352, 512]
  | 153 => [3, 12, 20, 352, 512]
  | 165 => [3, 12, 20, 453, 512]
  | 195 => [3, 12, 20, 165, 512]
  | 255 => [3, 12, 20, 512]
  | _ => []

@[expose] def dSubCard (n : ℕ) : ℕ := (List.range 8).countP fun p => n.testBit p

@[expose] def dSubMem (n u : ℕ) : Bool := n.testBit (u / 2)

@[expose] def dSubClosed (n : ℕ) : Bool :=
  (List.range 8).all fun p => (List.range 8).all fun q =>
    !(n.testBit p && n.testBit q) || n.testBit (p ^^^ q)

theorem dSub_classify : ∀ n < 256, n % 2 = 1 → dSubClosed n = true → n ∈ dSubList := by
  decide +kernel

theorem dSub_lt : ∀ n ∈ dSubList, ∀ a ∈ dSubBasis n, a < 2 ^ 11 := by decide +kernel

theorem dSub_nodup : ∀ n ∈ dSubList, (combos (dSubBasis n)).Nodup := by decide +kernel

theorem dSub_rank : ∀ n ∈ dSubList,
    ∃ k < 5, 1 ≤ k ∧ 2 * dSubCard n = 2 ^ k ∧ (dSubBasis n).length + k = 8 := by
  decide +kernel

theorem actM_dCols {u : ℕ} (hu : u < 16) {m : ℕ} (hm : m < 2 ^ 11) :
    actM (dCols u) m = actC11 (dArr u) m := by
  rw [← dCols_eq u hu]
  exact actM_matOf (xorLin_actC11 _) 11 m hm

theorem dSub_basis_fixed : ∀ n ∈ dSubList, ∀ m ∈ combos (dSubBasis n), ∀ u < 16,
    dSubMem n u = true → actM (dCols u) m = m := by
  decide +kernel

theorem dSub_fixed_mem : ∀ n ∈ dSubList, ∀ m < 2 ^ 11,
    (∀ u < 16, dSubMem n u = true → actM (dCols u) m = m) → m ∈ combos (dSubBasis n) := by
  decide +kernel

theorem dSub_fixed : ∀ n ∈ dSubList, ∀ m < 2 ^ 11,
    ((∀ u < 16, dSubMem n u = true → actC11 (dArr u) m = m) ↔ m ∈ combos (dSubBasis n)) := by
  intro n hn m hm
  constructor
  · intro h
    refine dSub_fixed_mem n hn m hm fun u hu hmem => ?_
    rw [actM_dCols hu hm]
    exact h u hu hmem
  · intro h u hu hmem
    rw [← actM_dCols hu hm]
    exact dSub_basis_fixed n hn m h u hu hmem

end CFSG.ASVolI.H16

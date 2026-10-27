module

public import CFSG.Monster.B.Rep4371.TauRow

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Rep4371

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess

theorem mem_oddCodes_iff (a : ℕ) :
    a ∈ Model.oddCodes.toList ↔
      a < 4096 ∧ a % 2 = 0 ∧ (Model.wordN a).testBit 0 = (Model.wordN a).testBit 1 := by
  simp only [Model.oddCodes, Model.oddCodesOf, List.toList_toArray, List.mem_filter, List.mem_map,
    List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, h⟩
    exact ⟨by omega, by omega, h⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨a / 2, by omega, by omega⟩, h3⟩

theorem oddCodes_sorted : Model.oddCodes.toList.Pairwise (· < ·) := by
  rw [Model.oddCodes, Model.oddCodesOf, List.toList_toArray]
  refine List.Pairwise.filter _ ?_
  rw [List.pairwise_map]
  exact List.pairwise_lt_range.imp fun h => by omega

theorem oddCodes_size : Model.oddCodes.size = 1024 := by decide +kernel

theorem mem_octCoeffs_iff (a : ℕ) :
    a ∈ Model.octCoeffs.toList ↔
      a < 4096 ∧ Model.popcN 24 (Model.wordN a) = 8 ∧ Model.wordN a % 4 = 3 := by
  simp only [Model.octCoeffs, Model.octCoeffsOf, List.toList_toArray, List.mem_mergeSort,
    List.mem_filter, List.mem_range, Bool.and_eq_true, beq_iff_eq]

theorem octCoeffs_sorted : (Model.octCoeffs.toList.map Model.wordN).Pairwise (· ≤ ·) := by
  rw [Model.octCoeffs, Model.octCoeffsOf, List.toList_toArray, List.pairwise_map]
  have h := List.pairwise_mergeSort (le := fun a b => decide (Model.wordN a ≤ Model.wordN b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
    ((List.range 4096).filter fun a => Model.popcN 24 (Model.wordN a) == 8 &&
      Model.wordN a % 4 == 3)
  exact h.imp fun h' => by simpa using h'

theorem Rraw_description :
    Rraw 0 = inA (basisA s(0, 0) - basisA s(1, 1)) ∧
    (∀ j : Fin 24, 2 ≤ (j : ℕ) →
      Rraw ((j : ℕ) - 1) = inA (basisA s(0, j) - basisA s(1, j)) ∧
      Rraw (23 + 2 * ((j : ℕ) - 2)) = inX (Xlift (rMinus 0 j) - Xlift (rMinus 1 j)) ∧
      Rraw (24 + 2 * ((j : ℕ) - 2)) = inX (Xlift (rPlus 0 j) - Xlift (rPlus 1 j))) ∧
    (∀ t < 1024, Rraw (67 + t) = inX (Xlift (rOdd (oddC t) 0) - Xlift (rOdd (oddC t) 1))) ∧
    (∀ b < 77, ∀ i < 16, Rraw (1091 + 16 * b + i) =
      inX (Xlift (rOct (octC b) (octSet b (Model.localPairs[i]!).1)) -
        Xlift (rOct (octC b) (octSet b (Model.localPairs[i]!).2)))) ∧
    (∀ t < 1024, Rraw (2323 + t) = inW (tensor (E 0 (oddC t)) wvec) ∧
      Rraw (3347 + t) = inW (tensor (E 1 (oddC t)) wvec)) := by
  have hf : ∀ j : Fin 24, 2 ≤ (j : ℕ) → fin24 (((j : ℕ) - 2) + 2) = j := fun j hj =>
    Fin.ext (by rw [fin24]; simp only; omega)
  refine ⟨rfl, fun j hj => ⟨?_, ?_, ?_⟩, fun t ht => ?_, fun b hb i hi => ?_, fun t ht => ⟨?_, ?_⟩⟩
  · rw [Rraw_A_eq (by omega) (by omega), show (j : ℕ) - 1 + 1 = ((j : ℕ) - 2) + 2 by omega,
      hf j hj]
    rfl
  · rw [Rraw_D_eq (by omega) (by omega) (by omega),
      show (23 + 2 * ((j : ℕ) - 2) - 23) / 2 = (j : ℕ) - 2 by omega, hf j hj]
    rfl
  · rw [Rraw_P_eq (by omega) (by omega) (by omega),
      show (24 + 2 * ((j : ℕ) - 2) - 23) / 2 = (j : ℕ) - 2 by omega, hf j hj]
    rfl
  · rw [Rraw_odd_eq (by omega) (by omega), Nat.add_sub_cancel_left]
    rfl
  · rw [Rraw_oct_eq (by omega) (by omega), show (1091 + 16 * b + i - 1091) / 16 = b by omega,
      show (1091 + 16 * b + i - 1091) % 16 = i by omega]
    rfl
  · rw [Rraw_spin_eq (by omega), ite_eq_right (by omega : ¬ 3347 ≤ 2323 + t),
      show (2323 + t - 2323) % 1024 = t by omega]
    rfl
  · rw [Rraw_spin_eq (by omega), ite_eq_left (by omega : 3347 ≤ 3347 + t),
      show (3347 + t - 2323) % 1024 = t by omega]
    rfl

end CFSG.Monster.B.Rep4371

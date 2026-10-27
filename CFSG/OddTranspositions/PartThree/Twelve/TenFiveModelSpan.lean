module

public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveModelBridge
public import Mathlib.Data.Fin.SuccPred

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal

set_option backward.isDefEq.respectTransparency false

theorem fiveForm_eq_dotProduct (k : ℕ) (ε : Bool) (x y : Fin (k + 1) → ZMod 5) :
    fiveForm k ε x y = x ⬝ᵥ fiveFormVec k ε y := by
  unfold fiveForm fiveFormVec dotProduct
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.castSucc_ne_last, ↓reduceIte]
  ring

theorem fiveQ_single (k : ℕ) (ε : Bool) (i : Fin (k + 1)) :
    fiveQ k ε (Pi.single i 1) = fiveWeight k ε i := by
  rw [fiveQ, QuadraticMap.weightedSumSquares_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem fiveQ_add_single_smul (k : ℕ) (ε : Bool) {i j : Fin (k + 1)} (hij : i ≠ j)
    (c : ZMod 5) :
    fiveQ k ε (Pi.single i 1 + c • Pi.single j 1) =
      fiveWeight k ε i + c ^ 2 * fiveWeight k ε j := by
  rw [fiveQ, QuadraticMap.weightedSumSquares_apply]
  simp_rw [smul_eq_mul]
  have hpoint : ∀ l : Fin (k + 1), fiveWeight k ε l *
        ((((Pi.single i 1 : Fin (k + 1) → ZMod 5) +
          c • (Pi.single j 1 : Fin (k + 1) → ZMod 5)) l) *
         (((Pi.single i 1 : Fin (k + 1) → ZMod 5) +
          c • (Pi.single j 1 : Fin (k + 1) → ZMod 5)) l)) =
      (if l = i then fiveWeight k ε i else 0) +
        (if l = j then c ^ 2 * fiveWeight k ε j else 0) := by
    intro l
    by_cases hli : l = i
    · rw [hli, if_pos rfl, if_neg hij]
      simp [Pi.single_apply, hij, smul_eq_mul]
    · by_cases hlj : l = j
      · rw [hlj, if_neg (Ne.symm hij), if_pos rfl]
        simp [Pi.single_apply, Ne.symm hij, smul_eq_mul]
        ring
      · rw [if_neg hli, if_neg hlj]
        simp [Pi.single_apply, hli, hlj, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun l _ => hpoint l), Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

theorem fiveForm_single_single (k : ℕ) (ε : Bool) (i j : Fin (k + 1)) :
    fiveForm k ε (Pi.single i 1) (Pi.single j 1) =
      if i = j then fiveWeight k ε i else 0 := by
  rw [fiveForm_eq_dotProduct, dotProduct, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, one_mul]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      simp only [fiveFormVec, fiveWeight, Pi.single_eq_same, mul_one]
    · rw [if_neg hij]
      simp only [fiveFormVec, Pi.single_apply]
      split_ifs <;> ring
  · intro l _ hl
    simp [Pi.single_apply, hl]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem fiveForm_sq_eq_two (k : ℕ) (ε : Bool) {i j : Fin (k + 1)} (hij : i ≠ j) :
    fiveForm k ε (Pi.single i 1 + Pi.single j 1) (Pi.single i 1 + Pi.single j 1) =
      fiveWeight k ε i + fiveWeight k ε j := by
  rw [← fiveQ_apply]
  have hh := fiveQ_add_single_smul k ε hij (1 : ZMod 5)
  simpa only [one_smul, one_pow, one_mul] using hh

theorem fiveForm_sq_sub (k : ℕ) (ε : Bool) {i j : Fin (k + 1)} (hij : i ≠ j) :
    fiveForm k ε (Pi.single i 1 - Pi.single j 1) (Pi.single i 1 - Pi.single j 1) =
      fiveWeight k ε i + fiveWeight k ε j := by
  have h : Pi.single i 1 - Pi.single j 1 =
      Pi.single i 1 + (-1 : ZMod 5) • Pi.single j 1 := by
    funext l
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg,
      mul_neg_one]
    ring_nf
  rw [h, ← fiveQ_apply, fiveQ_add_single_smul k ε hij (-1)]
  ring_nf

theorem fiveForm_single_self_eq_fiveWeight (k : ℕ) (ε : Bool) (i : Fin (k + 1)) :
    fiveForm k ε (Pi.single i 1) (Pi.single i 1) = fiveWeight k ε i := by
  rw [fiveForm_single_single, if_pos rfl]

theorem fiveWeight_zero (k : ℕ) (ε : Bool) (hk : 0 < k) :
    fiveWeight k ε (0 : Fin (k + 1)) = 1 := by
  rw [fiveWeight, if_neg]
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

theorem fiveForm_sq_add_smul (k : ℕ) (ε : Bool) {i j : Fin (k + 1)} (hij : i ≠ j)
    (c : ZMod 5) :
    fiveForm k ε (Pi.single i 1 + c • Pi.single j 1)
      (Pi.single i 1 + c • Pi.single j 1) =
      fiveWeight k ε i + c ^ 2 * fiveWeight k ε j := by
  rw [← fiveQ_apply, fiveQ_add_single_smul k ε hij c]

theorem isSquare_one_zmod5 : IsSquare (1 : ZMod 5) := ⟨1, by decide⟩

theorem not_isSquare_two_zmod5 : ¬ IsSquare (2 : ZMod 5) := by decide

end CFSG.OddTranspositions.PartThree

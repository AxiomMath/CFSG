module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDStdModel
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1GenComb

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.PhanDn.QTwo CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits

theorem qtwoLabel_self (n : ℕ) (i : Fin n) : CFSG.StandardType.ggCoxeterMatrixD n i i = 1 := by
  rw [CFSG.StandardType.ggCoxeterMatrixD_apply, if_pos rfl]

theorem qtwoLabel_three_iff {m : ℕ} (hm : 3 ≤ m) (i j : Fin (m + 1)) :
    CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 3 ↔
      (j.val = i.val + 1 ∧ j.val ≤ m - 1) ∨ (i.val = j.val + 1 ∧ i.val ≤ m - 1) ∨
        (i.val + 2 = m ∧ j.val = m) ∨ (j.val + 2 = m ∧ i.val = m) := by
  rw [CFSG.StandardType.OrthTorus.ggCoxeterMatrixD_eq_three_iff (by omega : 3 ≤ m + 1) i j]
  omega

theorem qtwoLabel_two_iff {m : ℕ} (hm : 3 ≤ m) (i j : Fin (m + 1)) (hij : i ≠ j) :
    CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 2 ↔
      ¬ ((j.val = i.val + 1 ∧ j.val ≤ m - 1) ∨ (i.val = j.val + 1 ∧ i.val ≤ m - 1) ∨
        (i.val + 2 = m ∧ j.val = m) ∨ (j.val + 2 = m ∧ i.val = m)) := by
  rw [← qtwoLabel_three_iff hm i j]
  rcases ggCoxeterMatrixD_two_or_three i j hij with h | h <;> rw [h] <;> decide

section Window

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]

@[expose] noncomputable def qtwoStdWin (m a len : ℕ) (h : a + len ≤ m + 1) :
    Su K 2 1 len →* ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) :=
  (suEndN (F := F) (unitaryInvolution K 2 1) (m + 1)).comp (blockEmb K 2 1 (m + 1) len a h)

variable (E : QuadExt F K (unitaryInvolution K 2 1)) (m : ℕ) (hm : 3 ≤ m)

theorem qtwoStdU_castSucc (k : Fin m) :
    qtwoStdU E m hm (Fin.castSucc k) =
      (qtwoStdWin (F := F) (K := K) m k.val 2 (by omega)).range := by
  unfold qtwoStdU
  rw [stdFamilyV_ι_castSucc]
  unfold stdChainIota qtwoStdWin
  rfl

theorem qtwoStdU_last :
    qtwoStdU E m hm (Fin.last m) =
      (qtwoStdWin (F := F) (K := K) m (m - 1) 2 (by omega)).range.map
        (stdConj E m).toMonoidHom := by
  unfold qtwoStdU
  rw [stdFamilyV_ι_last]
  unfold stdForkIota
  rw [MonoidHom.range_comp]
  unfold stdChainIota qtwoStdWin
  rfl

theorem qtwoStdW_chain (a : ℕ) (ha : a + 2 ≤ m) (i j : Fin (m + 1)) (hi : i.val = a)
    (hj : j.val = a + 1) :
    qtwoStdW E m hm i j = (qtwoStdWin (F := F) (K := K) m a 3 (by omega)).range := by
  obtain ⟨ai, hilt_i⟩ := i
  obtain ⟨aj, hilt_j⟩ := j
  have hi' : ai = a := hi
  have hj' : aj = a + 1 := hj
  subst ai
  subst aj
  have hlabel : CFSG.StandardType.ggCoxeterMatrixD (m + 1) (⟨a, hilt_i⟩ : Fin (m + 1))
      (⟨a + 1, hilt_j⟩ : Fin (m + 1)) = 3 := by
    rw [qtwoLabel_three_iff hm]
    exact Or.inl ⟨by show a + 1 = a + 1; omega, by show a + 1 ≤ m - 1; omega⟩
  have hlt : (⟨a, hilt_i⟩ : Fin (m + 1)) < (⟨a + 1, hilt_j⟩ : Fin (m + 1)) := by
    rw [Fin.lt_def]
    show a < a + 1
    omega
  have hjcast : (⟨a + 1, hilt_j⟩ : Fin (m + 1)) =
      Fin.castSucc (⟨a + 1, by omega⟩ : Fin m) := rfl
  unfold qtwoStdW
  rw [if_pos hlabel, if_pos hlt, stdFamilyV_θ]
  conv_lhs => rw [hjcast]
  rw [stdTheta_castSucc]
  unfold stdThetaAt
  rw [dif_pos (by show a + 1 = a + 1; omega)]
  unfold stdChainTheta qtwoStdWin
  rfl

theorem qtwoStdW_fork (i j : Fin (m + 1)) (hi : i.val = m - 2) (hj : j.val = m) :
    qtwoStdW E m hm i j =
      (qtwoStdWin (F := F) (K := K) m (m - 2) 3 (by omega)).range.map
        (stdConj E m).toMonoidHom := by
  obtain ⟨ai, hilt_i⟩ := i
  obtain ⟨aj, hilt_j⟩ := j
  have hi' : ai = m - 2 := hi
  have hj' : aj = m := hj
  subst ai
  subst aj
  have hlabel : CFSG.StandardType.ggCoxeterMatrixD (m + 1) (⟨m - 2, hilt_i⟩ : Fin (m + 1))
      (⟨m, hilt_j⟩ : Fin (m + 1)) = 3 := by
    rw [qtwoLabel_three_iff hm]
    exact Or.inr (Or.inr (Or.inl ⟨by show m - 2 + 2 = m; omega, by show m = m; omega⟩))
  have hlt : (⟨m - 2, hilt_i⟩ : Fin (m + 1)) < (⟨m, hilt_j⟩ : Fin (m + 1)) := by
    rw [Fin.lt_def]
    show m - 2 < m
    omega
  have hjlast : (⟨m, hilt_j⟩ : Fin (m + 1)) = Fin.last m := rfl
  unfold qtwoStdW
  rw [if_pos hlabel, if_pos hlt, stdFamilyV_θ]
  conv_lhs => rw [hjlast]
  rw [stdTheta_last]
  unfold stdForkTheta
  rw [MonoidHom.range_comp]
  unfold stdChainTheta qtwoStdWin
  rfl

theorem qtwoStdW_symm (i j : Fin (m + 1)) : qtwoStdW E m hm i j = qtwoStdW E m hm j i := by
  by_cases hij : i = j
  · rw [hij]
  have hsymm : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j =
      CFSG.StandardType.ggCoxeterMatrixD (m + 1) j i :=
    ((CFSG.StandardType.ggCoxeterMatrixD (m + 1)).isSymm.apply i j).symm
  by_cases h3 : CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 3
  · have h3' : CFSG.StandardType.ggCoxeterMatrixD (m + 1) j i = 3 := by
      rw [← hsymm]; exact h3
    unfold qtwoStdW
    rw [if_pos h3, if_pos h3']
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · rw [if_pos hlt, if_neg (not_lt_of_gt hlt)]
    · rw [if_neg (not_lt_of_gt hlt), if_pos hlt]
  · have h3' : CFSG.StandardType.ggCoxeterMatrixD (m + 1) j i ≠ 3 := by
      intro h
      exact h3 (by rw [hsymm]; exact h)
    unfold qtwoStdW
    rw [if_neg h3, if_neg h3']
    exact sup_comm _ _

end Window

end CFSG.StandardType.QTwo

end

module

public import CFSG.RankThree.PartTwo.Sec6.Item611Res5ProofL43Data
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import CFSG.RankThree.PartTwo.Sec6.Item611Res5ProofL43Cent

public section

namespace CFSG.RankThree.PartTwo.Sec6.Res611Res5.L43

open Matrix CFSG.RankThree.PartTwo.Sec4.Item434RemL43
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem exists_conj_rep {a b c d e f : ZMod 3} (h3 : a * d * f = 0)
    (h1 : ¬(a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0)) :
    ∃ (g h : Mat4) (M : SL4), (M = zSL ∨ M = u2SL ∨ M = u3SL) ∧ g * h = 1 ∧
      g * uuMat a b c d e f = (M : Mat4) * g := by
  obtain ⟨hk, hgh, hg⟩ := table_check a b c d e f h3 h1
  rcases hk with hk | hk | hk <;> rw [hk] at hg
  · exact ⟨_, _, zSL, Or.inl rfl, hgh, hg⟩
  · exact ⟨_, _, u2SL, Or.inr (Or.inl rfl), hgh, hg⟩
  · exact ⟨_, _, u3SL, Or.inr (Or.inr rfl), hgh, hg⟩

theorem val_eq_uuMat {u : SL4} (hu : u ∈ unitriangular 4 (ZMod 3)) :
    (u : Mat4) = uuMat ((u : Mat4) 0 1) ((u : Mat4) 0 2) ((u : Mat4) 0 3) ((u : Mat4) 1 2)
      ((u : Mat4) 1 3) ((u : Mat4) 2 3) := by
  obtain ⟨hlow, hdiag⟩ := mem_unitriangular.mp hu
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uuMat, hdiag, hlow 1 0 (by decide), hlow 2 0 (by decide), hlow 2 1 (by decide),
      hlow 3 0 (by decide), hlow 3 1 (by decide), hlow 3 2 (by decide)]

theorem uuMat_cube_entry (a b c d e f : ZMod 3) : (uuMat a b c d e f ^ 3) 0 3 = a * d * f := by
  simp [pow_three, uuMat, Matrix.mul_apply, Fin.sum_univ_four]
  linear_combination (c + a * e + b * f) * three_eq_zero

theorem card_centralizer_of_mem_unitriangular {u : SL4} (hu : u ∈ unitriangular 4 (ZMod 3))
    (h3 : u ^ 3 = 1) (h1 : u ≠ 1) :
    Nat.card (Subgroup.centralizer ({u} : Set SL4)) = 11664 ∨
      Nat.card (Subgroup.centralizer ({u} : Set SL4)) = 3888 ∨
      Nat.card (Subgroup.centralizer ({u} : Set SL4)) = 162 := by
  have hval := val_eq_uuMat hu
  have hadf : (u : Mat4) 0 1 * (u : Mat4) 1 2 * (u : Mat4) 2 3 = 0 := by
    have h : ((u : Mat4) ^ 3) 0 3 = (1 : Mat4) 0 3 :=
      congrFun (congrFun (congrArg (fun x : SL4 => (x : Mat4)) h3) 0) 3
    rw [hval, uuMat_cube_entry] at h
    simpa using h
  have hne : ¬((u : Mat4) 0 1 = 0 ∧ (u : Mat4) 0 2 = 0 ∧ (u : Mat4) 0 3 = 0 ∧
      (u : Mat4) 1 2 = 0 ∧ (u : Mat4) 1 3 = 0 ∧ (u : Mat4) 2 3 = 0) := by
    rintro ⟨ha, hb, hc, hd, he, hf⟩
    apply h1
    ext i j
    rw [hval, ha, hb, hc, hd, he, hf]
    fin_cases i <;> fin_cases j <;> rfl
  obtain ⟨g, h, M, hM, hgh, hg⟩ := exists_conj_rep hadf hne
  rw [← hval] at hg
  rw [card_centralizer_conj hgh hg]
  rcases hM with rfl | rfl | rfl
  · exact Or.inl card_centralizer_zSL
  · exact Or.inr (Or.inl card_centralizer_u2SL)
  · exact Or.inr (Or.inr card_centralizer_u3SL)

end CFSG.RankThree.PartTwo.Sec6.Res611Res5.L43

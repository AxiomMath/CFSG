module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LinearAlgebra.IntegralCongruenceTorsionFree
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.StandardType

@[expose] def ggPathPar (k : ℕ) (i : Fin k) : Fin k :=
  ⟨i.1 - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.2⟩

theorem ggCartanC_pathTree {k : ℕ} (root : Fin k) (hroot : root.1 = 0) :
    (∀ i j, CoxeterMatrix.B k i j ≠ 6) ∧
      (∀ i j : Fin k, i ≠ j → (CartanMatrix.C k i j ≠ 0 ↔
        ((i ≠ root ∧ ggPathPar k i = j) ∨ (j ≠ root ∧ ggPathPar k j = i)))) ∧
      (∀ i : Fin k, i ≠ root → (ggPathPar k i).1 < i.1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    simp only [CoxeterMatrix.B, Matrix.of_apply]
    split_ifs <;> omega
  · intro i j hij
    have hpar : ∀ x y : Fin k, ggPathPar k x = y ↔ x.1 - 1 = y.1 := by
      intro x y
      constructor
      · intro h
        have := congrArg Fin.val h
        simpa [ggPathPar] using this
      · intro h
        apply Fin.ext
        simpa [ggPathPar] using h
    have hC : CartanMatrix.C k i j ≠ 0 ↔ i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 := by
      simp only [CartanMatrix.C, Matrix.of_apply]
      rw [if_neg hij]
      constructor
      · intro h
        by_cases h1 : i.1 + 1 = j.1
        · exact Or.inl h1
        · rw [if_neg h1] at h
          by_cases h2 : j.1 + 1 = i.1
          · exact Or.inr h2
          · rw [if_neg h2] at h
            exact absurd rfl h
      · intro h
        rcases h with h1 | h2
        · rw [if_pos h1]
          norm_num
        · rw [if_neg (by omega : ¬ i.1 + 1 = j.1), if_pos h2]
          split_ifs <;> omega
    have hrel : ((i ≠ root ∧ ggPathPar k i = j) ∨ (j ≠ root ∧ ggPathPar k j = i)) ↔
        (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) := by
      constructor
      · rintro (⟨hir, hpar_eq⟩ | ⟨hjr, hpar_eq⟩)
        · right
          have hi0 : i.1 ≠ 0 := fun h => hir (Fin.ext (h.trans hroot.symm))
          have := (hpar i j).1 hpar_eq
          omega
        · left
          have hj0 : j.1 ≠ 0 := fun h => hjr (Fin.ext (h.trans hroot.symm))
          have := (hpar j i).1 hpar_eq
          omega
      · rintro (h1 | h2)
        · right
          refine ⟨?_, (hpar j i).2 ?_⟩
          · intro h
            have : j.1 = 0 := by rw [h, hroot]
            omega
          · omega
        · left
          refine ⟨?_, (hpar i j).2 ?_⟩
          · intro h
            have : i.1 = 0 := by rw [h, hroot]
            omega
          · omega
    exact hC.trans hrel.symm
  · intro i hi
    have hi0 : i.1 ≠ 0 := fun h => hi (Fin.ext (h.trans hroot.symm))
    show i.1 - 1 < i.1
    omega

end CFSG.StandardType

end

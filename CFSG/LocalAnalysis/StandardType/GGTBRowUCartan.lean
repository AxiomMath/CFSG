module

public import CFSG.LocalAnalysis.StandardType.GGTBRowSpCartan

public section

namespace CFSG.StandardType

theorem ggCartanA_pathTree {k : ℕ} (root : Fin k) (hroot : root.1 = 0) :
    (∀ i j, CoxeterMatrix.A k i j ≠ 6) ∧
      (∀ i j : Fin k, i ≠ j → (CartanMatrix.A k i j ≠ 0 ↔
        ((i ≠ root ∧ ggPathPar k i = j) ∨ (j ≠ root ∧ ggPathPar k j = i)))) ∧
      (∀ i : Fin k, i ≠ root → (ggPathPar k i).1 < i.1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    simp only [CoxeterMatrix.A, Matrix.of_apply]
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
    have hC : CartanMatrix.A k i j ≠ 0 ↔ i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 := by
      simp only [CartanMatrix.A, Matrix.of_apply]
      rw [if_neg hij]
      by_cases h : i.1 + 1 = j.1 ∨ j.1 + 1 = i.1
      · rw [if_pos h]
        exact ⟨fun _ => h, fun _ => by norm_num⟩
      · rw [if_neg h]
        exact ⟨fun h0 => absurd rfl h0, fun h0 => absurd h0 h⟩
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

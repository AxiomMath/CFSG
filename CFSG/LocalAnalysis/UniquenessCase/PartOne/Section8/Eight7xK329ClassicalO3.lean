module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329Data
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329SplitAssembly
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329SplitOmega
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329SplitPSL
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329SplitPSU
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329SplitSp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel classicalTags)
open CFSG.Open (StatedLieTag)
open CFSG.Open (StatedOmega StatedQuadMinus StatedQuadPlus StatedSL StatedSp StatedSU)

@[expose] def k329ClassicalO3NoDatum (t : StatedLieTag) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    ∀ n : ℕ, LieModel S t n 2 3 → ∀ u : S, ¬ K329UDatum S u

theorem k329_classicalO3_PSL : k329ClassicalO3NoDatum .PSL := by
  intro S _ _ _ n hL u hu
  obtain ⟨hadm, K, _, _, hK, ⟨eqv⟩⟩ := hL.statedClassicalModel (by simp [classicalTags])
  exact k329_O3_of_matrix (StatedSL n K) False (k329_S3c_PSL n hadm K hK)
    (k329_S4_PSL n hadm K hK) (k329_S5_PSL n hadm K hK) eqv hu

theorem k329_classicalO3_PSp : k329ClassicalO3NoDatum .PSp := by
  intro S _ _ _ n hL u hu
  obtain ⟨hadm, K, _, _, hK, ⟨eqv⟩⟩ := hL.statedClassicalModel (by simp [classicalTags])
  exact k329_O3_of_matrix (StatedSp n K) False (k329_S3c_PSp n hadm K hK)
    (k329_S4_PSp n hadm K hK) (k329_S5_PSp n hadm K) eqv hu

theorem k329_classicalO3_POmegaPlus : k329ClassicalO3NoDatum .POmegaPlus := by
  intro S _ _ _ n hL u hu
  obtain ⟨hadm, K, _, _, hK, ⟨eqv⟩⟩ := hL.statedClassicalModel (by simp [classicalTags])
  exact k329_O3_of_matrix (StatedOmega (StatedQuadPlus n K)) False
    (k329_S3c_POmegaPlus n hadm K hK) (k329_S4_POmegaPlus n hadm K hK)
    (k329_S5_POmegaPlus n hadm K) eqv hu

theorem k329_classicalO3_POmegaMinus : k329ClassicalO3NoDatum .POmegaMinus := by
  intro S _ _ _ n hL u hu
  obtain ⟨hadm, K, _, _, hK, b, c, hbc, ⟨eqv⟩⟩ :=
    hL.statedClassicalModel (by simp [classicalTags])
  exact k329_O3_of_matrix (StatedOmega (StatedQuadMinus n K b c)) False
    (k329_S3c_POmegaMinus n hadm K hK b c hbc) (k329_S4_POmegaMinus n hadm K hK b c hbc)
    (k329_S5_POmegaMinus n K b c) eqv hu

theorem k329_classicalO3_POmegaOdd : k329ClassicalO3NoDatum .POmegaOdd := by
  intro S _ _ _ n hL u _
  exact absurd rfl hL.admissible.2.2.2

theorem k329_classicalO3_PSU :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
      ∀ n : ℕ, LieModel S .PSU n 2 3 → ∀ u : S, K329UDatum S u → n = 3 := by
  intro S _ _ _ n hL u hu
  obtain ⟨hadm, K, _, _, hK, ⟨eqv⟩⟩ := hL.statedClassicalModel (by simp [classicalTags])
  exact k329_O3_of_matrix (StatedSU n (2 ^ 3) K) (n = 3) (k329_S3c_PSU n hadm K hK)
    (k329_S4_PSU n hadm K hK) (k329_S5_PSU n hadm K hK) eqv hu

theorem k329ClassicalO3_of_families (hL : k329ClassicalO3NoDatum .PSL)
    (hSp : k329ClassicalO3NoDatum .PSp)
    (hOO : k329ClassicalO3NoDatum .POmegaOdd) (hOP : k329ClassicalO3NoDatum .POmegaPlus)
    (hOM : k329ClassicalO3NoDatum .POmegaMinus) : k329ClassicalO3Statement := by
  have hU := k329_classicalO3_PSU
  intro S _ _ hS t n ht hLie u hu
  have h : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨
      t = .POmegaMinus := by
    simpa [classicalTags] using ht
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hu (hL S hS n hLie u)
  · exact ⟨rfl, hU S hS n hLie u hu⟩
  · exact absurd hu (hSp S hS n hLie u)
  · exact absurd hu (hOO S hS n hLie u)
  · exact absurd hu (hOP S hS n hLie u)
  · exact absurd hu (hOM S hS n hLie u)

theorem k329_classicalO3 : k329ClassicalO3Statement :=
  k329ClassicalO3_of_families k329_classicalO3_PSL k329_classicalO3_PSp
    k329_classicalO3_POmegaOdd k329_classicalO3_POmegaPlus k329_classicalO3_POmegaMinus

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

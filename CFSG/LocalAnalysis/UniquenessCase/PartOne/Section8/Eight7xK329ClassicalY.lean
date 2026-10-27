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
open CFSG.Open (StatedOmega StatedQuadMinus StatedQuadOdd StatedQuadPlus StatedSL StatedSp StatedSU)

@[expose] def k329ClassicalYFamily (t : StatedLieTag) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    ∀ (n r e : ℕ), LieModel S t n r e → r ≠ 3 → ∀ z : S, K329ZDatum S z → r ^ e = 8

theorem k329ClassicalY_of_families (h : ∀ t ∈ classicalTags, k329ClassicalYFamily t) :
    k329ClassicalYStatement :=
  fun S _ _ hS t n r e ht hL hr z hz => h t ht S hS n r e hL hr z hz

theorem k329_classicalY_PSL : k329ClassicalYFamily .PSL := by
  intro S _ _ _ n r e hL hr z hz
  obtain ⟨hadm, K, _, _, hK, ⟨eqv⟩⟩ := hL.statedClassicalModel (by simp [classicalTags])
  exact k329_Y_of_matrix (StatedSL n K) (r ^ e) (k329_S3f_PSL n r e hadm hr K hK) eqv hz

theorem k329_classicalY_PSU : k329ClassicalYFamily .PSU := by
  intro S _ _ _ n r e hL hr z hz
  obtain ⟨hadm, K, _, _, hK, ⟨eqv⟩⟩ := hL.statedClassicalModel (by simp [classicalTags])
  exact k329_Y_of_matrix (StatedSU n (r ^ e) K) (r ^ e) (k329_S3f_PSU n r e hadm hr K hK) eqv hz

theorem k329_classicalY_PSp : k329ClassicalYFamily .PSp := by
  intro S _ _ _ n r e hL hr z hz
  obtain ⟨hadm, K, _, _, hK, ⟨eqv⟩⟩ := hL.statedClassicalModel (by simp [classicalTags])
  exact k329_Y_of_matrix (StatedSp n K) (r ^ e) (k329_S3f_PSp n r e hadm hr K hK) eqv hz

theorem k329_classicalY_POmegaOdd : k329ClassicalYFamily .POmegaOdd := by
  intro S _ _ _ n r e hL hr z hz
  obtain ⟨hadm, K, _, _, hK, ⟨eqv⟩⟩ := hL.statedClassicalModel (by simp [classicalTags])
  exact k329_Y_of_matrix (StatedOmega (StatedQuadOdd n K)) (r ^ e)
    (k329_S3f_POmegaOdd n r e hadm hr K hK) eqv hz

theorem k329_classicalY_POmegaPlus : k329ClassicalYFamily .POmegaPlus := by
  intro S _ _ _ n r e hL hr z hz
  obtain ⟨hadm, K, _, _, hK, ⟨eqv⟩⟩ := hL.statedClassicalModel (by simp [classicalTags])
  exact k329_Y_of_matrix (StatedOmega (StatedQuadPlus n K)) (r ^ e)
    (k329_S3f_POmegaPlus n r e hadm hr K hK) eqv hz

theorem k329_classicalY_POmegaMinus : k329ClassicalYFamily .POmegaMinus := by
  intro S _ _ _ n r e hL hr z hz
  obtain ⟨hadm, K, _, _, hK, b, c, hbc, ⟨eqv⟩⟩ :=
    hL.statedClassicalModel (by simp [classicalTags])
  exact k329_Y_of_matrix (StatedOmega (StatedQuadMinus n K b c)) (r ^ e)
    (k329_S3f_POmegaMinus n r e hadm hr K hK b c hbc) eqv hz

theorem k329_classicalY : k329ClassicalYStatement := by
  refine k329ClassicalY_of_families fun t ht => ?_
  have h : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨
      t = .POmegaMinus := by
    simpa [classicalTags] using ht
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact k329_classicalY_PSL
  · exact k329_classicalY_PSU
  · exact k329_classicalY_PSp
  · exact k329_classicalY_POmegaOdd
  · exact k329_classicalY_POmegaPlus
  · exact k329_classicalY_POmegaMinus

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

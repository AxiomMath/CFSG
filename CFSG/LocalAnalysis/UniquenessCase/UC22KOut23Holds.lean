module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineKOut
public import CFSG.GH74.Generic.S3.L3Out
public import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Three.Aut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.JankoOne
public import CFSG.Blueprint.LieModelAPI
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz

public section

open scoped MatrixGroups

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.SignalizerFunctorTheorem.McBride.PSL2Three (perfect_le_range_conj)
open CFSG.RankThree.PartTwo.KFacts (commutator_le_inner_of_suzukiModel)

theorem perfectInInn_psl_two (F : Type) [Field F] [Finite F] :
    PerfectInInn (PSL(2, F)) := by
  intro P hP
  have hperf : Group.IsPerfect P := Subgroup.isPerfect_iff.mpr hP
  simpa [CFSG.ComponentClassification.OuterAutomorphisms.inner]
    using perfect_le_range_conj F P hperf

theorem kOut23_of_sz (hSz : ∀ (S : Type) [Group S] [Finite S] (a : ℕ), IsSz S a → PerfectInInn
    S) : KOut23 := by
  intro S _ _ hshape P hP
  have hout : PerfectInInn S := by
    rcases hshape with ⟨a, hL2 | hSzModel⟩ | ⟨q, hq, hq2, hL2Odd⟩ | hJ1
    · obtain ⟨-, -, F, hField, hFinite, -, ⟨e⟩⟩ := lieModel_psl_data hL2
      letI := hField
      letI := hFinite
      exact PerfectInInn.of_mulEquiv
        (e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm)
        (perfectInInn_psl_two F)
    · exact hSz S a hSzModel
    · obtain ⟨-, -, F, hField, hFinite, -, ⟨e⟩⟩ := lieModel_psl_data hL2Odd
      letI := hField
      letI := hFinite
      exact PerfectInInn.of_mulEquiv
        (e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm)
        (perfectInInn_psl_two F)
    · intro Q _
      intro g _
      obtain ⟨x, hx⟩ := (kJ1_holds S hJ1).2.2 g
      refine ⟨x, ?_⟩
      change MulAut.conj x = g
      exact hx.symm
  simpa [CFSG.ComponentClassification.OuterAutomorphisms.inner]
    using hout P (Subgroup.isPerfect_iff.mp hP)

theorem kOut23_holds : KOut23 := by
  refine kOut23_of_sz fun S _ _ a ha => ?_
  have ha' : LieModel S .twistedB2 0 2 a := ha
  obtain ⟨-, hSz⟩ := ha'.suzukiModel
  intro P hP
  have hle : P ≤ commutator (MulAut S) := by
    rw [← hP]
    exact Subgroup.commutator_mono le_top le_top
  have hcomm : commutator (MulAut S) ≤ (MulAut.conj : S →* MulAut S).range :=
    commutator_le_inner_of_suzukiModel hSz
  simpa [CFSG.ComponentClassification.OuterAutomorphisms.inner] using hle.trans hcomm

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

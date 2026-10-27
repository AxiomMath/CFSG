module

public import CFSG.Quasithin.Background.F7TwoInvSQTKFam
public import CFSG.Quasithin.Background.F7TwoInvL2
public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.LocalAnalysis.ComponentInitial.OddLinearTwoAliases
public import CFSG.Milestones.CL_LIT_SQTK_simple_listBase

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Milestones
open CFSG.LocalAnalysis.ComponentInitial

theorem invAutGen_of_sqtkSimpleList
    (hL3Odd : InvAutGenFamL3Odd) (hU3Odd : InvAutGenFamU3Odd)
    (hL3Even : InvAutGenFamL3Even) (hU3Even : InvAutGenFamU3Even)
    (hSp4 : InvAutGenFamSp4Even) (hG2 : InvAutGenFamG2Even) (h3D4 : InvAutGenFam3D4Even)
    (h2F4 : InvAutGenFam2F4) (hSz : InvAutGenFamSz) (hTits : InvAutGenFamTits)
    (hL5 : InvAutGenFamL5Two) (hSpor : InvAutGenFamSporadic)
    {S : Type} [Group S] [Finite S] (h : SQTKSimpleList S) :
    ∀ φ : MulAut S, φ * φ = 1 → φ ≠ 1 → InvAutGen S φ := by
  intro φ hφ2 hφ1
  have hmem : (StatedLieTag.PSL) ∈ classicalTags := by decide
  rcases h with ⟨n, hn5, hn8, ⟨e⟩⟩ | ⟨p, hp, hp2, ⟨f, -, hm⟩ | hm | hm⟩ |
    ⟨⟨f, ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hfo, hf, hm⟩ |
      ⟨hfo, hf, hm⟩⟩ | hm⟩ | ⟨n, hn, hm⟩ | ⟨s, hs, ⟨e⟩⟩
  · by_cases hn6 : n = 6
    · subst hn6
      have hm6 :=
        statedClassicalModel_psl_two_nine_of_alternating_six S ⟨e⟩
      exact invAutGen_of_statedPSL2 hm6 φ hφ2 hφ1
    · exact invAutGen_of_mulEquiv_alternatingGroup e hn5 hn6 φ hφ2 hφ1
  · exact invAutGen_of_statedPSL2 hm φ hφ2 hφ1
  · exact hL3Odd p S hp hp2 hm φ hφ2 hφ1
  · exact hU3Odd p S hp hp2 hm φ hφ2 hφ1
  · exact invAutGen_of_statedPSL2 hm φ hφ2 hφ1
  · by_cases hf2 : 2 ≤ f
    · exact hL3Even f S hf2 hm φ hφ2 hφ1
    · have hf1 : f = 1 := by omega
      subst hf1
      rcases PSL3_two_PSL2_seven_paired_isomorphism S (Or.inl ⟨hmem, hm⟩) with
        ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
      · exact invAutGen_of_statedPSL2 hc φ hφ2 hφ1
      all_goals exact absurd ht (by decide)
  · exact hU3Even f S hf hm φ hφ2 hφ1
  · exact hSp4 f S hf hm φ hφ2 hφ1
  · exact hG2 f S hf hm φ hφ2 hφ1
  · exact h3D4 f S hf hm φ hφ2 hφ1
  · exact h2F4 f S hfo hf hm φ hφ2 hφ1
  · exact hSz f S hfo hf hm φ hφ2 hφ1
  · exact hTits S hm φ hφ2 hφ1
  · rcases hn with rfl | rfl
    · obtain ⟨e⟩ := CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel
        (G := S) (Or.inl ⟨hmem, hm⟩)
      exact invAutGen_of_mulEquiv_alternatingGroup e (by norm_num) (by norm_num) φ hφ2 hφ1
    · exact hL5 S hm φ hφ2 hφ1
  · exact hSpor s hs S ⟨e⟩ φ hφ2 hφ1

end CFSG.Quasithin.F7Two

module

public import CFSG.LocalAnalysis.StandardType.GGQ2SpStatements
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksMark
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksIso
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksSp
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksSU
import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResU3ThreeSolv
import CFSG.LocalAnalysis.StandardType.MarkingSmall

public section

namespace CFSG.StandardType.GGQ2Frame.SpBlocks

open CFSG.Open (StatedSp)

theorem spIsQuasisimpleYcode_holds : SpIsQuasisimpleYcode := by
  intro K _ _ _ ζ m hK hζ c hc
  obtain ⟨hperf, lab, -, hraw⟩ := spMarkedYcode_holds ζ m hK hζ c hc
  obtain ⟨R, _, -, -, hsimple, hna, θ, -⟩ :=
    largeEvenRawDatum_exists ((largeEvenRawDatum_legacy lab _).mpr hraw)
  have : IsSimpleGroup R := hsimple
  exact ⟨⟨hperf⟩, θ.isSimpleGroup, nonabelian_of_mulEquiv θ.symm hna⟩

theorem not_isComponentOf_commutator_bot {G : Type} [Group G] (X : Subgroup G) :
    ¬ CFSG.Assembly.IsComponentOf X ⁅(⊥ : Subgroup G), ⊥⁆ :=
  CFSG.StandardType.ResU3Three.not_isComponentOf_of_isSolvable
    (by rw [Subgroup.commutator_bot_left]; infer_instance)

theorem spNotIsComponentOfYcode_holds : SpNotIsComponentOfYcode := by
  intro K _ _ _ ζ m hK hζ c hc X
  cases c with
  | zero S =>
    have hS : S.card ≤ 1 := by
      have h : ¬ 2 ≤ S.card := hc
      omega
    rcases S.eq_empty_or_nonempty with rfl | hne
    · change ¬ CFSG.Assembly.IsComponentOf X
        ⁅blockGroup ζ m (.zero ∅), blockGroup ζ m (.zero ∅)⁆
      rw [blockGroup_zero_empty]
      exact not_isComponentOf_commutator_bot X
    · obtain ⟨e⟩ := nonempty_blockGroup_zero_mulEquiv ζ m hK hζ hne
      exact not_isComponentOf_commutator_of_mulEquiv_statedSp hK hS e X
  | extension e =>
    by_cases he : e = 0
    · subst he
      change ¬ CFSG.Assembly.IsComponentOf X
        ⁅blockGroup ζ m (.extension 0), blockGroup ζ m (.extension 0)⁆
      rw [blockGroup_extension_zero]
      exact not_isComponentOf_commutator_bot X
    · have h3 : (PlaneRaw.Code.extSupport e).card ≤ 3 := by
        by_contra h
        exact hc ⟨he, by omega⟩
      obtain ⟨E, _, _, _, hE, ⟨φ⟩⟩ := exists_blockGroup_extension_mulEquiv ζ m hK hζ he
      exact not_isComponentOf_commutator_of_mulEquiv_guFull hE h3 φ X

end CFSG.StandardType.GGQ2Frame.SpBlocks

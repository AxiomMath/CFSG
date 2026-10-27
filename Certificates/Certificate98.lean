module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourActionWitnessesCore

public section

open CFSG CFSG.LargeEvenClassification CFSG.LargeEvenClassification.Helpers

namespace CertificateChecks.Batch98

open CFSG CFSG.LargeEvenClassification CFSG.LargeEvenClassification.Helpers

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

private theorem c8FourActionRecord640_covered : c8FourActionCovered c8FourRecordData640 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨41, ?_⟩
  decide +kernel

private theorem c8FourActionRecord640_bounded : c8FourActionBounded c8FourRecordData640 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord641_covered : c8FourActionCovered c8FourRecordData641 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨42, ?_⟩
  decide +kernel

private theorem c8FourActionRecord641_bounded : c8FourActionBounded c8FourRecordData641 := by
  decide +kernel

private theorem c8FourActionRecord642_covered : c8FourActionCovered c8FourRecordData642 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨41, ?_⟩
  decide +kernel

private theorem c8FourActionRecord642_bounded : c8FourActionBounded c8FourRecordData642 := by
  decide +kernel

private theorem c8FourActionRecord643_covered : c8FourActionCovered c8FourRecordData643 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨42, ?_⟩
  decide +kernel

private theorem c8FourActionRecord643_bounded : c8FourActionBounded c8FourRecordData643 := by
  decide +kernel

private theorem c8FourActionRecord644_covered : c8FourActionCovered c8FourRecordData644 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord644_bounded : c8FourActionBounded c8FourRecordData644 := by
  decide +kernel

private theorem c8FourActionRecord645_covered : c8FourActionCovered c8FourRecordData645 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord645_bounded : c8FourActionBounded c8FourRecordData645 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord646_covered : c8FourActionCovered c8FourRecordData646 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord646_bounded : c8FourActionBounded c8FourRecordData646 := by
  decide +kernel

private theorem c8FourActionRecord647_covered : c8FourActionCovered c8FourRecordData647 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord647_bounded : c8FourActionBounded c8FourRecordData647 := by
  decide +kernel

private theorem c8FourActionRecord648_covered : c8FourActionCovered c8FourRecordData648 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord648_bounded : c8FourActionBounded c8FourRecordData648 := by
  decide +kernel

private theorem c8FourActionRecord649_covered : c8FourActionCovered c8FourRecordData649 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨42, ?_⟩
  decide +kernel

private theorem c8FourActionRecord649_bounded : c8FourActionBounded c8FourRecordData649 := by
  decide +kernel

private theorem c8FourActionRecord650_covered : c8FourActionCovered c8FourRecordData650 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨42, ?_⟩
  decide +kernel

private theorem c8FourActionRecord650_bounded : c8FourActionBounded c8FourRecordData650 := by
  decide +kernel

private theorem c8FourActionRecord651_covered : c8FourActionCovered c8FourRecordData651 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord651_bounded : c8FourActionBounded c8FourRecordData651 := by
  decide +kernel

private theorem c8FourActionRecord652_covered : c8FourActionCovered c8FourRecordData652 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨43, ?_⟩
  decide +kernel

private theorem c8FourActionRecord652_bounded : c8FourActionBounded c8FourRecordData652 := by
  decide +kernel

private theorem c8FourActionRecord653_covered : c8FourActionCovered c8FourRecordData653 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord653_bounded : c8FourActionBounded c8FourRecordData653 := by
  decide +kernel

private theorem c8FourActionRecord654_covered : c8FourActionCovered c8FourRecordData654 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord654_bounded : c8FourActionBounded c8FourRecordData654 := by
  decide +kernel

private theorem c8FourActionRecord655_covered : c8FourActionCovered c8FourRecordData655 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord655_bounded : c8FourActionBounded c8FourRecordData655 := by
  decide +kernel

private theorem c8FourActionRecord656_covered : c8FourActionCovered c8FourRecordData656 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord656_bounded : c8FourActionBounded c8FourRecordData656 := by
  decide +kernel

private theorem c8FourActionRecord657_covered : c8FourActionCovered c8FourRecordData657 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord657_bounded : c8FourActionBounded c8FourRecordData657 := by
  decide +kernel

private theorem c8FourActionRecord658_covered : c8FourActionCovered c8FourRecordData658 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨9, ?_⟩
  decide +kernel

private theorem c8FourActionRecord658_bounded : c8FourActionBounded c8FourRecordData658 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord659_covered : c8FourActionCovered c8FourRecordData659 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨1, ?_⟩
  decide +kernel

private theorem c8FourActionRecord659_bounded : c8FourActionBounded c8FourRecordData659 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord660_covered : c8FourActionCovered c8FourRecordData660 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨9, ?_⟩
  decide +kernel

private theorem c8FourActionRecord660_bounded : c8FourActionBounded c8FourRecordData660 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord661_covered : c8FourActionCovered c8FourRecordData661 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨2, ?_⟩
  decide +kernel

private theorem c8FourActionRecord661_bounded : c8FourActionBounded c8FourRecordData661 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord662_covered : c8FourActionCovered c8FourRecordData662 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨9, ?_⟩
  decide +kernel

private theorem c8FourActionRecord662_bounded : c8FourActionBounded c8FourRecordData662 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord663_covered : c8FourActionCovered c8FourRecordData663 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨9, ?_⟩
  decide +kernel

private theorem c8FourActionRecord663_bounded : c8FourActionBounded c8FourRecordData663 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord664_covered : c8FourActionCovered c8FourRecordData664 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨2, ?_⟩
  decide +kernel

private theorem c8FourActionRecord664_bounded : c8FourActionBounded c8FourRecordData664 := by
  decide +kernel

private theorem c8FourActionRecord665_covered : c8FourActionCovered c8FourRecordData665 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨1, ?_⟩
  decide +kernel

private theorem c8FourActionRecord665_bounded : c8FourActionBounded c8FourRecordData665 := by
  decide +kernel

private theorem c8FourActionRecord666_covered : c8FourActionCovered c8FourRecordData666 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord666_bounded : c8FourActionBounded c8FourRecordData666 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord667_covered : c8FourActionCovered c8FourRecordData667 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord667_bounded : c8FourActionBounded c8FourRecordData667 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord668_covered : c8FourActionCovered c8FourRecordData668 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord668_bounded : c8FourActionBounded c8FourRecordData668 := by
  decide +kernel

private theorem c8FourActionRecord669_covered : c8FourActionCovered c8FourRecordData669 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord669_bounded : c8FourActionBounded c8FourRecordData669 := by
  decide +kernel

private theorem c8FourActionRecord670_covered : c8FourActionCovered c8FourRecordData670 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord670_bounded : c8FourActionBounded c8FourRecordData670 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord671_covered : c8FourActionCovered c8FourRecordData671 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord671_bounded : c8FourActionBounded c8FourRecordData671 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord672_covered : c8FourActionCovered c8FourRecordData672 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord672_bounded : c8FourActionBounded c8FourRecordData672 := by
  decide +kernel

private theorem c8FourActionRecord673_covered : c8FourActionCovered c8FourRecordData673 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord673_bounded : c8FourActionBounded c8FourRecordData673 := by
  decide +kernel

private theorem c8FourActionRecord674_covered : c8FourActionCovered c8FourRecordData674 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨9, ?_⟩
  decide +kernel

private theorem c8FourActionRecord674_bounded : c8FourActionBounded c8FourRecordData674 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord675_covered : c8FourActionCovered c8FourRecordData675 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨1, ?_⟩
  decide +kernel

private theorem c8FourActionRecord675_bounded : c8FourActionBounded c8FourRecordData675 := by
  decide +kernel

private theorem c8FourActionRecord676_covered : c8FourActionCovered c8FourRecordData676 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨2, ?_⟩
  decide +kernel

private theorem c8FourActionRecord676_bounded : c8FourActionBounded c8FourRecordData676 := by
  decide +kernel

private theorem c8FourActionRecord677_covered : c8FourActionCovered c8FourRecordData677 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord677_bounded : c8FourActionBounded c8FourRecordData677 := by
  decide +kernel

private theorem c8FourActionRecord678_covered : c8FourActionCovered c8FourRecordData678 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord678_bounded : c8FourActionBounded c8FourRecordData678 := by
  decide +kernel

private theorem c8FourActionRecord679_covered : c8FourActionCovered c8FourRecordData679 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord679_bounded : c8FourActionBounded c8FourRecordData679 := by
  decide +kernel

private theorem c8FourActionRecord680_covered : c8FourActionCovered c8FourRecordData680 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨44, ?_⟩
  decide +kernel

private theorem c8FourActionRecord680_bounded : c8FourActionBounded c8FourRecordData680 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord681_covered : c8FourActionCovered c8FourRecordData681 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨45, ?_⟩
  decide +kernel

private theorem c8FourActionRecord681_bounded : c8FourActionBounded c8FourRecordData681 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord682_covered : c8FourActionCovered c8FourRecordData682 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨44, ?_⟩
  decide +kernel

private theorem c8FourActionRecord682_bounded : c8FourActionBounded c8FourRecordData682 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord683_covered : c8FourActionCovered c8FourRecordData683 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨44, ?_⟩
  decide +kernel

private theorem c8FourActionRecord683_bounded : c8FourActionBounded c8FourRecordData683 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord684_covered : c8FourActionCovered c8FourRecordData684 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨45, ?_⟩
  decide +kernel

private theorem c8FourActionRecord684_bounded : c8FourActionBounded c8FourRecordData684 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord685_covered : c8FourActionCovered c8FourRecordData685 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨44, ?_⟩
  decide +kernel

private theorem c8FourActionRecord685_bounded : c8FourActionBounded c8FourRecordData685 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord686_covered : c8FourActionCovered c8FourRecordData686 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨44, ?_⟩
  decide +kernel

private theorem c8FourActionRecord686_bounded : c8FourActionBounded c8FourRecordData686 := by
  decide +kernel

private theorem c8FourActionRecord687_covered : c8FourActionCovered c8FourRecordData687 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨45, ?_⟩
  decide +kernel

private theorem c8FourActionRecord687_bounded : c8FourActionBounded c8FourRecordData687 := by
  decide +kernel

private theorem c8FourActionRecord688_covered : c8FourActionCovered c8FourRecordData688 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord688_bounded : c8FourActionBounded c8FourRecordData688 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord689_covered : c8FourActionCovered c8FourRecordData689 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord689_bounded : c8FourActionBounded c8FourRecordData689 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord690_covered : c8FourActionCovered c8FourRecordData690 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord690_bounded : c8FourActionBounded c8FourRecordData690 := by
  decide +kernel

private theorem c8FourActionRecord691_covered : c8FourActionCovered c8FourRecordData691 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord691_bounded : c8FourActionBounded c8FourRecordData691 := by
  decide +kernel

private theorem c8FourActionRecord692_covered : c8FourActionCovered c8FourRecordData692 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord692_bounded : c8FourActionBounded c8FourRecordData692 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord693_covered : c8FourActionCovered c8FourRecordData693 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨46, ?_⟩
  decide +kernel

private theorem c8FourActionRecord693_bounded : c8FourActionBounded c8FourRecordData693 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord694_covered : c8FourActionCovered c8FourRecordData694 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨46, ?_⟩
  decide +kernel

private theorem c8FourActionRecord694_bounded : c8FourActionBounded c8FourRecordData694 := by
  decide +kernel

private theorem c8FourActionRecord695_covered : c8FourActionCovered c8FourRecordData695 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨47, ?_⟩
  decide +kernel

private theorem c8FourActionRecord695_bounded : c8FourActionBounded c8FourRecordData695 := by
  decide +kernel

private theorem c8FourActionRecord696_covered : c8FourActionCovered c8FourRecordData696 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord696_bounded : c8FourActionBounded c8FourRecordData696 := by
  decide +kernel

private theorem c8FourActionRecord697_covered : c8FourActionCovered c8FourRecordData697 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord697_bounded : c8FourActionBounded c8FourRecordData697 := by
  decide +kernel

private theorem c8FourActionRecord698_covered : c8FourActionCovered c8FourRecordData698 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord698_bounded : c8FourActionBounded c8FourRecordData698 := by
  decide +kernel

private theorem c8FourActionRecord699_covered : c8FourActionCovered c8FourRecordData699 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord699_bounded : c8FourActionBounded c8FourRecordData699 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord700_covered : c8FourActionCovered c8FourRecordData700 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord700_bounded : c8FourActionBounded c8FourRecordData700 := by
  decide +kernel

private theorem c8FourActionRecord701_covered : c8FourActionCovered c8FourRecordData701 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord701_bounded : c8FourActionBounded c8FourRecordData701 := by
  decide +kernel

private theorem c8FourActionRecord702_covered : c8FourActionCovered c8FourRecordData702 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord702_bounded : c8FourActionBounded c8FourRecordData702 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord703_covered : c8FourActionCovered c8FourRecordData703 := by
  apply Or.inr (Or.inr (Or.inl _))
  decide +kernel

private theorem c8FourActionRecord703_bounded : c8FourActionBounded c8FourRecordData703 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionChunk10_covered (j : Fin 64) :
    c8FourActionCovered (c8FourRecordChunk10[j.val]!) := by
  fin_cases j
  · exact c8FourActionRecord640_covered
  · exact c8FourActionRecord641_covered
  · exact c8FourActionRecord642_covered
  · exact c8FourActionRecord643_covered
  · exact c8FourActionRecord644_covered
  · exact c8FourActionRecord645_covered
  · exact c8FourActionRecord646_covered
  · exact c8FourActionRecord647_covered
  · exact c8FourActionRecord648_covered
  · exact c8FourActionRecord649_covered
  · exact c8FourActionRecord650_covered
  · exact c8FourActionRecord651_covered
  · exact c8FourActionRecord652_covered
  · exact c8FourActionRecord653_covered
  · exact c8FourActionRecord654_covered
  · exact c8FourActionRecord655_covered
  · exact c8FourActionRecord656_covered
  · exact c8FourActionRecord657_covered
  · exact c8FourActionRecord658_covered
  · exact c8FourActionRecord659_covered
  · exact c8FourActionRecord660_covered
  · exact c8FourActionRecord661_covered
  · exact c8FourActionRecord662_covered
  · exact c8FourActionRecord663_covered
  · exact c8FourActionRecord664_covered
  · exact c8FourActionRecord665_covered
  · exact c8FourActionRecord666_covered
  · exact c8FourActionRecord667_covered
  · exact c8FourActionRecord668_covered
  · exact c8FourActionRecord669_covered
  · exact c8FourActionRecord670_covered
  · exact c8FourActionRecord671_covered
  · exact c8FourActionRecord672_covered
  · exact c8FourActionRecord673_covered
  · exact c8FourActionRecord674_covered
  · exact c8FourActionRecord675_covered
  · exact c8FourActionRecord676_covered
  · exact c8FourActionRecord677_covered
  · exact c8FourActionRecord678_covered
  · exact c8FourActionRecord679_covered
  · exact c8FourActionRecord680_covered
  · exact c8FourActionRecord681_covered
  · exact c8FourActionRecord682_covered
  · exact c8FourActionRecord683_covered
  · exact c8FourActionRecord684_covered
  · exact c8FourActionRecord685_covered
  · exact c8FourActionRecord686_covered
  · exact c8FourActionRecord687_covered
  · exact c8FourActionRecord688_covered
  · exact c8FourActionRecord689_covered
  · exact c8FourActionRecord690_covered
  · exact c8FourActionRecord691_covered
  · exact c8FourActionRecord692_covered
  · exact c8FourActionRecord693_covered
  · exact c8FourActionRecord694_covered
  · exact c8FourActionRecord695_covered
  · exact c8FourActionRecord696_covered
  · exact c8FourActionRecord697_covered
  · exact c8FourActionRecord698_covered
  · exact c8FourActionRecord699_covered
  · exact c8FourActionRecord700_covered
  · exact c8FourActionRecord701_covered
  · exact c8FourActionRecord702_covered
  · exact c8FourActionRecord703_covered

private theorem c8FourActionChunk10_bounded (j : Fin 64) :
    c8FourActionBounded (c8FourRecordChunk10[j.val]!) := by
  fin_cases j
  · exact c8FourActionRecord640_bounded
  · exact c8FourActionRecord641_bounded
  · exact c8FourActionRecord642_bounded
  · exact c8FourActionRecord643_bounded
  · exact c8FourActionRecord644_bounded
  · exact c8FourActionRecord645_bounded
  · exact c8FourActionRecord646_bounded
  · exact c8FourActionRecord647_bounded
  · exact c8FourActionRecord648_bounded
  · exact c8FourActionRecord649_bounded
  · exact c8FourActionRecord650_bounded
  · exact c8FourActionRecord651_bounded
  · exact c8FourActionRecord652_bounded
  · exact c8FourActionRecord653_bounded
  · exact c8FourActionRecord654_bounded
  · exact c8FourActionRecord655_bounded
  · exact c8FourActionRecord656_bounded
  · exact c8FourActionRecord657_bounded
  · exact c8FourActionRecord658_bounded
  · exact c8FourActionRecord659_bounded
  · exact c8FourActionRecord660_bounded
  · exact c8FourActionRecord661_bounded
  · exact c8FourActionRecord662_bounded
  · exact c8FourActionRecord663_bounded
  · exact c8FourActionRecord664_bounded
  · exact c8FourActionRecord665_bounded
  · exact c8FourActionRecord666_bounded
  · exact c8FourActionRecord667_bounded
  · exact c8FourActionRecord668_bounded
  · exact c8FourActionRecord669_bounded
  · exact c8FourActionRecord670_bounded
  · exact c8FourActionRecord671_bounded
  · exact c8FourActionRecord672_bounded
  · exact c8FourActionRecord673_bounded
  · exact c8FourActionRecord674_bounded
  · exact c8FourActionRecord675_bounded
  · exact c8FourActionRecord676_bounded
  · exact c8FourActionRecord677_bounded
  · exact c8FourActionRecord678_bounded
  · exact c8FourActionRecord679_bounded
  · exact c8FourActionRecord680_bounded
  · exact c8FourActionRecord681_bounded
  · exact c8FourActionRecord682_bounded
  · exact c8FourActionRecord683_bounded
  · exact c8FourActionRecord684_bounded
  · exact c8FourActionRecord685_bounded
  · exact c8FourActionRecord686_bounded
  · exact c8FourActionRecord687_bounded
  · exact c8FourActionRecord688_bounded
  · exact c8FourActionRecord689_bounded
  · exact c8FourActionRecord690_bounded
  · exact c8FourActionRecord691_bounded
  · exact c8FourActionRecord692_bounded
  · exact c8FourActionRecord693_bounded
  · exact c8FourActionRecord694_bounded
  · exact c8FourActionRecord695_bounded
  · exact c8FourActionRecord696_bounded
  · exact c8FourActionRecord697_bounded
  · exact c8FourActionRecord698_bounded
  · exact c8FourActionRecord699_bounded
  · exact c8FourActionRecord700_bounded
  · exact c8FourActionRecord701_bounded
  · exact c8FourActionRecord702_bounded
  · exact c8FourActionRecord703_bounded

end CertificateChecks.Batch98

namespace Certificates

open CertificateChecks

open CFSG CFSG.LargeEvenClassification CFSG.LargeEvenClassification.Helpers in
theorem certificate98 : (c8FourActionCovered c8FourRecordData640)
    ∧ (c8FourActionBounded c8FourRecordData640)
    ∧ (c8FourActionCovered c8FourRecordData641)
    ∧ (c8FourActionBounded c8FourRecordData641)
    ∧ (c8FourActionCovered c8FourRecordData642)
    ∧ (c8FourActionBounded c8FourRecordData642)
    ∧ (c8FourActionCovered c8FourRecordData643)
    ∧ (c8FourActionBounded c8FourRecordData643)
    ∧ (c8FourActionCovered c8FourRecordData644)
    ∧ (c8FourActionBounded c8FourRecordData644)
    ∧ (c8FourActionCovered c8FourRecordData645)
    ∧ (c8FourActionBounded c8FourRecordData645)
    ∧ (c8FourActionCovered c8FourRecordData646)
    ∧ (c8FourActionBounded c8FourRecordData646)
    ∧ (c8FourActionCovered c8FourRecordData647)
    ∧ (c8FourActionBounded c8FourRecordData647)
    ∧ (c8FourActionCovered c8FourRecordData648)
    ∧ (c8FourActionBounded c8FourRecordData648)
    ∧ (c8FourActionCovered c8FourRecordData649)
    ∧ (c8FourActionBounded c8FourRecordData649)
    ∧ (c8FourActionCovered c8FourRecordData650)
    ∧ (c8FourActionBounded c8FourRecordData650)
    ∧ (c8FourActionCovered c8FourRecordData651)
    ∧ (c8FourActionBounded c8FourRecordData651)
    ∧ (c8FourActionCovered c8FourRecordData652)
    ∧ (c8FourActionBounded c8FourRecordData652)
    ∧ (c8FourActionCovered c8FourRecordData653)
    ∧ (c8FourActionBounded c8FourRecordData653)
    ∧ (c8FourActionCovered c8FourRecordData654)
    ∧ (c8FourActionBounded c8FourRecordData654)
    ∧ (c8FourActionCovered c8FourRecordData655)
    ∧ (c8FourActionBounded c8FourRecordData655)
    ∧ (c8FourActionCovered c8FourRecordData656)
    ∧ (c8FourActionBounded c8FourRecordData656)
    ∧ (c8FourActionCovered c8FourRecordData657)
    ∧ (c8FourActionBounded c8FourRecordData657)
    ∧ (c8FourActionCovered c8FourRecordData658)
    ∧ (c8FourActionBounded c8FourRecordData658)
    ∧ (c8FourActionCovered c8FourRecordData659)
    ∧ (c8FourActionBounded c8FourRecordData659)
    ∧ (c8FourActionCovered c8FourRecordData660)
    ∧ (c8FourActionBounded c8FourRecordData660)
    ∧ (c8FourActionCovered c8FourRecordData661)
    ∧ (c8FourActionBounded c8FourRecordData661)
    ∧ (c8FourActionCovered c8FourRecordData662)
    ∧ (c8FourActionBounded c8FourRecordData662)
    ∧ (c8FourActionCovered c8FourRecordData663)
    ∧ (c8FourActionBounded c8FourRecordData663)
    ∧ (c8FourActionCovered c8FourRecordData664)
    ∧ (c8FourActionBounded c8FourRecordData664)
    ∧ (c8FourActionCovered c8FourRecordData665)
    ∧ (c8FourActionBounded c8FourRecordData665)
    ∧ (c8FourActionCovered c8FourRecordData666)
    ∧ (c8FourActionBounded c8FourRecordData666)
    ∧ (c8FourActionCovered c8FourRecordData667)
    ∧ (c8FourActionBounded c8FourRecordData667)
    ∧ (c8FourActionCovered c8FourRecordData668)
    ∧ (c8FourActionBounded c8FourRecordData668)
    ∧ (c8FourActionCovered c8FourRecordData669)
    ∧ (c8FourActionBounded c8FourRecordData669)
    ∧ (c8FourActionCovered c8FourRecordData670)
    ∧ (c8FourActionBounded c8FourRecordData670)
    ∧ (c8FourActionCovered c8FourRecordData671)
    ∧ (c8FourActionBounded c8FourRecordData671)
    ∧ (c8FourActionCovered c8FourRecordData672)
    ∧ (c8FourActionBounded c8FourRecordData672)
    ∧ (c8FourActionCovered c8FourRecordData673)
    ∧ (c8FourActionBounded c8FourRecordData673)
    ∧ (c8FourActionCovered c8FourRecordData674)
    ∧ (c8FourActionBounded c8FourRecordData674)
    ∧ (c8FourActionCovered c8FourRecordData675)
    ∧ (c8FourActionBounded c8FourRecordData675)
    ∧ (c8FourActionCovered c8FourRecordData676)
    ∧ (c8FourActionBounded c8FourRecordData676)
    ∧ (c8FourActionCovered c8FourRecordData677)
    ∧ (c8FourActionBounded c8FourRecordData677)
    ∧ (c8FourActionCovered c8FourRecordData678)
    ∧ (c8FourActionBounded c8FourRecordData678)
    ∧ (c8FourActionCovered c8FourRecordData679)
    ∧ (c8FourActionBounded c8FourRecordData679)
    ∧ (c8FourActionCovered c8FourRecordData680)
    ∧ (c8FourActionBounded c8FourRecordData680)
    ∧ (c8FourActionCovered c8FourRecordData681)
    ∧ (c8FourActionBounded c8FourRecordData681)
    ∧ (c8FourActionCovered c8FourRecordData682)
    ∧ (c8FourActionBounded c8FourRecordData682)
    ∧ (c8FourActionCovered c8FourRecordData683)
    ∧ (c8FourActionBounded c8FourRecordData683)
    ∧ (c8FourActionCovered c8FourRecordData684)
    ∧ (c8FourActionBounded c8FourRecordData684)
    ∧ (c8FourActionCovered c8FourRecordData685)
    ∧ (c8FourActionBounded c8FourRecordData685)
    ∧ (c8FourActionCovered c8FourRecordData686)
    ∧ (c8FourActionBounded c8FourRecordData686)
    ∧ (c8FourActionCovered c8FourRecordData687)
    ∧ (c8FourActionBounded c8FourRecordData687)
    ∧ (c8FourActionCovered c8FourRecordData688)
    ∧ (c8FourActionBounded c8FourRecordData688)
    ∧ (c8FourActionCovered c8FourRecordData689)
    ∧ (c8FourActionBounded c8FourRecordData689)
    ∧ (c8FourActionCovered c8FourRecordData690)
    ∧ (c8FourActionBounded c8FourRecordData690)
    ∧ (c8FourActionCovered c8FourRecordData691)
    ∧ (c8FourActionBounded c8FourRecordData691)
    ∧ (c8FourActionCovered c8FourRecordData692)
    ∧ (c8FourActionBounded c8FourRecordData692)
    ∧ (c8FourActionCovered c8FourRecordData693)
    ∧ (c8FourActionBounded c8FourRecordData693)
    ∧ (c8FourActionCovered c8FourRecordData694)
    ∧ (c8FourActionBounded c8FourRecordData694)
    ∧ (c8FourActionCovered c8FourRecordData695)
    ∧ (c8FourActionBounded c8FourRecordData695)
    ∧ (c8FourActionCovered c8FourRecordData696)
    ∧ (c8FourActionBounded c8FourRecordData696)
    ∧ (c8FourActionCovered c8FourRecordData697)
    ∧ (c8FourActionBounded c8FourRecordData697)
    ∧ (c8FourActionCovered c8FourRecordData698)
    ∧ (c8FourActionBounded c8FourRecordData698)
    ∧ (c8FourActionCovered c8FourRecordData699)
    ∧ (c8FourActionBounded c8FourRecordData699)
    ∧ (c8FourActionCovered c8FourRecordData700)
    ∧ (c8FourActionBounded c8FourRecordData700)
    ∧ (c8FourActionCovered c8FourRecordData701)
    ∧ (c8FourActionBounded c8FourRecordData701)
    ∧ (c8FourActionCovered c8FourRecordData702)
    ∧ (c8FourActionBounded c8FourRecordData702)
    ∧ (c8FourActionCovered c8FourRecordData703)
    ∧ (c8FourActionBounded c8FourRecordData703) := by
  exact ⟨CertificateChecks.Batch98.c8FourActionRecord640_covered, CertificateChecks.Batch98.c8FourActionRecord640_bounded, CertificateChecks.Batch98.c8FourActionRecord641_covered, CertificateChecks.Batch98.c8FourActionRecord641_bounded, CertificateChecks.Batch98.c8FourActionRecord642_covered, CertificateChecks.Batch98.c8FourActionRecord642_bounded, CertificateChecks.Batch98.c8FourActionRecord643_covered, CertificateChecks.Batch98.c8FourActionRecord643_bounded, CertificateChecks.Batch98.c8FourActionRecord644_covered, CertificateChecks.Batch98.c8FourActionRecord644_bounded, CertificateChecks.Batch98.c8FourActionRecord645_covered, CertificateChecks.Batch98.c8FourActionRecord645_bounded, CertificateChecks.Batch98.c8FourActionRecord646_covered, CertificateChecks.Batch98.c8FourActionRecord646_bounded, CertificateChecks.Batch98.c8FourActionRecord647_covered, CertificateChecks.Batch98.c8FourActionRecord647_bounded, CertificateChecks.Batch98.c8FourActionRecord648_covered, CertificateChecks.Batch98.c8FourActionRecord648_bounded, CertificateChecks.Batch98.c8FourActionRecord649_covered, CertificateChecks.Batch98.c8FourActionRecord649_bounded, CertificateChecks.Batch98.c8FourActionRecord650_covered, CertificateChecks.Batch98.c8FourActionRecord650_bounded, CertificateChecks.Batch98.c8FourActionRecord651_covered, CertificateChecks.Batch98.c8FourActionRecord651_bounded, CertificateChecks.Batch98.c8FourActionRecord652_covered, CertificateChecks.Batch98.c8FourActionRecord652_bounded, CertificateChecks.Batch98.c8FourActionRecord653_covered, CertificateChecks.Batch98.c8FourActionRecord653_bounded, CertificateChecks.Batch98.c8FourActionRecord654_covered, CertificateChecks.Batch98.c8FourActionRecord654_bounded, CertificateChecks.Batch98.c8FourActionRecord655_covered, CertificateChecks.Batch98.c8FourActionRecord655_bounded, CertificateChecks.Batch98.c8FourActionRecord656_covered, CertificateChecks.Batch98.c8FourActionRecord656_bounded, CertificateChecks.Batch98.c8FourActionRecord657_covered, CertificateChecks.Batch98.c8FourActionRecord657_bounded, CertificateChecks.Batch98.c8FourActionRecord658_covered, CertificateChecks.Batch98.c8FourActionRecord658_bounded, CertificateChecks.Batch98.c8FourActionRecord659_covered, CertificateChecks.Batch98.c8FourActionRecord659_bounded, CertificateChecks.Batch98.c8FourActionRecord660_covered, CertificateChecks.Batch98.c8FourActionRecord660_bounded, CertificateChecks.Batch98.c8FourActionRecord661_covered, CertificateChecks.Batch98.c8FourActionRecord661_bounded, CertificateChecks.Batch98.c8FourActionRecord662_covered, CertificateChecks.Batch98.c8FourActionRecord662_bounded, CertificateChecks.Batch98.c8FourActionRecord663_covered, CertificateChecks.Batch98.c8FourActionRecord663_bounded, CertificateChecks.Batch98.c8FourActionRecord664_covered, CertificateChecks.Batch98.c8FourActionRecord664_bounded, CertificateChecks.Batch98.c8FourActionRecord665_covered, CertificateChecks.Batch98.c8FourActionRecord665_bounded, CertificateChecks.Batch98.c8FourActionRecord666_covered, CertificateChecks.Batch98.c8FourActionRecord666_bounded, CertificateChecks.Batch98.c8FourActionRecord667_covered, CertificateChecks.Batch98.c8FourActionRecord667_bounded, CertificateChecks.Batch98.c8FourActionRecord668_covered, CertificateChecks.Batch98.c8FourActionRecord668_bounded, CertificateChecks.Batch98.c8FourActionRecord669_covered, CertificateChecks.Batch98.c8FourActionRecord669_bounded, CertificateChecks.Batch98.c8FourActionRecord670_covered, CertificateChecks.Batch98.c8FourActionRecord670_bounded, CertificateChecks.Batch98.c8FourActionRecord671_covered, CertificateChecks.Batch98.c8FourActionRecord671_bounded, CertificateChecks.Batch98.c8FourActionRecord672_covered, CertificateChecks.Batch98.c8FourActionRecord672_bounded, CertificateChecks.Batch98.c8FourActionRecord673_covered, CertificateChecks.Batch98.c8FourActionRecord673_bounded, CertificateChecks.Batch98.c8FourActionRecord674_covered, CertificateChecks.Batch98.c8FourActionRecord674_bounded, CertificateChecks.Batch98.c8FourActionRecord675_covered, CertificateChecks.Batch98.c8FourActionRecord675_bounded, CertificateChecks.Batch98.c8FourActionRecord676_covered, CertificateChecks.Batch98.c8FourActionRecord676_bounded, CertificateChecks.Batch98.c8FourActionRecord677_covered, CertificateChecks.Batch98.c8FourActionRecord677_bounded, CertificateChecks.Batch98.c8FourActionRecord678_covered, CertificateChecks.Batch98.c8FourActionRecord678_bounded, CertificateChecks.Batch98.c8FourActionRecord679_covered, CertificateChecks.Batch98.c8FourActionRecord679_bounded, CertificateChecks.Batch98.c8FourActionRecord680_covered, CertificateChecks.Batch98.c8FourActionRecord680_bounded, CertificateChecks.Batch98.c8FourActionRecord681_covered, CertificateChecks.Batch98.c8FourActionRecord681_bounded, CertificateChecks.Batch98.c8FourActionRecord682_covered, CertificateChecks.Batch98.c8FourActionRecord682_bounded, CertificateChecks.Batch98.c8FourActionRecord683_covered, CertificateChecks.Batch98.c8FourActionRecord683_bounded, CertificateChecks.Batch98.c8FourActionRecord684_covered, CertificateChecks.Batch98.c8FourActionRecord684_bounded, CertificateChecks.Batch98.c8FourActionRecord685_covered, CertificateChecks.Batch98.c8FourActionRecord685_bounded, CertificateChecks.Batch98.c8FourActionRecord686_covered, CertificateChecks.Batch98.c8FourActionRecord686_bounded, CertificateChecks.Batch98.c8FourActionRecord687_covered, CertificateChecks.Batch98.c8FourActionRecord687_bounded, CertificateChecks.Batch98.c8FourActionRecord688_covered, CertificateChecks.Batch98.c8FourActionRecord688_bounded, CertificateChecks.Batch98.c8FourActionRecord689_covered, CertificateChecks.Batch98.c8FourActionRecord689_bounded, CertificateChecks.Batch98.c8FourActionRecord690_covered, CertificateChecks.Batch98.c8FourActionRecord690_bounded, CertificateChecks.Batch98.c8FourActionRecord691_covered, CertificateChecks.Batch98.c8FourActionRecord691_bounded, CertificateChecks.Batch98.c8FourActionRecord692_covered, CertificateChecks.Batch98.c8FourActionRecord692_bounded, CertificateChecks.Batch98.c8FourActionRecord693_covered, CertificateChecks.Batch98.c8FourActionRecord693_bounded, CertificateChecks.Batch98.c8FourActionRecord694_covered, CertificateChecks.Batch98.c8FourActionRecord694_bounded, CertificateChecks.Batch98.c8FourActionRecord695_covered, CertificateChecks.Batch98.c8FourActionRecord695_bounded, CertificateChecks.Batch98.c8FourActionRecord696_covered, CertificateChecks.Batch98.c8FourActionRecord696_bounded, CertificateChecks.Batch98.c8FourActionRecord697_covered, CertificateChecks.Batch98.c8FourActionRecord697_bounded, CertificateChecks.Batch98.c8FourActionRecord698_covered, CertificateChecks.Batch98.c8FourActionRecord698_bounded, CertificateChecks.Batch98.c8FourActionRecord699_covered, CertificateChecks.Batch98.c8FourActionRecord699_bounded, CertificateChecks.Batch98.c8FourActionRecord700_covered, CertificateChecks.Batch98.c8FourActionRecord700_bounded, CertificateChecks.Batch98.c8FourActionRecord701_covered, CertificateChecks.Batch98.c8FourActionRecord701_bounded, CertificateChecks.Batch98.c8FourActionRecord702_covered, CertificateChecks.Batch98.c8FourActionRecord702_bounded, CertificateChecks.Batch98.c8FourActionRecord703_covered, CertificateChecks.Batch98.c8FourActionRecord703_bounded⟩

end Certificates

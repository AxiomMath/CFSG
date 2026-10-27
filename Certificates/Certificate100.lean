module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourActionWitnessesCore

public section

open CFSG CFSG.LargeEvenClassification CFSG.LargeEvenClassification.Helpers

namespace CertificateChecks.Batch100

open CFSG CFSG.LargeEvenClassification CFSG.LargeEvenClassification.Helpers

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

private theorem c8FourActionRecord768_covered : c8FourActionCovered c8FourRecordData768 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord768_bounded : c8FourActionBounded c8FourRecordData768 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord769_covered : c8FourActionCovered c8FourRecordData769 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨11, ?_⟩
  decide +kernel

private theorem c8FourActionRecord769_bounded : c8FourActionBounded c8FourRecordData769 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord770_covered : c8FourActionCovered c8FourRecordData770 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨2, ?_⟩
  decide +kernel

private theorem c8FourActionRecord770_bounded : c8FourActionBounded c8FourRecordData770 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord771_covered : c8FourActionCovered c8FourRecordData771 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord771_bounded : c8FourActionBounded c8FourRecordData771 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord772_covered : c8FourActionCovered c8FourRecordData772 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord772_bounded : c8FourActionBounded c8FourRecordData772 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord773_covered : c8FourActionCovered c8FourRecordData773 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord773_bounded : c8FourActionBounded c8FourRecordData773 := by
  decide +kernel

private theorem c8FourActionRecord774_covered : c8FourActionCovered c8FourRecordData774 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord774_bounded : c8FourActionBounded c8FourRecordData774 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord775_covered : c8FourActionCovered c8FourRecordData775 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨1, ?_⟩
  decide +kernel

private theorem c8FourActionRecord775_bounded : c8FourActionBounded c8FourRecordData775 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord776_covered : c8FourActionCovered c8FourRecordData776 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨49, ?_⟩
  decide +kernel

private theorem c8FourActionRecord776_bounded : c8FourActionBounded c8FourRecordData776 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord777_covered : c8FourActionCovered c8FourRecordData777 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨49, ?_⟩
  decide +kernel

private theorem c8FourActionRecord777_bounded : c8FourActionBounded c8FourRecordData777 := by
  decide +kernel

private theorem c8FourActionRecord778_covered : c8FourActionCovered c8FourRecordData778 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨2, ?_⟩
  decide +kernel

private theorem c8FourActionRecord778_bounded : c8FourActionBounded c8FourRecordData778 := by
  decide +kernel

private theorem c8FourActionRecord779_covered : c8FourActionCovered c8FourRecordData779 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨1, ?_⟩
  decide +kernel

private theorem c8FourActionRecord779_bounded : c8FourActionBounded c8FourRecordData779 := by
  decide +kernel

private theorem c8FourActionRecord780_covered : c8FourActionCovered c8FourRecordData780 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨50, ?_⟩
  decide +kernel

private theorem c8FourActionRecord780_bounded : c8FourActionBounded c8FourRecordData780 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord781_covered : c8FourActionCovered c8FourRecordData781 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨50, ?_⟩
  decide +kernel

private theorem c8FourActionRecord781_bounded : c8FourActionBounded c8FourRecordData781 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord782_covered : c8FourActionCovered c8FourRecordData782 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord782_bounded : c8FourActionBounded c8FourRecordData782 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord783_covered : c8FourActionCovered c8FourRecordData783 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨12, ?_⟩
  decide +kernel

private theorem c8FourActionRecord783_bounded : c8FourActionBounded c8FourRecordData783 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord784_covered : c8FourActionCovered c8FourRecordData784 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord784_bounded : c8FourActionBounded c8FourRecordData784 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord785_covered : c8FourActionCovered c8FourRecordData785 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord785_bounded : c8FourActionBounded c8FourRecordData785 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord786_covered : c8FourActionCovered c8FourRecordData786 := by
  apply Or.inr (Or.inl _)
  decide +kernel

private theorem c8FourActionRecord786_bounded : c8FourActionBounded c8FourRecordData786 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord787_covered : c8FourActionCovered c8FourRecordData787 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord787_bounded : c8FourActionBounded c8FourRecordData787 := by
  decide +kernel

private theorem c8FourActionRecord788_covered : c8FourActionCovered c8FourRecordData788 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨2, ?_⟩
  decide +kernel

private theorem c8FourActionRecord788_bounded : c8FourActionBounded c8FourRecordData788 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord789_covered : c8FourActionCovered c8FourRecordData789 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord789_bounded : c8FourActionBounded c8FourRecordData789 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord790_covered : c8FourActionCovered c8FourRecordData790 := by
  apply Or.inl
  decide +kernel

private theorem c8FourActionRecord790_bounded : c8FourActionBounded c8FourRecordData790 := by
  decide +kernel

private theorem c8FourActionRecord791_covered : c8FourActionCovered c8FourRecordData791 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨13, ?_⟩
  decide +kernel

private theorem c8FourActionRecord791_bounded : c8FourActionBounded c8FourRecordData791 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord792_covered : c8FourActionCovered c8FourRecordData792 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord792_bounded : c8FourActionBounded c8FourRecordData792 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord793_covered : c8FourActionCovered c8FourRecordData793 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨13, ?_⟩
  decide +kernel

private theorem c8FourActionRecord793_bounded : c8FourActionBounded c8FourRecordData793 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord794_covered : c8FourActionCovered c8FourRecordData794 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨13, ?_⟩
  decide +kernel

private theorem c8FourActionRecord794_bounded : c8FourActionBounded c8FourRecordData794 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord795_covered : c8FourActionCovered c8FourRecordData795 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨5, ?_⟩
  decide +kernel

private theorem c8FourActionRecord795_bounded : c8FourActionBounded c8FourRecordData795 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord796_covered : c8FourActionCovered c8FourRecordData796 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨5, ?_⟩
  decide +kernel

private theorem c8FourActionRecord796_bounded : c8FourActionBounded c8FourRecordData796 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord797_covered : c8FourActionCovered c8FourRecordData797 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨4, ?_⟩
  decide +kernel

private theorem c8FourActionRecord797_bounded : c8FourActionBounded c8FourRecordData797 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord798_covered : c8FourActionCovered c8FourRecordData798 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨4, ?_⟩
  decide +kernel

private theorem c8FourActionRecord798_bounded : c8FourActionBounded c8FourRecordData798 := by
  decide +kernel

private theorem c8FourActionRecord799_covered : c8FourActionCovered c8FourRecordData799 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord799_bounded : c8FourActionBounded c8FourRecordData799 := by
  decide +kernel

private theorem c8FourActionRecord800_covered : c8FourActionCovered c8FourRecordData800 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord800_bounded : c8FourActionBounded c8FourRecordData800 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord801_covered : c8FourActionCovered c8FourRecordData801 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨5, ?_⟩
  decide +kernel

private theorem c8FourActionRecord801_bounded : c8FourActionBounded c8FourRecordData801 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord802_covered : c8FourActionCovered c8FourRecordData802 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨13, ?_⟩
  decide +kernel

private theorem c8FourActionRecord802_bounded : c8FourActionBounded c8FourRecordData802 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord803_covered : c8FourActionCovered c8FourRecordData803 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord803_bounded : c8FourActionBounded c8FourRecordData803 := by
  decide +kernel

private theorem c8FourActionRecord804_covered : c8FourActionCovered c8FourRecordData804 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨5, ?_⟩
  decide +kernel

private theorem c8FourActionRecord804_bounded : c8FourActionBounded c8FourRecordData804 := by
  decide +kernel

private theorem c8FourActionRecord805_covered : c8FourActionCovered c8FourRecordData805 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord805_bounded : c8FourActionBounded c8FourRecordData805 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord806_covered : c8FourActionCovered c8FourRecordData806 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨13, ?_⟩
  decide +kernel

private theorem c8FourActionRecord806_bounded : c8FourActionBounded c8FourRecordData806 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord807_covered : c8FourActionCovered c8FourRecordData807 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord807_bounded : c8FourActionBounded c8FourRecordData807 := by
  decide +kernel

private theorem c8FourActionRecord808_covered : c8FourActionCovered c8FourRecordData808 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨5, ?_⟩
  decide +kernel

private theorem c8FourActionRecord808_bounded : c8FourActionBounded c8FourRecordData808 := by
  decide +kernel

private theorem c8FourActionRecord809_covered : c8FourActionCovered c8FourRecordData809 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨3, ?_⟩
  decide +kernel

private theorem c8FourActionRecord809_bounded : c8FourActionBounded c8FourRecordData809 := by
  decide +kernel

private theorem c8FourActionRecord810_covered : c8FourActionCovered c8FourRecordData810 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨4, ?_⟩
  decide +kernel

private theorem c8FourActionRecord810_bounded : c8FourActionBounded c8FourRecordData810 := by
  decide +kernel

private theorem c8FourActionRecord811_covered : c8FourActionCovered c8FourRecordData811 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord811_bounded : c8FourActionBounded c8FourRecordData811 := by
  decide +kernel

private theorem c8FourActionRecord812_covered : c8FourActionCovered c8FourRecordData812 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨4, ?_⟩
  decide +kernel

private theorem c8FourActionRecord812_bounded : c8FourActionBounded c8FourRecordData812 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord813_covered : c8FourActionCovered c8FourRecordData813 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord813_bounded : c8FourActionBounded c8FourRecordData813 := by
  decide +kernel

private theorem c8FourActionRecord814_covered : c8FourActionCovered c8FourRecordData814 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨5, ?_⟩
  decide +kernel

private theorem c8FourActionRecord814_bounded : c8FourActionBounded c8FourRecordData814 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord815_covered : c8FourActionCovered c8FourRecordData815 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord815_bounded : c8FourActionBounded c8FourRecordData815 := by
  decide +kernel

private theorem c8FourActionRecord816_covered : c8FourActionCovered c8FourRecordData816 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨5, ?_⟩
  decide +kernel

private theorem c8FourActionRecord816_bounded : c8FourActionBounded c8FourRecordData816 := by
  decide +kernel

private theorem c8FourActionRecord817_covered : c8FourActionCovered c8FourRecordData817 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord817_bounded : c8FourActionBounded c8FourRecordData817 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord818_covered : c8FourActionCovered c8FourRecordData818 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord818_bounded : c8FourActionBounded c8FourRecordData818 := by
  decide +kernel

private theorem c8FourActionRecord819_covered : c8FourActionCovered c8FourRecordData819 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord819_bounded : c8FourActionBounded c8FourRecordData819 := by
  decide +kernel

private theorem c8FourActionRecord820_covered : c8FourActionCovered c8FourRecordData820 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨51, ?_⟩
  decide +kernel

private theorem c8FourActionRecord820_bounded : c8FourActionBounded c8FourRecordData820 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord821_covered : c8FourActionCovered c8FourRecordData821 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨51, ?_⟩
  decide +kernel

private theorem c8FourActionRecord821_bounded : c8FourActionBounded c8FourRecordData821 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord822_covered : c8FourActionCovered c8FourRecordData822 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨51, ?_⟩
  decide +kernel

private theorem c8FourActionRecord822_bounded : c8FourActionBounded c8FourRecordData822 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord823_covered : c8FourActionCovered c8FourRecordData823 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨51, ?_⟩
  decide +kernel

private theorem c8FourActionRecord823_bounded : c8FourActionBounded c8FourRecordData823 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord824_covered : c8FourActionCovered c8FourRecordData824 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨51, ?_⟩
  decide +kernel

private theorem c8FourActionRecord824_bounded : c8FourActionBounded c8FourRecordData824 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord825_covered : c8FourActionCovered c8FourRecordData825 := by
  apply Or.inr (Or.inr (Or.inr (Or.inl _)))
  refine ⟨0, ?_⟩
  decide +kernel

private theorem c8FourActionRecord825_bounded : c8FourActionBounded c8FourRecordData825 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord826_covered : c8FourActionCovered c8FourRecordData826 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨51, ?_⟩
  decide +kernel

private theorem c8FourActionRecord826_bounded : c8FourActionBounded c8FourRecordData826 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord827_covered : c8FourActionCovered c8FourRecordData827 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨51, ?_⟩
  decide +kernel

private theorem c8FourActionRecord827_bounded : c8FourActionBounded c8FourRecordData827 := by
  decide +kernel

private theorem c8FourActionRecord828_covered : c8FourActionCovered c8FourRecordData828 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨51, ?_⟩
  decide +kernel

private theorem c8FourActionRecord828_bounded : c8FourActionBounded c8FourRecordData828 := by
  decide +kernel

private theorem c8FourActionRecord829_covered : c8FourActionCovered c8FourRecordData829 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨51, ?_⟩
  decide +kernel

private theorem c8FourActionRecord829_bounded : c8FourActionBounded c8FourRecordData829 := by
  exact c8FourActionBounded_of_small _ (by decide +kernel)

private theorem c8FourActionRecord830_covered : c8FourActionCovered c8FourRecordData830 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨51, ?_⟩
  decide +kernel

private theorem c8FourActionRecord830_bounded : c8FourActionBounded c8FourRecordData830 := by
  decide +kernel

private theorem c8FourActionRecord831_covered : c8FourActionCovered c8FourRecordData831 := by
  apply Or.inr (Or.inr (Or.inr (Or.inr _)))
  refine ⟨51, ?_⟩
  decide +kernel

private theorem c8FourActionRecord831_bounded : c8FourActionBounded c8FourRecordData831 := by
  decide +kernel

private theorem c8FourActionChunk12_covered (j : Fin 64) :
    c8FourActionCovered (c8FourRecordChunk12[j.val]!) := by
  fin_cases j
  · exact c8FourActionRecord768_covered
  · exact c8FourActionRecord769_covered
  · exact c8FourActionRecord770_covered
  · exact c8FourActionRecord771_covered
  · exact c8FourActionRecord772_covered
  · exact c8FourActionRecord773_covered
  · exact c8FourActionRecord774_covered
  · exact c8FourActionRecord775_covered
  · exact c8FourActionRecord776_covered
  · exact c8FourActionRecord777_covered
  · exact c8FourActionRecord778_covered
  · exact c8FourActionRecord779_covered
  · exact c8FourActionRecord780_covered
  · exact c8FourActionRecord781_covered
  · exact c8FourActionRecord782_covered
  · exact c8FourActionRecord783_covered
  · exact c8FourActionRecord784_covered
  · exact c8FourActionRecord785_covered
  · exact c8FourActionRecord786_covered
  · exact c8FourActionRecord787_covered
  · exact c8FourActionRecord788_covered
  · exact c8FourActionRecord789_covered
  · exact c8FourActionRecord790_covered
  · exact c8FourActionRecord791_covered
  · exact c8FourActionRecord792_covered
  · exact c8FourActionRecord793_covered
  · exact c8FourActionRecord794_covered
  · exact c8FourActionRecord795_covered
  · exact c8FourActionRecord796_covered
  · exact c8FourActionRecord797_covered
  · exact c8FourActionRecord798_covered
  · exact c8FourActionRecord799_covered
  · exact c8FourActionRecord800_covered
  · exact c8FourActionRecord801_covered
  · exact c8FourActionRecord802_covered
  · exact c8FourActionRecord803_covered
  · exact c8FourActionRecord804_covered
  · exact c8FourActionRecord805_covered
  · exact c8FourActionRecord806_covered
  · exact c8FourActionRecord807_covered
  · exact c8FourActionRecord808_covered
  · exact c8FourActionRecord809_covered
  · exact c8FourActionRecord810_covered
  · exact c8FourActionRecord811_covered
  · exact c8FourActionRecord812_covered
  · exact c8FourActionRecord813_covered
  · exact c8FourActionRecord814_covered
  · exact c8FourActionRecord815_covered
  · exact c8FourActionRecord816_covered
  · exact c8FourActionRecord817_covered
  · exact c8FourActionRecord818_covered
  · exact c8FourActionRecord819_covered
  · exact c8FourActionRecord820_covered
  · exact c8FourActionRecord821_covered
  · exact c8FourActionRecord822_covered
  · exact c8FourActionRecord823_covered
  · exact c8FourActionRecord824_covered
  · exact c8FourActionRecord825_covered
  · exact c8FourActionRecord826_covered
  · exact c8FourActionRecord827_covered
  · exact c8FourActionRecord828_covered
  · exact c8FourActionRecord829_covered
  · exact c8FourActionRecord830_covered
  · exact c8FourActionRecord831_covered

private theorem c8FourActionChunk12_bounded (j : Fin 64) :
    c8FourActionBounded (c8FourRecordChunk12[j.val]!) := by
  fin_cases j
  · exact c8FourActionRecord768_bounded
  · exact c8FourActionRecord769_bounded
  · exact c8FourActionRecord770_bounded
  · exact c8FourActionRecord771_bounded
  · exact c8FourActionRecord772_bounded
  · exact c8FourActionRecord773_bounded
  · exact c8FourActionRecord774_bounded
  · exact c8FourActionRecord775_bounded
  · exact c8FourActionRecord776_bounded
  · exact c8FourActionRecord777_bounded
  · exact c8FourActionRecord778_bounded
  · exact c8FourActionRecord779_bounded
  · exact c8FourActionRecord780_bounded
  · exact c8FourActionRecord781_bounded
  · exact c8FourActionRecord782_bounded
  · exact c8FourActionRecord783_bounded
  · exact c8FourActionRecord784_bounded
  · exact c8FourActionRecord785_bounded
  · exact c8FourActionRecord786_bounded
  · exact c8FourActionRecord787_bounded
  · exact c8FourActionRecord788_bounded
  · exact c8FourActionRecord789_bounded
  · exact c8FourActionRecord790_bounded
  · exact c8FourActionRecord791_bounded
  · exact c8FourActionRecord792_bounded
  · exact c8FourActionRecord793_bounded
  · exact c8FourActionRecord794_bounded
  · exact c8FourActionRecord795_bounded
  · exact c8FourActionRecord796_bounded
  · exact c8FourActionRecord797_bounded
  · exact c8FourActionRecord798_bounded
  · exact c8FourActionRecord799_bounded
  · exact c8FourActionRecord800_bounded
  · exact c8FourActionRecord801_bounded
  · exact c8FourActionRecord802_bounded
  · exact c8FourActionRecord803_bounded
  · exact c8FourActionRecord804_bounded
  · exact c8FourActionRecord805_bounded
  · exact c8FourActionRecord806_bounded
  · exact c8FourActionRecord807_bounded
  · exact c8FourActionRecord808_bounded
  · exact c8FourActionRecord809_bounded
  · exact c8FourActionRecord810_bounded
  · exact c8FourActionRecord811_bounded
  · exact c8FourActionRecord812_bounded
  · exact c8FourActionRecord813_bounded
  · exact c8FourActionRecord814_bounded
  · exact c8FourActionRecord815_bounded
  · exact c8FourActionRecord816_bounded
  · exact c8FourActionRecord817_bounded
  · exact c8FourActionRecord818_bounded
  · exact c8FourActionRecord819_bounded
  · exact c8FourActionRecord820_bounded
  · exact c8FourActionRecord821_bounded
  · exact c8FourActionRecord822_bounded
  · exact c8FourActionRecord823_bounded
  · exact c8FourActionRecord824_bounded
  · exact c8FourActionRecord825_bounded
  · exact c8FourActionRecord826_bounded
  · exact c8FourActionRecord827_bounded
  · exact c8FourActionRecord828_bounded
  · exact c8FourActionRecord829_bounded
  · exact c8FourActionRecord830_bounded
  · exact c8FourActionRecord831_bounded

end CertificateChecks.Batch100

namespace Certificates

open CertificateChecks

open CFSG CFSG.LargeEvenClassification CFSG.LargeEvenClassification.Helpers in
theorem certificate100 : (c8FourActionCovered c8FourRecordData768)
    ∧ (c8FourActionBounded c8FourRecordData768)
    ∧ (c8FourActionCovered c8FourRecordData769)
    ∧ (c8FourActionBounded c8FourRecordData769)
    ∧ (c8FourActionCovered c8FourRecordData770)
    ∧ (c8FourActionBounded c8FourRecordData770)
    ∧ (c8FourActionCovered c8FourRecordData771)
    ∧ (c8FourActionBounded c8FourRecordData771)
    ∧ (c8FourActionCovered c8FourRecordData772)
    ∧ (c8FourActionBounded c8FourRecordData772)
    ∧ (c8FourActionCovered c8FourRecordData773)
    ∧ (c8FourActionBounded c8FourRecordData773)
    ∧ (c8FourActionCovered c8FourRecordData774)
    ∧ (c8FourActionBounded c8FourRecordData774)
    ∧ (c8FourActionCovered c8FourRecordData775)
    ∧ (c8FourActionBounded c8FourRecordData775)
    ∧ (c8FourActionCovered c8FourRecordData776)
    ∧ (c8FourActionBounded c8FourRecordData776)
    ∧ (c8FourActionCovered c8FourRecordData777)
    ∧ (c8FourActionBounded c8FourRecordData777)
    ∧ (c8FourActionCovered c8FourRecordData778)
    ∧ (c8FourActionBounded c8FourRecordData778)
    ∧ (c8FourActionCovered c8FourRecordData779)
    ∧ (c8FourActionBounded c8FourRecordData779)
    ∧ (c8FourActionCovered c8FourRecordData780)
    ∧ (c8FourActionBounded c8FourRecordData780)
    ∧ (c8FourActionCovered c8FourRecordData781)
    ∧ (c8FourActionBounded c8FourRecordData781)
    ∧ (c8FourActionCovered c8FourRecordData782)
    ∧ (c8FourActionBounded c8FourRecordData782)
    ∧ (c8FourActionCovered c8FourRecordData783)
    ∧ (c8FourActionBounded c8FourRecordData783)
    ∧ (c8FourActionCovered c8FourRecordData784)
    ∧ (c8FourActionBounded c8FourRecordData784)
    ∧ (c8FourActionCovered c8FourRecordData785)
    ∧ (c8FourActionBounded c8FourRecordData785)
    ∧ (c8FourActionCovered c8FourRecordData786)
    ∧ (c8FourActionBounded c8FourRecordData786)
    ∧ (c8FourActionCovered c8FourRecordData787)
    ∧ (c8FourActionBounded c8FourRecordData787)
    ∧ (c8FourActionCovered c8FourRecordData788)
    ∧ (c8FourActionBounded c8FourRecordData788)
    ∧ (c8FourActionCovered c8FourRecordData789)
    ∧ (c8FourActionBounded c8FourRecordData789)
    ∧ (c8FourActionCovered c8FourRecordData790)
    ∧ (c8FourActionBounded c8FourRecordData790)
    ∧ (c8FourActionCovered c8FourRecordData791)
    ∧ (c8FourActionBounded c8FourRecordData791)
    ∧ (c8FourActionCovered c8FourRecordData792)
    ∧ (c8FourActionBounded c8FourRecordData792)
    ∧ (c8FourActionCovered c8FourRecordData793)
    ∧ (c8FourActionBounded c8FourRecordData793)
    ∧ (c8FourActionCovered c8FourRecordData794)
    ∧ (c8FourActionBounded c8FourRecordData794)
    ∧ (c8FourActionCovered c8FourRecordData795)
    ∧ (c8FourActionBounded c8FourRecordData795)
    ∧ (c8FourActionCovered c8FourRecordData796)
    ∧ (c8FourActionBounded c8FourRecordData796)
    ∧ (c8FourActionCovered c8FourRecordData797)
    ∧ (c8FourActionBounded c8FourRecordData797)
    ∧ (c8FourActionCovered c8FourRecordData798)
    ∧ (c8FourActionBounded c8FourRecordData798)
    ∧ (c8FourActionCovered c8FourRecordData799)
    ∧ (c8FourActionBounded c8FourRecordData799)
    ∧ (c8FourActionCovered c8FourRecordData800)
    ∧ (c8FourActionBounded c8FourRecordData800)
    ∧ (c8FourActionCovered c8FourRecordData801)
    ∧ (c8FourActionBounded c8FourRecordData801)
    ∧ (c8FourActionCovered c8FourRecordData802)
    ∧ (c8FourActionBounded c8FourRecordData802)
    ∧ (c8FourActionCovered c8FourRecordData803)
    ∧ (c8FourActionBounded c8FourRecordData803)
    ∧ (c8FourActionCovered c8FourRecordData804)
    ∧ (c8FourActionBounded c8FourRecordData804)
    ∧ (c8FourActionCovered c8FourRecordData805)
    ∧ (c8FourActionBounded c8FourRecordData805)
    ∧ (c8FourActionCovered c8FourRecordData806)
    ∧ (c8FourActionBounded c8FourRecordData806)
    ∧ (c8FourActionCovered c8FourRecordData807)
    ∧ (c8FourActionBounded c8FourRecordData807)
    ∧ (c8FourActionCovered c8FourRecordData808)
    ∧ (c8FourActionBounded c8FourRecordData808)
    ∧ (c8FourActionCovered c8FourRecordData809)
    ∧ (c8FourActionBounded c8FourRecordData809)
    ∧ (c8FourActionCovered c8FourRecordData810)
    ∧ (c8FourActionBounded c8FourRecordData810)
    ∧ (c8FourActionCovered c8FourRecordData811)
    ∧ (c8FourActionBounded c8FourRecordData811)
    ∧ (c8FourActionCovered c8FourRecordData812)
    ∧ (c8FourActionBounded c8FourRecordData812)
    ∧ (c8FourActionCovered c8FourRecordData813)
    ∧ (c8FourActionBounded c8FourRecordData813)
    ∧ (c8FourActionCovered c8FourRecordData814)
    ∧ (c8FourActionBounded c8FourRecordData814)
    ∧ (c8FourActionCovered c8FourRecordData815)
    ∧ (c8FourActionBounded c8FourRecordData815)
    ∧ (c8FourActionCovered c8FourRecordData816)
    ∧ (c8FourActionBounded c8FourRecordData816)
    ∧ (c8FourActionCovered c8FourRecordData817)
    ∧ (c8FourActionBounded c8FourRecordData817)
    ∧ (c8FourActionCovered c8FourRecordData818)
    ∧ (c8FourActionBounded c8FourRecordData818)
    ∧ (c8FourActionCovered c8FourRecordData819)
    ∧ (c8FourActionBounded c8FourRecordData819)
    ∧ (c8FourActionCovered c8FourRecordData820)
    ∧ (c8FourActionBounded c8FourRecordData820)
    ∧ (c8FourActionCovered c8FourRecordData821)
    ∧ (c8FourActionBounded c8FourRecordData821)
    ∧ (c8FourActionCovered c8FourRecordData822)
    ∧ (c8FourActionBounded c8FourRecordData822)
    ∧ (c8FourActionCovered c8FourRecordData823)
    ∧ (c8FourActionBounded c8FourRecordData823)
    ∧ (c8FourActionCovered c8FourRecordData824)
    ∧ (c8FourActionBounded c8FourRecordData824)
    ∧ (c8FourActionCovered c8FourRecordData825)
    ∧ (c8FourActionBounded c8FourRecordData825)
    ∧ (c8FourActionCovered c8FourRecordData826)
    ∧ (c8FourActionBounded c8FourRecordData826)
    ∧ (c8FourActionCovered c8FourRecordData827)
    ∧ (c8FourActionBounded c8FourRecordData827)
    ∧ (c8FourActionCovered c8FourRecordData828)
    ∧ (c8FourActionBounded c8FourRecordData828)
    ∧ (c8FourActionCovered c8FourRecordData829)
    ∧ (c8FourActionBounded c8FourRecordData829)
    ∧ (c8FourActionCovered c8FourRecordData830)
    ∧ (c8FourActionBounded c8FourRecordData830)
    ∧ (c8FourActionCovered c8FourRecordData831)
    ∧ (c8FourActionBounded c8FourRecordData831) := by
  exact ⟨CertificateChecks.Batch100.c8FourActionRecord768_covered, CertificateChecks.Batch100.c8FourActionRecord768_bounded, CertificateChecks.Batch100.c8FourActionRecord769_covered, CertificateChecks.Batch100.c8FourActionRecord769_bounded, CertificateChecks.Batch100.c8FourActionRecord770_covered, CertificateChecks.Batch100.c8FourActionRecord770_bounded, CertificateChecks.Batch100.c8FourActionRecord771_covered, CertificateChecks.Batch100.c8FourActionRecord771_bounded, CertificateChecks.Batch100.c8FourActionRecord772_covered, CertificateChecks.Batch100.c8FourActionRecord772_bounded, CertificateChecks.Batch100.c8FourActionRecord773_covered, CertificateChecks.Batch100.c8FourActionRecord773_bounded, CertificateChecks.Batch100.c8FourActionRecord774_covered, CertificateChecks.Batch100.c8FourActionRecord774_bounded, CertificateChecks.Batch100.c8FourActionRecord775_covered, CertificateChecks.Batch100.c8FourActionRecord775_bounded, CertificateChecks.Batch100.c8FourActionRecord776_covered, CertificateChecks.Batch100.c8FourActionRecord776_bounded, CertificateChecks.Batch100.c8FourActionRecord777_covered, CertificateChecks.Batch100.c8FourActionRecord777_bounded, CertificateChecks.Batch100.c8FourActionRecord778_covered, CertificateChecks.Batch100.c8FourActionRecord778_bounded, CertificateChecks.Batch100.c8FourActionRecord779_covered, CertificateChecks.Batch100.c8FourActionRecord779_bounded, CertificateChecks.Batch100.c8FourActionRecord780_covered, CertificateChecks.Batch100.c8FourActionRecord780_bounded, CertificateChecks.Batch100.c8FourActionRecord781_covered, CertificateChecks.Batch100.c8FourActionRecord781_bounded, CertificateChecks.Batch100.c8FourActionRecord782_covered, CertificateChecks.Batch100.c8FourActionRecord782_bounded, CertificateChecks.Batch100.c8FourActionRecord783_covered, CertificateChecks.Batch100.c8FourActionRecord783_bounded, CertificateChecks.Batch100.c8FourActionRecord784_covered, CertificateChecks.Batch100.c8FourActionRecord784_bounded, CertificateChecks.Batch100.c8FourActionRecord785_covered, CertificateChecks.Batch100.c8FourActionRecord785_bounded, CertificateChecks.Batch100.c8FourActionRecord786_covered, CertificateChecks.Batch100.c8FourActionRecord786_bounded, CertificateChecks.Batch100.c8FourActionRecord787_covered, CertificateChecks.Batch100.c8FourActionRecord787_bounded, CertificateChecks.Batch100.c8FourActionRecord788_covered, CertificateChecks.Batch100.c8FourActionRecord788_bounded, CertificateChecks.Batch100.c8FourActionRecord789_covered, CertificateChecks.Batch100.c8FourActionRecord789_bounded, CertificateChecks.Batch100.c8FourActionRecord790_covered, CertificateChecks.Batch100.c8FourActionRecord790_bounded, CertificateChecks.Batch100.c8FourActionRecord791_covered, CertificateChecks.Batch100.c8FourActionRecord791_bounded, CertificateChecks.Batch100.c8FourActionRecord792_covered, CertificateChecks.Batch100.c8FourActionRecord792_bounded, CertificateChecks.Batch100.c8FourActionRecord793_covered, CertificateChecks.Batch100.c8FourActionRecord793_bounded, CertificateChecks.Batch100.c8FourActionRecord794_covered, CertificateChecks.Batch100.c8FourActionRecord794_bounded, CertificateChecks.Batch100.c8FourActionRecord795_covered, CertificateChecks.Batch100.c8FourActionRecord795_bounded, CertificateChecks.Batch100.c8FourActionRecord796_covered, CertificateChecks.Batch100.c8FourActionRecord796_bounded, CertificateChecks.Batch100.c8FourActionRecord797_covered, CertificateChecks.Batch100.c8FourActionRecord797_bounded, CertificateChecks.Batch100.c8FourActionRecord798_covered, CertificateChecks.Batch100.c8FourActionRecord798_bounded, CertificateChecks.Batch100.c8FourActionRecord799_covered, CertificateChecks.Batch100.c8FourActionRecord799_bounded, CertificateChecks.Batch100.c8FourActionRecord800_covered, CertificateChecks.Batch100.c8FourActionRecord800_bounded, CertificateChecks.Batch100.c8FourActionRecord801_covered, CertificateChecks.Batch100.c8FourActionRecord801_bounded, CertificateChecks.Batch100.c8FourActionRecord802_covered, CertificateChecks.Batch100.c8FourActionRecord802_bounded, CertificateChecks.Batch100.c8FourActionRecord803_covered, CertificateChecks.Batch100.c8FourActionRecord803_bounded, CertificateChecks.Batch100.c8FourActionRecord804_covered, CertificateChecks.Batch100.c8FourActionRecord804_bounded, CertificateChecks.Batch100.c8FourActionRecord805_covered, CertificateChecks.Batch100.c8FourActionRecord805_bounded, CertificateChecks.Batch100.c8FourActionRecord806_covered, CertificateChecks.Batch100.c8FourActionRecord806_bounded, CertificateChecks.Batch100.c8FourActionRecord807_covered, CertificateChecks.Batch100.c8FourActionRecord807_bounded, CertificateChecks.Batch100.c8FourActionRecord808_covered, CertificateChecks.Batch100.c8FourActionRecord808_bounded, CertificateChecks.Batch100.c8FourActionRecord809_covered, CertificateChecks.Batch100.c8FourActionRecord809_bounded, CertificateChecks.Batch100.c8FourActionRecord810_covered, CertificateChecks.Batch100.c8FourActionRecord810_bounded, CertificateChecks.Batch100.c8FourActionRecord811_covered, CertificateChecks.Batch100.c8FourActionRecord811_bounded, CertificateChecks.Batch100.c8FourActionRecord812_covered, CertificateChecks.Batch100.c8FourActionRecord812_bounded, CertificateChecks.Batch100.c8FourActionRecord813_covered, CertificateChecks.Batch100.c8FourActionRecord813_bounded, CertificateChecks.Batch100.c8FourActionRecord814_covered, CertificateChecks.Batch100.c8FourActionRecord814_bounded, CertificateChecks.Batch100.c8FourActionRecord815_covered, CertificateChecks.Batch100.c8FourActionRecord815_bounded, CertificateChecks.Batch100.c8FourActionRecord816_covered, CertificateChecks.Batch100.c8FourActionRecord816_bounded, CertificateChecks.Batch100.c8FourActionRecord817_covered, CertificateChecks.Batch100.c8FourActionRecord817_bounded, CertificateChecks.Batch100.c8FourActionRecord818_covered, CertificateChecks.Batch100.c8FourActionRecord818_bounded, CertificateChecks.Batch100.c8FourActionRecord819_covered, CertificateChecks.Batch100.c8FourActionRecord819_bounded, CertificateChecks.Batch100.c8FourActionRecord820_covered, CertificateChecks.Batch100.c8FourActionRecord820_bounded, CertificateChecks.Batch100.c8FourActionRecord821_covered, CertificateChecks.Batch100.c8FourActionRecord821_bounded, CertificateChecks.Batch100.c8FourActionRecord822_covered, CertificateChecks.Batch100.c8FourActionRecord822_bounded, CertificateChecks.Batch100.c8FourActionRecord823_covered, CertificateChecks.Batch100.c8FourActionRecord823_bounded, CertificateChecks.Batch100.c8FourActionRecord824_covered, CertificateChecks.Batch100.c8FourActionRecord824_bounded, CertificateChecks.Batch100.c8FourActionRecord825_covered, CertificateChecks.Batch100.c8FourActionRecord825_bounded, CertificateChecks.Batch100.c8FourActionRecord826_covered, CertificateChecks.Batch100.c8FourActionRecord826_bounded, CertificateChecks.Batch100.c8FourActionRecord827_covered, CertificateChecks.Batch100.c8FourActionRecord827_bounded, CertificateChecks.Batch100.c8FourActionRecord828_covered, CertificateChecks.Batch100.c8FourActionRecord828_bounded, CertificateChecks.Batch100.c8FourActionRecord829_covered, CertificateChecks.Batch100.c8FourActionRecord829_bounded, CertificateChecks.Batch100.c8FourActionRecord830_covered, CertificateChecks.Batch100.c8FourActionRecord830_bounded, CertificateChecks.Batch100.c8FourActionRecord831_covered, CertificateChecks.Batch100.c8FourActionRecord831_bounded⟩

end Certificates

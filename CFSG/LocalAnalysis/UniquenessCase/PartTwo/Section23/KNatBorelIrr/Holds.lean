module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsTwoThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.LinesLinear
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.LinesMinus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.LinesPlus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

theorem kNatBorelIrr_holds : KNatBorelIrr := by
  intro W _ _ H S P k hN hperf hS hNP hPH hP J hJ hstab
  rcases hN with h | h | h | h | h | h | h | h | h | h | h
  · exact borelIrr_of_binaryNaturalSL (d := 2) (by norm_num) h.2 hS hNP hPH hP hJ hstab
  · exact borelIrr_of_omegaMinusFour h.2 hS hNP hPH hP hJ hstab
  · exact borelIrr_of_omegaPlusFour h.2 hperf hS hNP hPH hP hJ hstab
  · exact borelIrr_of_natSpn (N := 4) (by norm_num) h.2 hS hNP hPH hP hJ hstab
  · exact borelIrr_of_binaryNaturalSL (d := 3) (by norm_num) h.2 hS hNP hPH hP hJ hstab
  · obtain ⟨a, -, -, hNat⟩ := h
    exact borelIrr_of_natSUn hNat hS hNP hPH hP hJ hstab
  · exact borelIrr_of_omegaMinusSix h.2 hS hNP hPH hP hJ hstab
  · exact borelIrr_of_binaryNaturalSL (d := 4) (by norm_num) h.2 hS hNP hPH hP hJ hstab
  · exact borelIrr_of_omegaPlusSix h.2 hS hNP hPH hP hJ hstab
  · exact borelIrr_of_natSpn (N := 6) (by norm_num) h.2 hS hNP hPH hP hJ hstab
  · exact borelIrr_of_omegaMinusEight h.2 hS hNP hPH hP hJ hstab

end CFSG.LocalAnalysis.UniquenessCase.UC22

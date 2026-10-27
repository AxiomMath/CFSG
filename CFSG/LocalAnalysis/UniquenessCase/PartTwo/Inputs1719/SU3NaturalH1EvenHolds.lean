module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3NaturalH1Odd
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SU3H1.Compl
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SU3H1.Even

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem k_SU3NaturalH1Even_holds : K_SU3NaturalH1Even := by
  intro W _ _ hW K n hK hn _ Z _ hZK hZ _ _ hNat
  obtain ⟨P, hP, hinf, hsup, hPK⟩ := SU3H1.exists_stableUnder_compl hW hK hn hZK hZ hNat
  obtain ⟨hPc, hPnat⟩ :=
    SU3H1.commSub_eq_and_cNatModSU3Sub_of_compl hZK hZ hNat hP hinf hsup hPK
  exact ⟨P, hP, hinf, hsup, hPc, hPnat⟩

theorem k_SU3NaturalH1_holds : K_SU3NaturalH1 :=
  k_SU3NaturalH1_of_even k_SU3NaturalH1Even_holds

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

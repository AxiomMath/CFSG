module

public import CFSG.RankThree.PartOne.F106.ConvAll
public import CFSG.RankThree.PartOne.F106.OddRad
public import CFSG.RankThree.PartOne.F106.OddRadL2
public import CFSG.RankThree.PartOne.F106.OddRadSz
public import CFSG.RankThree.PartOne.F106.OddRadPSL
public import CFSG.RankThree.PartOne.F106.OddRadG2Out
public import CFSG.RankThree.PartOne.F106.OddRadTriOut
public import CFSG.RankThree.PartOne.F106.OddRadF4
public import CFSG.RankThree.PartOne.F106.OddRadUnitary
public import CFSG.RankThree.PartOne.F106.OddRadSp
public import CFSG.RankThree.PartOne.F106.OddRadOrth
public import CFSG.RankThree.PartOne.F106.OddRadRee
public import CFSG.RankThree.PartOne.F106.OddRadTits

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.RankThree.PartOne.N143

theorem oddRadFive_of_converse
    (hConv : EvenListConverse) : OddRadFive := by
  intro T _ _ hs hna hEven hList β hβ
  obtain ⟨t, hsm⟩ := (evenLieTypeSmall_iff_exists_smallModel T).mp (hConv T hs hna hEven hList)
  cases t with
  | PSL =>
    obtain ⟨n, f, hadm, hmodel, hsmall⟩ := hsm
    have h2n : 2 ≤ n := hadm.2.2.1
    by_cases hn2 : n = 2
    · subst hn2
      exact oddRadAt_pslTwo T hs ⟨f, hadm, hmodel⟩ β hβ
    · exact oddRadAt_pslGeThree T hs ⟨n, f, by omega, hadm, hmodel, hsmall⟩ β hβ
  | PSU => exact oddRadAt_smallModel_psu T hs hsm β hβ
  | PSp => exact oddRadAt_smallModel_psp T hs hsm β hβ
  | POmegaOdd => obtain ⟨n, f, -, -, h⟩ := hsm; exact h.elim
  | POmegaPlus => exact oddRadAt_smallModel_pOmegaPlus T hs hsm β hβ
  | POmegaMinus => exact oddRadAt_smallModel_pOmegaMinus T hs hsm β hβ
  | G2 => exact oddRadAt_smallModel_g2 T hs hsm β hβ
  | F4 => exact oddRadAt_smallModel_f4 T hs hsm β hβ
  | E6 => obtain ⟨n, f, -, -, h⟩ := hsm; exact h.elim
  | E7 => obtain ⟨n, f, -, -, h⟩ := hsm; exact h.elim
  | E8 => obtain ⟨n, f, -, -, h⟩ := hsm; exact h.elim
  | twistedE6 => obtain ⟨n, f, -, -, h⟩ := hsm; exact h.elim
  | trialityD4 => exact oddRadAt_smallModel_trialityD4 T hs hsm β hβ
  | twistedB2 => exact oddRadAt_smallModel_twistedB2 T hs hsm β hβ
  | twistedG2 => obtain ⟨n, f, -, -, h⟩ := hsm; exact h.elim
  | twistedF4 => exact oddRadAt_smallModel_twistedF4 T hs hsm β hβ
  | Tits => exact oddRadAt_smallModel_tits T hs hsm β hβ

section Certs

theorem oddRadFive_holds : OddRadFive :=
  oddRadFive_of_converse evenListConverse_of

end Certs

end CFSG.RankThree.PartOne.F106

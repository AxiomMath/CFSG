module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Assembly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154RT8
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Four
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34T8
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSmallResults
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSmallT7
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenElevenRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_r16_4_of_three (D : Data G) (S : s16h_Std D) (hr3 : CFSG.Open.evenRank G = 3)
    (hσG : SigmaThree D) (hσ1 : D.sig = D.sig1) (hRows : K_FixHalfRows) (h880 : F08.R880 D)
    (h163c : R16_3FComp D) (hSchur : RSchur153) (hJP : K_JonesParshallH1) (h1217 : R1217 D)
    (hU2 : R8100U2 D) (h920L28 : s16h_e3_R920L28 D) (h153 : R15_3Small D) :
    R16_4 D := by
  have h129 : R129_1 D := r129_1_of_r127 D S.h127
  have h115 : F11.R115 D := uc22p22q_r115_of D S.hx S.h61
  have h1110 : R1110Core D :=
    r1110Core_holds D S.hSig S.h61 S.h63 S.h77 S.h869 S.h111 S.h112 S.hThin S.hCyc
  have hT7 : RT7Small D := rt7_of_fifteen_three_small D h153 h129 h1217
  have h156 : R15_6Small D := fun V₀ V L h hsmall hL g hVg hAM =>
    fifteen_six_small D h129 h1217 hT7 S.hSig hσ1 V₀ V L h hsmall hL g hVg hAM
  have h159 : R15_9Small D := fifteen_nine_small D h1217 h156 (fifteen_eight_small D h1217 h156)
  have hT8 : RT8 D :=
    s16c34_rt8_of_small D h153 h1217 S.h127
      (s16h_r1110W_holds D S.hSig S.h61 S.h63 S.h77 S.h869 S.h111 S.h112 S.hThin S.hCyc) hσ1
  have h1513 : R15_13Small D :=
    s16c34_fifteen_thirteen D S.hSig hσ1 h129 S.h61 S.h126 S.h127 h1217 h1110
      (s16c34_r1111_of_153 (r1111_153_holds D S.hx S.h61)) h115 h159
      (s16c34_fifteen_eleven D h1217 h159 hT7 hT8) (s16c34_fifteen_twelve D h129 h1217 hT7)
  exact s16c34_sixteen_four D h1513
    (s16h_r16_4_hyp154_of_three D S hr3 hσG (fun _ _ _ => hσ1) hRows h880 h163c hSchur hJP h1217
      hU2 h920L28)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

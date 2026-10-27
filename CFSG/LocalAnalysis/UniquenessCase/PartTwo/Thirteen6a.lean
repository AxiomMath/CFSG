module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen6aMain
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveFourteenB
import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3S13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S136a

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r136a_of_rows
    (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) {D : Data G}
    (hx : DataExt D) (hSg : UC6S846.SigmaStd D) (hrk3 : SigmaRankThree13 D)
    (h846 : F08.R846 D) (h82 : F08.R82 D) (h76 : F07.R76Sig D) (h614 : UC6.R6_14 D)
    (h638 : UC6.R6_38 D)
    (hrows : ∀ (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V),
      (Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3) → D.sig = D.sig1 →
        S17.R17_1At D V₀ V hV ∧ S17.R17_2_2At D V₀ V hV ∧ S17.R17_2_3At D V₀ V hV ∧
          S17.R17_3At D V₀ V ∧ S17.R17_33_2At D V₀ V ∧ S17.R17_33_3At D V₀ V) :
    S17.R136a D := by
  intro h1219 h131 p hp ⟨V₀, V, ⟨h123, H₀, h124⟩, h1669⟩
  have hV : Hyp125 D V₀ V := ⟨h123, H₀, TwelveFourteen.mem_hSet_of_f12Hyp124 D h124,
    TwelveFourteen.hyp124_of_f12Hyp124 D h124⟩
  obtain ⟨r1, r22, r23, r3, r332, r333⟩ := hrows V₀ V hV h1669 h1219
  have hS : Setting13 D := ⟨h1219, h131⟩
  have h847 : R847Four D := fun Y hY X hXY q hq hq2 hXq _ _ hthin =>
    r3 Y hY hthin X ⟨q, hq, hq2, hXq, hXY⟩
  exact r136a_at hThin hCyc hx hSg hS h82 h76 h614 h638
    (fun _ hL => uc22s2121e3_shape hThin hCyc hS hSg hrk3 h846 h847 hL) hV r1 r22 r23 r332 r333
    hp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S136a

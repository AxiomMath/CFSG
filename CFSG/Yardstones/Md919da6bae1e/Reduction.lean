module

public import CFSG.Yardstones.Md919da6bae1e.Definitions
public import CFSG.RankThree.PartTwo.Census.Item433
public import CFSG.RankThree.PartTwo.Sec21.LitScopeProofGL83
public import CFSG.RankThree.PartTwo.Sec21.Item64Glue
public import CFSG.RankThree.PartTwo.Sec6.LitScopeProof
public import CFSG.RankThree.PartTwo.Sec4.Item45Closed
public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowGriess
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.RankThree.PartTwo.Sec4.T444.Step452Residual
public import CFSG.RankThree.PartTwo.Sec4.Item4ResProof4443
public import CFSG.RankThree.PartTwo.KFacts.KS18OuterMain
public import CFSG.RankThree.PartTwo.Sec18.Item18ResProofHyp191
public import CFSG.RankThree.PartTwo.Sec18.Item183ETProof
public import CFSG.RankThree.PartTwo.Sec18.Item18ResProofRem187Q
public import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
public import CFSG.RankThree.PartTwo.Late.Item2011
public import CFSG.RankThree.PartTwo.Sec19.Item1912
public import CFSG.RankThree.PartTwo.KFacts.KS18M12Proof
public import CFSG.RankThree.PartTwo.KFacts.KS14GL33
public import CFSG.RankThree.PartTwo.Sec19.Item19Res4ProofWide3
public import CFSG.RankThree.PartTwo.Sec19.Item19Res4ProofWide3S1919
public import CFSG.RankThree.PartTwo.Sec19.KS1919G2P
public import CFSG.RankThree.PartTwo.Sec19.KS1919U48
public import CFSG.Holt.H78.Theorem1
public import CFSG.Holt.H78.Bridge

public section

namespace CFSG.Yardstones.Md919da6bae1e

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly (KProper InCatalog IsCharTwoType evenRank)
open CFSG.Assembly.RankThreeEven (localRank IIModel AschCoreLocal)


theorem r3e_part_two_prime_three_outcome_of_yardstones
    (y01 : Sec6.GF2TypeE27) (y02 : Sec4.Item4_34Sec)
    (y03 : Sec4.Item4_44_3Diag) (y04 : Sec21.Item612) (y05 : Sec12.Item128BarAt)
    (y06 : Sec13.Item131) (y07 : Sec17.Item1730) (y08 : Sec19.Item194UsedWide3)
    (y09 : Sec19.Item195) (y10 : Sec19.Step1914) (y11 : Steps1918Core1919)
    (y12 : Sec20.Item201Contra1) (y13 : Sec21.Item231) (y14 : Sec21.Item233)
    (y15 : Sec21.GL83StronglyEmbeddedNoSimpleThree) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      KProper InCatalog G → IsCharTwoType G → evenRank G = 3 →
      (∀ q : ℕ, q.Prime → 3 < q → localRank q G < 3) → IIModel G ∨ AschCoreLocal G 2 := by
  have h45 : Sec4.Item4_5 := Sec4.rank3II_4_5
  have hGr := CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  have h422 : Sec4.Item4_22 := KFacts.rank3II_4_22_of_items_noItem41 h45 hGr
    (Sec4.Census.rank3II_4_3_of_griess_noItem41 hGr)
  have h4441 := Sec4.rank3II_4_44_1_of_item4_34 y02 h45
  have h4442 := Sec4.rank3II_4_44_2_of h45 y02
  have h4443 : Sec4.Item4_44_3 := Sec4.Res4443.item4_44_3_of y02 h45 y03
  have h1811 := Sec18.rank3II_18_1_1_of h4441
  have h1812 := Sec18.rank3II_18_1_2_of h4442 KFacts.KS18.ks18OuterInvolution
  have h1210 : Sec12.Item1210BarS := Sec12.item1210BarS_of y05 h422 h45
  have h183One := Sec18.item183One_of_item181 h45 h1811 h1812 (Sec18.item183ET_of h1210 y07)
  have h1841 := Sec18.rank3II_18_4_1_of_item183One h1812 h183One
    (Sec18.claim184LcLe_of h1812 (Sec4.item4_44_3SL_of_item4_44_3 h4443))
  have hrem := Sec18.rank3II_rem_18_7_of_item184 h1841
    (Sec18.rem187Q_of_item4443 h4443 h1812 h1841 (Sec18.item183K_of_item183One h183One))
  have hsetAt := Sec13.item13SetupAt_of h422 h45
  have h1914E := Sec19.rank3II_19_14E_of y10 KFacts.ks18M12
  have h1919 : Sec19.Step1919 := Sec19.step1919_of_lie_wide3 y11.step1919CoreSplitLie y08
    h1914E (Sec19.step1914More_of_step1914 y10)
  have h1912 := Sec19.rank3II_19_12_of y07 y06 Sec13.sporadicModels131 Sec13.slTwoCenter
    (Late.item13Setup_of hsetAt) hsetAt h1811 h1812 y09 y11.step1918
    (Sec19.rank3II_19_19_O2_of y10 h1914E KFacts.KS14.ks18GL33) h1919
    (Sec19.step1919End_of_parabolic_wide3 y08 y10 Sec19.ks1919G2P Sec19.ks1919U48)
  have h2011 : Item2011 := Late.rank3II_20_11_of_items h4441 hrem y12 h1912
  have hHolt : Sec21.HoltUniqueFixedPointSimple :=
    CFSG.Holt.H78.holtUniqueFixedPointSimple_of_holtTheorem1 CFSG.Holt.H78.holtTheorem1
  have h641 : Sec6.Item6_4_1 := Sec6.rank3II_6_4_1_of_e27 y01
  have h236 : Item236 := Sec21.item236_of_items (Sec21.item64One_of_item6_4_1 h641)
    (Sec21.item612Sec21_of_items y04 (Sec6.item45_of_item4_5 h45)) y14
    (Sec21.rank3II_23_4_of_gl83Simple y13 y14 y15) hHolt
  exact theorem_four_of_items Census.item433 h236 h2011

end CFSG.Yardstones.Md919da6bae1e

module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12InvPlan
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12InvA
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12InvB
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12InvC
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12InvD
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12InvE
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12InvF
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.KFacts.KS18M12Proof
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item414Local
public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesPlan2
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesSylow
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesElem
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesD
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesPair
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesS3
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesFusG
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12S1red
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12S1gen
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12N45
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12S2a
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12Swap
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12NormL
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12EA9
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12S1abs
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12S1Y
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12S1F
public import CFSG.RankThree.PartTwo.Sec13.Item131a

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem ycfgMemA_holds : YCfgMemA :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hY => hY.haA

theorem ycfgMixed_holds : YCfgMixed := ycfgMixed_of_EA9 cfgEA9_holds

theorem pieceM12_holds
    (h131a : Item131a) (h45 : Sec4.Item4_5) : PieceM12 :=
  pieceM12_of_residual ycfgMemA_holds (m12Inverting_of_parts (invPartA_of h131a sporadicModels131)
      (invPartB_of KFacts.ks18M12) invPartC_holds invPartD_holds
      (invPartE_of Sec4.Sporadic.rank3II_4_14_local) invPartF_holds)
    (m12NormLComm_of_mixed ycfgMixed_holds)
    (m12MovesL_of_parts
        (S1_of_parts s1red_holds (s1n_holds h45) s1gen_holds (s1y_holds h131a) (s1f_holds h131a)
            s1abs_holds)
        (S2_of_parts (s2pair_of_parts s2swap_holds s2a_holds s2fus_holds) s2d_of_lift
            (s2e_holds h45)) s3_holds s4_holds s5_holds s6_holds s7_holds ycfgMixed_holds)

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b

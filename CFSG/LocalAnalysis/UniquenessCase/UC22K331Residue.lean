module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K331Fams
public import CFSG.RankThree.PartOne.TCB.Sporadic
public import CFSG.GH74.Orders.Sporadic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRankAny
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels
public import CFSG.LieType.SeitzGeneration.ExcVacuousSuzuki
public import CFSG.LieType.SeitzGeneration.ExcParabolicTits
import CFSG.LocalAnalysis.UniquenessCase.UC22K331ClassicalLow
import CFSG.LocalAnalysis.UniquenessCase.UC22K331D4Odd
import CFSG.LocalAnalysis.UniquenessCase.UC22K331G2Odd
import CFSG.LocalAnalysis.UniquenessCase.UC22K331HeRu
import CFSG.LocalAnalysis.UniquenessCase.UC22K331L3Even
import CFSG.LocalAnalysis.UniquenessCase.UC22K331RankCl
import CFSG.LocalAnalysis.UniquenessCase.UC22K331RankGap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

theorem k331_of_residue
    (h : K331Residue) : K331 := by
  refine k331_of_inputs
    { bridge := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group
      card_M11 := CFSG.Semidihedral.GL2Recognition.card_nativeM11
      card_M12 := CFSG.GH74.card_of_isSporadic_M12 ⟨MulEquiv.refl _⟩
      card_J1 := CFSG.GH74.card_of_isSporadic_J1 ⟨MulEquiv.refl _⟩
      witness := CFSG.SectionRank.sporadicThreeRankWitnesses
      monster := fun hN => by
        haveI : Nontrivial CFSG.Blueprint.NativeSporadic.M := hN
        exact CFSG.SectionRank.M_nontrivial_elementary_three_rank_four
      chevalley := CFSG.TauCetiBridge.Even.chevalleyBridgesAll
      adjoint := fun τ hτ K _ _ S _ _ ⟨e⟩ => by
        have : Finite (CFSG.Blueprint.AdjointQuotient τ K) := Finite.of_equiv S e.toEquiv
        exact three_le_pRank_of_equiv e ((by norm_num : 3 ≤ 4).trans
          (CFSG.LieType.Chevalley.four_le_pRank_three_adjointQuotient_any hτ))
      ree := fun m hv S _ _ ⟨e⟩ => by
        obtain ⟨-, h3, hr⟩ := CFSG.SectionRank.smallReeModel_rank
          (CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 m ⟨hv, ⟨e⟩⟩)
        omega
      suzuki := fun m hv => CFSG.LieType.SeitzGeneration.card_cat_suzuki_coprime_three hv
      tits := fun hv => CFSG.LieType.SeitzGeneration.card_cat_tits hv
      rankGap := k331_rankGap
      classicalLow := k331_classicalLow
      l3Even := k331_l3Even
      g2Odd := k331_g2Odd
      d4Odd := k331_d4Odd
      heRu := k331_heRu CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group } h

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

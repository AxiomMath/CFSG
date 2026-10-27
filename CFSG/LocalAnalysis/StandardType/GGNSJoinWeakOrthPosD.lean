module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinWeakOrthDispatch
public import CFSG.LocalAnalysis.StandardType.GGNSJoinOutWeakPosDefs
import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameOfMarking
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylNoLine

public section

namespace CFSG.StandardType.NSJoin

open CFSG CFSG.Assembly

theorem nsWeakOrthPosInputOf_D
    (hRk : GGTwE6ThreeNbrRankInput) (hNQ4 : NSNbrQFourInputOf (fun {ι} M => NSTypeD M)) :
    NSWeakOrthPosInputOf (fun {ι} M => NSTypeD M) := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hnsL hguard K hK hns hnU
  have hmark := nsWeakNbr_orthMarking_typeD hRk hNQ4 hcfg hnsL hguard hK hns hnU
  obtain ⟨hp, hodd⟩ := ggRouteCfg_prime hcfg
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨y, hnb⟩, -⟩ := id hK
  refine OrthTorus.exists_orthWeakFrame_of_marking ggLabelRigidInput_holds hodd
    hcfg.1.1.2.1.2.1 hcfg.1.1.2.1.2.2.2 hmark fun hN => ?_
  have h3 := pow_three_le_card_range_ggGamma_bstar hcfg.1.1 hnb hN
  by_contra hall
  push Not at hall
  have hbot : (ggGamma K hN).range = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨b, rfl⟩
    exact hall b
  rw [hbot, Subgroup.card_bot] at h3
  have h1 : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp.one_lt
  omega

end CFSG.StandardType.NSJoin

end

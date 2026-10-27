module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestOverP
public import CFSG.LocalAnalysis.StandardType.GGSporKRestFStarSylow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.McLFiveLocal

public section

namespace CFSG.StandardType.SporadicShape

theorem sporKRestAsch86McLFive_holds :
    SporKRestAsch86McLFive := by
  intro S Y hY hNY
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  let θ : (TauCeti.CFSGIndex.sporadic .McL).Group ≃* CFSG.RankThree.Native.mcl275P :=
    eC.symm.trans CFSG.RankThree.Native.mcl275Equiv
  haveI : Finite (TauCeti.CFSGIndex.sporadic .McL).Group := Finite.of_equiv _ θ.symm.toEquiv
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨-, hmax, hcent, -, -, -, hsolv, -⟩ := CFSG.AGLEmbeddingD2.heisLocal_mclP θ S
  rcases hmax Y hNY with rfl | rfl
  · refine sporKRest_fstar_isPGroup_of_normal_sylow hsolv (S.subtype Subgroup.le_normalizer)
      (by rw [Sylow.coe_subtype]; exact Subgroup.normal_in_normalizer) fun x hx => ?_
    rw [Sylow.coe_subtype] at hx ⊢
    rw [Subgroup.mem_subgroupOf]
    apply hcent
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.1 hx) ⟨h, Subgroup.le_normalizer hh⟩
      (by rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]; exact hh))
  · exact absurd rfl hY

theorem sporKRest_coverOrUnmarked_McL_5 :
    SporKRestCoverOrUnmarked 5 (TauCeti.CFSGIndex.sporadic .McL).Group :=
  ggSporKRest_coverOrUnmarked_McL_5_of_asch86 sporKRestAsch86McLFive_holds

end CFSG.StandardType.SporadicShape

end

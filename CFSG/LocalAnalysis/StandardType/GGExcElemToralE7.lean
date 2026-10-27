module

public import CFSG.LocalAnalysis.StandardType.GGExcElemToralCyclic
public import CFSG.LocalAnalysis.StandardType.GGExcToralSylowElem
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralSevenProved
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E7FiveAux.Steinberg
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharE7
public import CFSG.LieType.Chevalley.EvenCartanRootDiagonals
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Assembly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.K133H.G2Plane
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.ThreeA1Group

public section

namespace CFSG.StandardType

open CFSG.StandardType.ExcElemToral CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple


theorem ggExcElemToralRestInput_E7 : GGExcElemToralRestInput .E7 := by
  intro K _ _ _ p hp hp2 hpq hpb s hs
  have hp11 : p < 11 := hpb
  have htorus : ∀ a : Fin Tag.E7.rank → Kˣ, rootDiagUnit Tag.E7 a ∈ torusGroup Tag.E7 K :=
    fun a => (even_power_two_Cartan_root_diagonals_inner .E7
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) K (ringChar.eq K 2)).1 a
  have hp' : p = 3 ∨ p = 5 ∨ p = 7 := by
    have := hp.two_le
    interval_cases p
    · exact absurd rfl hp2
    · exact Or.inl rfl
    · exact absurd hp (by norm_num)
    · exact Or.inr (Or.inl rfl)
    · exact absurd hp (by norm_num)
    · exact Or.inr (Or.inr rfl)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
  rcases hp' with rfl | rfl | rfl
  · exact ggExcToral_zpowers_of_monomialToral hp
      (monomialToralAt_three_of_block a2BlockToral_E7)
      (fun _ _ a ha => (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_three a ha).le)
      hpq (fun a _ => htorus a) hs
  · exact ggExcToral_zpowers_of_monomialToral hp
      monomialToralAt_E7_five
      (fun _ _ a ha => (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_five a ha).le)
      hpq (fun a _ => htorus a) hs
  · exact ggExcToral_zpowers_of_monomialToral hp
      (monomialToralAt_seven_of_chainBlock (fun _ hγ => iform_self_E7 hγ)
        (chainBlockToral_E7_six_of_transitive a6ChainTransitive_E7))
      (fun _ _ a ha => (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_seven a ha).le)
      hpq (fun a _ => htorus a) hs

end CFSG.StandardType

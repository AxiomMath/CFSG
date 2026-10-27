module

public import CFSG.LocalAnalysis.StandardType.GGExcElemToralCyclic
public import CFSG.LocalAnalysis.StandardType.GGExcToralSylowElem
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralSevenProved
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharE8
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

public section

namespace CFSG.StandardType

open CFSG.StandardType.ExcElemToral CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Steinberg


theorem ggExcElemToralRestInput_E8 : GGExcElemToralRestInput .E8 := by
  intro K _ _ _ p hp hp2 hpq hpb s hs
  have hp11 : p < 11 := hpb
  have htorus : ∀ a : Fin Tag.E8.rank → Kˣ, rootDiagUnit Tag.E8 a ∈ torusGroup Tag.E8 K :=
    fun a => (even_power_two_Cartan_root_diagonals_inner .E8
      (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) K (ringChar.eq K 2)).1 a
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
      (monomialToralAt_three_of_block a2BlockToral_E8)
      (fun _ _ a ha => (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_three a ha).le)
      hpq (fun a _ => htorus a) hs
  · exact ggExcToral_zpowers_of_monomialToral hp
      (monomialToralAt_five_of_chainBlock (fun _ hγ => iform_self_E8 hγ) chainBlockToral_E8_four)
      (fun _ _ a ha => (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_five a ha).le)
      hpq (fun a _ => htorus a) hs
  · exact ggExcToral_zpowers_of_monomialToral hp
      (monomialToralAt_seven_of_chainBlock (fun _ hγ => iform_self_E8 hγ)
        (chainBlockToral_E8_six_of_transitive a6ChainTransitive_E8))
      (fun _ _ a ha => (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_seven a ha).le)
      hpq (fun a _ => htorus a) hs

end CFSG.StandardType

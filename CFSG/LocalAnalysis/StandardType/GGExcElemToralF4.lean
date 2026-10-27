module

public import CFSG.LocalAnalysis.StandardType.GGExcElemToralCyclic
public import CFSG.LocalAnalysis.StandardType.GGExcToralSylowElem
public import CFSG.HardMathSupport.Timmesfeld.Torality.F4Block
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharF4
public import CFSG.LieType.Chevalley.EvenCartanRootDiagonals

public section

namespace CFSG.StandardType

open CFSG.StandardType.ExcElemToral CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Steinberg


theorem ggExcElemToralRestInput_F4 : GGExcElemToralRestInput .F4 := by
  intro K _ _ _ p hp hp2 hpq hpb s hs
  have hp5 : p < 5 := hpb
  have hp3 : p = 3 := by
    have := hp.two_le
    interval_cases p
    · exact absurd rfl hp2
    · rfl
    · exact absurd hp (by norm_num)
  subst hp3
  exact ggExcToral_zpowers_of_monomialToral hp
    (monomialToralAt_three_of_block
      CFSG.HardMathSupport.Timmesfeld.Torality.a2BlockToral_F4)
    (fun _ _ a ha => (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_F4_three a ha).le)
    hpq (fun a _ => (even_power_two_Cartan_root_diagonals_inner .F4 (Or.inr (Or.inl rfl)) K
      (ringChar.eq K 2)).1 a) hs

end CFSG.StandardType

module

public import CFSG.LocalAnalysis.StandardType.GGE0ChevStMarking
public import CFSG.LocalAnalysis.StandardType.GGE0ExcNoSuzukiRee
public import CFSG.LocalAnalysis.StandardType.GGE0ExcF4
public import CFSG.LocalAnalysis.StandardType.GGE0ExcE7
public import CFSG.LocalAnalysis.StandardType.GGE0ExcE8

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem excNoSuzukiReeAdj_holds
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8) : ExcNoSuzukiReeAdj τ := by
  intro K _ _ _ p hp hp2 s hs C hC hmark
  exact ggChevStMarking_of_compFieldDataQ
    (ggExcCompFieldInputQ hτ K p hp hp2 s hs C
      (CFSG.Assembly.isComponentOf_iff_open.mp hC)) hmark

theorem ggE0At_F4_holds
    : GGE0At .F4 :=
  ggE0At_F4 (excNoSuzukiReeAdj_holds (Or.inl rfl))

theorem ggE0At_E7_holds
    : GGE0At .E7 :=
  ggE0At_E7 (excNoSuzukiReeAdj_holds (Or.inr (Or.inl rfl)))

theorem ggE0At_E8_holds
    : GGE0At .E8 :=
  ggE0At_E8 (excNoSuzukiReeAdj_holds (Or.inr (Or.inr rfl)))

end CFSG.StandardType

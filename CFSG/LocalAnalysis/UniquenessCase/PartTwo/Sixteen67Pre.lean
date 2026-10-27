module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67Bot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def R16_67_preNe (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Sit1665 D V₀ V hV L → V₀ ≠ ⊥ → ∀ g : G, conjSubgroup V g ∈ calO 1 D.M V₀ V →
      Concl1667pre D V₀ V L hV g

theorem r16_67_pre_of_ne (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h61 : UC6.R6_1 D) (h1217 : R1217 D) (h129 : R129_1 D) (h159 : R15_9Small D)
    (hne : R16_67_preNe D) : R16_67_pre D := by
  intro V₀ V L hV hS hs g hg
  by_cases h0 : V₀ = ⊥
  · exact s1667_concl_bot D hSg h1219 h61 h1217 h129 h159 hS hs h0 hg
  · exact hne V₀ V L hV hS hs h0 g hg

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

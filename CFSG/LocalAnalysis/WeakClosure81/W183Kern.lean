module

public import CFSG.LocalAnalysis.WeakClosure81.W18KernBridge
public import CFSG.LocalAnalysis.WeakClosure81.W18Tail
public import CFSG.LocalAnalysis.WeakClosure81.W18ASTail
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.WeakClosure81.W18Gamma

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

variable {G : Type} [Group G] [Finite G]

namespace MinCex183

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem false_of_not_concl181_AS_kern (h162 : W3Thm162Gt2 G)
    (h172 : W3Thm172Weak G) (h5_4 : Asch5_4) (h5_11 : Asch5_11AS) (h5_12 : Asch5_12)
    (h5_13 : Asch5_13AS) (hMult : OddMultiplierSocle185) (b2 : Tail189Two_AS G)
    (b4 : Tail189Four_AS G) (c : MinCex183 D V₀ V H i) (h1 : ¬ Concl181 D V₀ V H) : False := by
  obtain ⟨g, hgT, hgK, hgi⟩ := c.exists_conj_inf_le_T
  rcases c.relIndex_cases hgK with hA | hA
  · exact b2 h162 h172 h5_4 h5_11 h5_12 h5_13 c h1 hgT hgK hgi hA
  · exact b4 h162 h172 h5_4 h5_11 h5_12 h5_13 c h1
      (c.kerMV_le_centralizer_of_four_181 h162 h172 h5_11 h5_12 h5_13 hMult h1 hgK hgi hA)
      hgT hgK hgi hA

end MinCex183

end CFSG.LocalAnalysis.WeakClosure81

end

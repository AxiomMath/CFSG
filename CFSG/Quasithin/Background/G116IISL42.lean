module

public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

namespace G11

open CFSG.Assembly.LowTwoRank

theorem sl42IsoA8 : Nonempty (↥(StatedSL 4 (ZMod 2)) ≃* ↥(alternatingGroup (Fin 8))) := by
  have hK : Nat.card (ZMod 2) = 2 := by simp
  exact ⟨((MulEquiv.subgroupCongr
    (CFSG.GH74.Exceptional.statedSL_eq_top_of_card_two hK 4)).trans Subgroup.topEquiv).trans
      CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.symm⟩

end G11

end CFSG.Quasithin

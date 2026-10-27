module

public import Certificates.Certificate117
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerDenseDefs
import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverModel
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerModel
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKFrameCore

public section

namespace CFSG.StandardType

open CFSG.Open

section Inputs


theorem ggSecFiveBCoordBCornerPlaneFrameInput_holds :
    GGSecFiveBCoordBCornerPlaneFrameInput := by
  intro hMp G _ _ B Bs x L D J 𝒦 hR s hs eta i0 hb hM
  obtain ⟨φ, -, hφ, hφL, -⟩ :=
    exists_spPlaneTorus_model (n := s + 3) hR.1.1 (by omega) eta hb hM
  have hBs : GGBstar 3 B Bs := hR.1.1.2.1
  have hmark : GGInnerDiagOn Bs L := hR.1.2.2.1.1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let ψ : ZMod 2 ≃+* GaloisField 2 1 := (GaloisField.equivZmodP 2).toRingEquiv.symm
  let e : ↥L ≃* StatedSp (s + 2) (GaloisField 2 1) :=
    ((MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hφL)).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.statedSpCongr ψ (s + 2))
  obtain ⟨π, hπ0, κ, ζ, hframe⟩ :=
    ggSecFiveBPermSpK_exists_planeFrame_of_conj hMp (p := 3) (r := s + 1) (f := 1)
      (by norm_num) le_rfl (by omega) hBs hmark e eta hb
  exact ⟨π, hπ0, κ, ζ, hframe⟩

end Inputs

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGSporKB5Native
public import CFSG.Sporadic.Bridge.BBound
import CFSG.LocalAnalysis.StandardType.GGSporKBMBridgeZ
import CFSG.LocalAnalysis.StandardType.GGSporKBMTransportA

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint

theorem ggSporK_bmPCentralF1F4_B_five
    [Finite (TauCeti.CFSGIndex.sporadic .B).Group] :
    BMPCentralF1 5 (TauCeti.CFSGIndex.sporadic .B).Group ∧
      BMPCentralF4 5 (TauCeti.CFSGIndex.sporadic .B).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.B.nonempty_mulEquiv
  let e' : CFSG.Blueprint.NativeSporadic.B ≃* (TauCeti.CFSGIndex.sporadic .B).Group :=
    e.trans (MulEquiv.refl _)
  haveI : Finite CFSG.Blueprint.NativeSporadic.B := Finite.of_equiv _ e'.symm.toEquiv
  have h := ggSporK_bmPCentralF1F4_B_five_native
  exact ⟨@bmPCentralF1_of_mulEquiv CFSG.Blueprint.NativeSporadic.B
      (TauCeti.CFSGIndex.sporadic .B).Group _ _ _ _ 5 e' h.1,
    @bmPCentralF4_of_mulEquiv CFSG.Blueprint.NativeSporadic.B
      (TauCeti.CFSGIndex.sporadic .B).Group _ _ _ _ 5 e' h.2⟩

theorem ggSporK_bmCentreZ_B_five
    [Finite (TauCeti.CFSGIndex.sporadic .B).Group] :
    BMCentreZ 5 (TauCeti.CFSGIndex.sporadic .B).Group :=
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  bmCentreZ_of_F1_F4 5 _ ggSporK_bmPCentralF1F4_B_five.1 ggSporK_bmPCentralF1F4_B_five.2

end CFSG.StandardType.SporadicShape

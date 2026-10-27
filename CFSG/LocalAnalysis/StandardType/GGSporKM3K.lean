module

public import CFSG.LocalAnalysis.StandardType.GGSporKM3Gmat
public import CFSG.Sporadic.Bridge.MonsterModels
public import CFSG.RankThree.PartOne.SPOR.OuterM
import CFSG.LocalAnalysis.StandardType.GGSporKBMBridgeZ
import CFSG.LocalAnalysis.StandardType.GGSporKBMTransportA

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly
open CFSG.Monster.Generated

theorem ggSporK_bmPCentralF1F4_M_three_of_simple
    
    [Finite (TauCeti.CFSGIndex.sporadic .M).Group]
    (hS : IsSimpleGroup (TauCeti.CFSGIndex.sporadic .M).Group) :
    BMPCentralF1 3 (TauCeti.CFSGIndex.sporadic .M).Group ∧
      BMPCentralF4 3 (TauCeti.CFSGIndex.sporadic .M).Group := by
  obtain ⟨e⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_y443Derived_tauCeti
  haveI := hS
  let e' : (TauCeti.CFSGIndex.sporadic .M).Group ≃* CFSG.Blueprint.NativeSporadic.Carrier .M :=
    e.symm.trans (MulEquiv.refl _)
  obtain ⟨f⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple
    (T := (TauCeti.CFSGIndex.sporadic .M).Group) e'
  haveI : Finite CFSG.Monster.Generated.Gmat :=
    CFSG.Monster.Generated.generated_rational_group_finite_simple.2.2
  exact ⟨bmPCentralF1_of_mulEquiv 3 f.symm ggSporK_bmPCentralF1F4_gmat_three.1,
    bmPCentralF4_of_mulEquiv 3 f.symm ggSporK_bmPCentralF1F4_gmat_three.2⟩

theorem ggSporK_bmCentreZ_M_three_of_simple
    
    [Finite (TauCeti.CFSGIndex.sporadic .M).Group]
    (hS : IsSimpleGroup (TauCeti.CFSGIndex.sporadic .M).Group) :
    BMCentreZ 3 (TauCeti.CFSGIndex.sporadic .M).Group :=
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  bmCentreZ_of_F1_F4 3 _ (ggSporK_bmPCentralF1F4_M_three_of_simple hS).1
    (ggSporK_bmPCentralF1F4_M_three_of_simple hS).2

end CFSG.StandardType.SporadicShape

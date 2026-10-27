module

public import CFSG.LocalAnalysis.StandardType.GGQ2NoTwoNodeAssembly
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRawNoTwoNode

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly GGQ2Frame

@[expose] noncomputable def excCatalogue : FrameKind → RawFrameData
  | .exceptional m => excRaw m
  | k => emptyEntry k

theorem excCatalogue_kind (k : FrameKind) (hk : IsExceptional k) : (excCatalogue k).kind = k := by
  cases k with
  | exceptional m => rfl
  | _ => exact (hk trivial).elim

theorem ggQTwoNoTwoNodeIndInput_of_excRaw
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hrig : GGLabelRigidInput)
    (hplCl : PlacementCoreInputOn ClassicalLabel (catalogueOf classicalCatalogue excCatalogue))
    (hplEx : PlacementCoreInputOn ExceptionalLabel (catalogueOf classicalCatalogue excCatalogue)) :
    GGQTwoNoTwoNodeIndInput := by
  refine ggQTwoNoTwoNodeIndInput_of_halves hLB hP hrig excCatalogue excCatalogue_kind ?_ ?_ hplCl hplEx
  · intro k hk
    cases k with
    | exceptional m => exact fun c _ lab h => h
    | _ => exact (hk trivial).elim
  · intro k hk
    cases k with
    | exceptional m => exact rawNoInternalTwoNode_excRaw m
    | _ => exact (hk trivial).elim

end CFSG.StandardType

end

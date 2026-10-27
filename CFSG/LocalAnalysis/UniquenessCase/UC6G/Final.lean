module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.KFacts
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35OmDirect
public import CFSG.LocalAnalysis.UniquenessCase.UC6K620ExcAHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC6K323
public import CFSG.LocalAnalysis.UniquenessCase.UC6KMultL2
public import CFSG.LocalAnalysis.UniquenessCase.UC6K324Holds
public import CFSG.LocalAnalysis.UniquenessCase.UCKQSCrossMain
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332THolds
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35cDirect
public import CFSG.LocalAnalysis.UniquenessCase.UCK461Holds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.Yardstones.Mf4cdcdf2e013 (TheoremCAt)

section


theorem r6_14_of_hooks
    {G : Type} [Group G] [Finite G] {Dat : Data G} (hk : Hooks Dat)
    (hC : TheoremCAt Dat.M) (h67 : R6_7 Dat) : R6_14 Dat :=
  r6_14_of_kernelsW hk hC h67 (KernelsW.of_facts
    { kMult := UCK.kMult_holds
      kMult3 := UCK.kMult3_holds
      kSch := UCK.kSch_holds
      k35Om := UCK.K35Ω_holds
      k620exc := UCK.k620exc_holds
      k322 := UCK.k322_holds
      k323 := UCK.k323_holds
      kProjRepTits := fun J _ _ hq N _ hN h q hq' hq5 d hd f =>
        UCK.kProjRep_Tits J hq N hN h q hq' hq5 d hd f
      kProjRepA10 := fun J _ _ hq N _ hN h q hq' hq5 d hd f =>
        UCK.kProjRep_A10 J hq N hN h q hq' hq5 d hd f
      kProjRepL2 := UCK.kProjRepL2_holds
      kMultL2 := UCK.kMultL2_holds
      k324 := UCK.k324_holds
      kOutP := UCK.kOutP_holds
      kqs := UCK.kqs_holds
      k332three := UCK.k332Three_holds
      k35c := UCK.k35c_holds
      k631 := UCK.k631_holds
      ksz := UCK.kSz_holds
      k461 := UCK.k461_holds })

end

end CFSG.LocalAnalysis.UniquenessCase.UC6G

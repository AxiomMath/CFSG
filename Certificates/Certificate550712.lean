module

public import Certificates.Data.YamakiAmalgam
import Certificates.Kernel.Misc.YamakiAut.FinalCC

public section

namespace Certificates

open CFSG.ClassicalInvolution.Solomon73.Yamaki in
theorem certificate550712 :
    (crGenCheck () = true)
    ∧ (autCheck () = true)
    ∧ (CFSG.ClassicalInvolution.Solomon73.Yamaki.stabCheck () = true)
    ∧ (stdCheck () = true)
    ∧ (c1Check () = true)
    ∧ (c2Check () = true)
    ∧ (CFSG.ClassicalInvolution.Solomon73.Yamaki.chainCheck () = true) :=
  ⟨CFSG.KD.YamakiAutM.crGenCheck_holds, CFSG.KD.YamakiAutM.autCheck_holds,
    CFSG.KD.YamakiAutM.stabCheck_holds, CFSG.KD.YamakiAutM.stdCheck_holds,
    CFSG.KD.YamakiAutM.c1Check_holds, CFSG.KD.YamakiAutM.c2Check_holds,
    CFSG.KD.YamakiAutM.chainCheck_holds⟩

end Certificates

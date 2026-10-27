module

public import Certificates.Data.G23Emb
import Certificates.Kernel.Misc.G23EmbFacts

public section

namespace Certificates

open CFSG.CGT.PushingUpLit.CGT6.EmbModule in
theorem certificate271037 : coverEmbCheck = true :=
  CFSG.KD.Misc.G23Emb.coverEmbCheck_true

end Certificates

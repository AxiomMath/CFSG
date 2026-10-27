module

public import Certificates.Data.E8Frame
import Certificates.Data.E8FrameFast

public section

namespace Certificates

open CFSG.LieType.Chevalley.E8Frame

theorem certificate20190 : CFSG.LieType.Chevalley.E8Frame.gensCheck () = true ∧
    CFSG.LieType.Chevalley.E8Frame.reflCheck () = true ∧
    CFSG.LieType.Chevalley.E8Frame.frameCheck () = true ∧
    CFSG.LieType.Chevalley.E8Frame.lineCheck () = true :=
  ⟨by rw [Certificates.E8FrameFast.gensCheck_eq_gensCheckFast]; decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

end Certificates

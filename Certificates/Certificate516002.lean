module

public import Certificates.Data.S5RowsM12
import CFSG.Certificates.Kernel.PermCent.S7M12CSound
import Certificates.Kernel.PermCent.K516002
public import Certificates.Data.Kernel.PermCent.CV
import CFSG.Certificates.Kernel.PermCent.S7Q8MapSound

public section

open CFSG.Blueprint CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.S7M12C Certificates.S5Rows
  Certificates.S5RowsM12 Certificates.S7Q8

namespace Certificates

open Certificates.S5RowsM12 in
theorem certificate516002 : m12RowsF2a () = true ∧ m12RowsF2b () = true := by
  have hs := NativeSporadic.M12.subtype_injective
  have he : Function.Injective (evHom 12) := ev_injective
  refine ⟨?_, ?_⟩
  · have h : threeCycCheck (sylowL ()) (czL ()) (fun _ => true) =
        threeCycCheck ((sylowL ()).map NativeSporadic.M12.subtype)
          ((czL ()).map NativeSporadic.M12.subtype) (fun _ => true) :=
      (threeCycCheck_map _ hs (sylowL ()) (czL ()) fun _ => true).symm
    rw [m12RowsF2a, h, sylowL_map, czL_map, threeCycCheck_map _ he, ← threeCycCheck_filter_ord4]
    exact K516002.k516002_f2a
  · have h : invPairCheck (sylowL ()) M12Model.fp =
        invPairCheck ((sylowL ()).map NativeSporadic.M12.subtype) M12Model.fixPts :=
      (invPairCheck_map _ hs (sylowL ()) M12Model.fixPts).symm
    rw [m12RowsF2b, h, sylowL_map, invPairCheck_map _ he]
    simp only [evHom_apply, fixPts_ev]
    exact K516002.k516002_f2b

end Certificates

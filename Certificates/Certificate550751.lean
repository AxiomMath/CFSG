module

public import Certificates.Data.YamakiG3
import CFSG.Certificates.Kernel.Misc.YamakiBicomSound
import Certificates.Kernel.Misc.YamakiBicom.Checks

public section

open CFSG.KD.YamakiBicom CFSG.KC.YamakiBicom

namespace Certificates

open CFSG.ClassicalInvolution.Solomon73.Yamaki in
theorem certificate550751 : BicomExpand ∧ BicomCommute :=
  ⟨ch550751_expand, bicomCommute_of rfl ch550751_basis
    (List.forall₂_iff_zip.2 ⟨rfl, fun h => ch550751_gens _ h⟩) ch550751_g8 ch550751_check⟩

end Certificates

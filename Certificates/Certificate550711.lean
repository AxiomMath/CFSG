module

public import Certificates.Kernel.Misc.YamakiRep.FinalF
public import Certificates.Kernel.Misc.YamakiRep.Pos550711
public import CFSG.Certificates.Kernel.Misc.YamakiGenPosSound

public section

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.KD.YamakiRepF CFSG.KD.YamakiGenPos
  CFSG.KC.YamakiGenPos

namespace CertificateChecks.Batch550711

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.KD.YamakiRepF CFSG.KD.YamakiGenPos
  CFSG.KC.YamakiGenPos

theorem enumCheck_holds : enumCheck () = true := by
  rw [enumCheck, enumX_repF.2.1, enumN_repF.2.1, enumH_repF.2.1]
  rfl

theorem sizeCheck_holds : sizeCheck () = true := by
  rw [sizeCheck, enumX_repF.1.1, enumN_repF.1.1, enumH_repF.1.1]
  rfl

theorem tablesGenCheck_holds : tablesGenCheck () = true := by
  have hX := lookups_of_pos enumX_repF.1 yfX_gens (by decide) ch550711pX
  have hN := lookups_of_pos enumN_repF.1 yfN_gens (by decide) ch550711pN
  have hH := lookups_of_pos enumH_repF.1 yfH_gens (by decide) ch550711pH
  rw [tablesGenCheck, idxX0, idxN0, idxHhat, hX, hN, hH]
  rfl

end CertificateChecks.Batch550711

namespace Certificates

open CertificateChecks

open CFSG.ClassicalInvolution.Solomon73.Yamaki in
theorem certificate550711 :
    (enumCheck () = true)
    ∧ (sizeCheck () = true)
    ∧ (tablesGenCheck () = true) :=
  ⟨CertificateChecks.Batch550711.enumCheck_holds, CertificateChecks.Batch550711.sizeCheck_holds,
    CertificateChecks.Batch550711.tablesGenCheck_holds⟩

end Certificates

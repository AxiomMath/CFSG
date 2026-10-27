module

public import CFSG.LieType.Steinberg.Minuscule.ValidInputs
import Certificates.Certificate113
import Certificates.Certificate114
import Certificates.Certificate115

public noncomputable section

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule

end

namespace CertificateChecks.Batch116

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule

open CFSG.Blueprint.Chevalley

namespace MinData

variable {τ : Tag} (D : MinData τ)

namespace Valid

variable {D} (hV : D.Valid)
include hV

end Valid

end MinData

private theorem e6Data_checkExtra : e6Data.checkExtra = true := by decide +kernel

private theorem e7Data_checkExtra : e7Data.checkExtra = true := by decide +kernel

end CertificateChecks.Batch116

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule in
open CFSG.Blueprint.Chevalley in
theorem certificate116 : (e6Data.checkExtra = true)
    ∧ (e7Data.checkExtra = true) := by
  exact ⟨CertificateChecks.Batch116.e6Data_checkExtra, CertificateChecks.Batch116.e7Data_checkExtra⟩

end Certificates

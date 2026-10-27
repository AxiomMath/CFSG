module

public import CFSG.LieType.Steinberg.TwistedE6.CertInputs
import Certificates.Certificate113
import Certificates.Certificate114
import Certificates.Certificate115

public section

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6

namespace CertificateChecks.Batch123

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule

private theorem checkPerm_eq : checkPerm = true := by decide +kernel

private theorem checkRho_eq : checkRho = true := by decide +kernel

private theorem checkTranspose_eq : checkTranspose = true := by decide +kernel

private theorem checkSimple_eq : checkSimple = true := by decide +kernel

end CertificateChecks.Batch123

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6 in
open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule in
theorem certificate123 : (checkPerm = true)
    ∧ (checkRho = true)
    ∧ (checkTranspose = true)
    ∧ (checkSimple = true) := by
  exact ⟨CertificateChecks.Batch123.checkPerm_eq, CertificateChecks.Batch123.checkRho_eq, CertificateChecks.Batch123.checkTranspose_eq, CertificateChecks.Batch123.checkSimple_eq⟩

end Certificates

module

public import CFSG.Blueprint.ChevalleyRootsInputs

public section

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley

namespace CertificateChecks.Batch113

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley

namespace RootCertificate

variable {τ : Tag} (C : RootCertificate τ)

variable {C}

end RootCertificate

private theorem g2Certificate_check : g2Certificate.check = true := by decide +kernel

private theorem f4Certificate_check : f4Certificate.check = true := by decide +kernel

private theorem d4Certificate_check : d4Certificate.check = true := by decide +kernel

private theorem e6Certificate_check : e6Certificate.check = true := by decide +kernel

private theorem e7Certificate_check : e7Certificate.check = true := by decide +kernel

private theorem e8Certificate_check : e8Certificate.check = true := by decide +kernel

namespace Tag

end Tag

namespace RootCertificate

variable {τ : Tag} (C : RootCertificate τ)

end RootCertificate

private theorem g2Certificate_checkSigns : g2Certificate.checkSigns = true := by decide +kernel
private theorem f4Certificate_checkSigns : f4Certificate.checkSigns = true := by decide +kernel
private theorem d4Certificate_checkSigns : d4Certificate.checkSigns = true := by decide +kernel
private theorem e6Certificate_checkSigns : e6Certificate.checkSigns = true := by decide +kernel
private theorem e7Certificate_checkSigns : e7Certificate.checkSigns = true := by decide +kernel
private theorem e8Certificate_checkSigns : e8Certificate.checkSigns = true := by decide +kernel

private theorem g2Certificate_checkNodup : g2Certificate.checkNodup = true := by decide +kernel
private theorem f4Certificate_checkNodup : f4Certificate.checkNodup = true := by decide +kernel
private theorem d4Certificate_checkNodup : d4Certificate.checkNodup = true := by decide +kernel
private theorem e6Certificate_checkNodup : e6Certificate.checkNodup = true := by decide +kernel
private theorem e7Certificate_checkNodup : e7Certificate.checkNodup = true := by decide +kernel
private theorem e8Certificate_checkNodup : e8Certificate.checkNodup = true := by decide +kernel

namespace Tag

end Tag

end CertificateChecks.Batch113

namespace Certificates

open CertificateChecks

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley in
theorem certificate113 : (g2Certificate.check = true)
    ∧ (f4Certificate.check = true)
    ∧ (d4Certificate.check = true)
    ∧ (e6Certificate.check = true)
    ∧ (e7Certificate.check = true)
    ∧ (e8Certificate.check = true)
    ∧ (g2Certificate.checkSigns = true)
    ∧ (f4Certificate.checkSigns = true)
    ∧ (d4Certificate.checkSigns = true)
    ∧ (e6Certificate.checkSigns = true)
    ∧ (e7Certificate.checkSigns = true)
    ∧ (e8Certificate.checkSigns = true)
    ∧ (g2Certificate.checkNodup = true)
    ∧ (f4Certificate.checkNodup = true)
    ∧ (d4Certificate.checkNodup = true)
    ∧ (e6Certificate.checkNodup = true)
    ∧ (e7Certificate.checkNodup = true)
    ∧ (e8Certificate.checkNodup = true) := by
  exact ⟨CertificateChecks.Batch113.g2Certificate_check, CertificateChecks.Batch113.f4Certificate_check, CertificateChecks.Batch113.d4Certificate_check, CertificateChecks.Batch113.e6Certificate_check, CertificateChecks.Batch113.e7Certificate_check, CertificateChecks.Batch113.e8Certificate_check, CertificateChecks.Batch113.g2Certificate_checkSigns, CertificateChecks.Batch113.f4Certificate_checkSigns, CertificateChecks.Batch113.d4Certificate_checkSigns, CertificateChecks.Batch113.e6Certificate_checkSigns, CertificateChecks.Batch113.e7Certificate_checkSigns, CertificateChecks.Batch113.e8Certificate_checkSigns, CertificateChecks.Batch113.g2Certificate_checkNodup, CertificateChecks.Batch113.f4Certificate_checkNodup, CertificateChecks.Batch113.d4Certificate_checkNodup, CertificateChecks.Batch113.e6Certificate_checkNodup, CertificateChecks.Batch113.e7Certificate_checkNodup, CertificateChecks.Batch113.e8Certificate_checkNodup⟩

end Certificates

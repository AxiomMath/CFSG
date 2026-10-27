module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResHSext3Data
public import Certificates.Certificate11003

public section

namespace CertificateChecks.Batch25761

private theorem sext3Data_0 : CFSG.EvenSporadicStandard.M24Std.DResH.Sext3Data := by
  decide +kernel

end CertificateChecks.Batch25761

namespace Certificates

open CertificateChecks

theorem certificate25761 : CFSG.EvenSporadicStandard.M24Std.DResH.Sext3Data :=
  CertificateChecks.Batch25761.sext3Data_0

end Certificates

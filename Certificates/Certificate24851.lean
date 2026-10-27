module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.PairData

public section

namespace CertificateChecks.Batch24851

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem octadCentData_0 : CFSG.EvenSporadicStandard.M24Std.OctadCentData := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem octadTransData_1 : CFSG.EvenSporadicStandard.M24Std.OctadTransData := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem octadFixData_2 : CFSG.EvenSporadicStandard.M24Std.OctadFixData := by
  decide +kernel

end CertificateChecks.Batch24851

namespace Certificates

open CertificateChecks

theorem certificate24851 : CFSG.EvenSporadicStandard.M24Std.OctadCentData ∧
    CFSG.EvenSporadicStandard.M24Std.OctadTransData ∧
    CFSG.EvenSporadicStandard.M24Std.OctadFixData :=
  ⟨CertificateChecks.Batch24851.octadCentData_0, CertificateChecks.Batch24851.octadTransData_1, CertificateChecks.Batch24851.octadFixData_2⟩

end Certificates

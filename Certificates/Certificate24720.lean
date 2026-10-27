module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Data

public section

namespace CertificateChecks.Batch24720

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem squareData_0 : CFSG.EvenSporadicStandard.M24Std.SquareData := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem nineData_1 : CFSG.EvenSporadicStandard.M24Std.NineData := by
  decide +kernel

end CertificateChecks.Batch24720

namespace Certificates

open CertificateChecks

theorem certificate24720 : CFSG.EvenSporadicStandard.M24Std.SquareData ∧
    CFSG.EvenSporadicStandard.M24Std.NineData := by
  exact ⟨CertificateChecks.Batch24720.squareData_0, CertificateChecks.Batch24720.nineData_1⟩

end Certificates

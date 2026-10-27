module

public import Certificates.Data.GHarrisGL42

public section

open CFSG.ComponentClassification.GHarris

namespace CertificateChecks.Batch22612

open CFSG.ComponentClassification.GHarris

set_option maxHeartbeats 0 in
private theorem close_0 : ∀ k ∈ List.range 70, ∀ i ∈ List.range 12, GL42.closeIdx k i < 70 ∧
    GL42.SetEq (GL42.conjT (GL42.transAt i) (GL42.conjAt k)) (GL42.conjAt (GL42.closeIdx k i)) := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem wit_1 : ∀ k ∈ List.range 70, GL42.WitP (GL42.conjAt k) (GL42.witAt k) := by
  decide +kernel

end CertificateChecks.Batch22612

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GHarris in
theorem certificate22612 :
    (∀ k ∈ List.range 70, ∀ i ∈ List.range 12, GL42.closeIdx k i < 70 ∧
      GL42.SetEq (GL42.conjT (GL42.transAt i) (GL42.conjAt k)) (GL42.conjAt (GL42.closeIdx k i))) ∧
    (∀ k ∈ List.range 70, GL42.WitP (GL42.conjAt k) (GL42.witAt k)) := by
  exact ⟨CertificateChecks.Batch22612.close_0, CertificateChecks.Batch22612.wit_1⟩

end Certificates

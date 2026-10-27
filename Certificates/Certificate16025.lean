module

public import CFSG.Sporadic.HNSchreier.ThreeSpec

public section

open CFSG CFSG.Sporadic CFSG.Sporadic.HNSchreier CFSG.Blueprint.NativeSporadic
  CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.He.Native Matrix Equiv

namespace CertificateChecks.Batch16025

open CFSG CFSG.Sporadic CFSG.Sporadic.HNSchreier CFSG.Blueprint.NativeSporadic
  CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.He.Native Matrix Equiv

private theorem r1_fixed_0 : 1047 ∈ FAData.sFixed[0]! := by
  decide +kernel

private theorem r2_fixed_1 : 119497 ∈ FAData.sFixed[0]! := by
  decide +kernel

end CertificateChecks.Batch16025

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.HNSchreier CFSG.Blueprint.NativeSporadic
  CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.He.Native Matrix Equiv in
theorem certificate16025 : (
    1047 ∈ FAData.sFixed[0]!
  ) ∧ (
    119497 ∈ FAData.sFixed[0]!
  ) := by
  exact ⟨CertificateChecks.Batch16025.r1_fixed_0, CertificateChecks.Batch16025.r2_fixed_1⟩

end Certificates

module

public import Certificates.Kernel.Fi22Nine.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 CFSG.Monster.B.Fischer in
theorem certificate744107 :     IndexNinePackage ↥(fi22P.subgroupOf fi22R) ∧ IndexThreePackage ↥(fi22P.subgroupOf fi22R) := by
  intros
  exact ⟨KernelSpor.Fi22Nine.index_nine_package, KernelSpor.Fi22Nine.index_three_package⟩

end Certificates

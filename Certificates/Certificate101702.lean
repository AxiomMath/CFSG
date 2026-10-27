module

public import CFSG.Certificates.Kernel.BabyMonster.TwoDFiveAFacts
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.BabyMonster.TwoDFiveA.Mem
import Certificates.Kernel.BabyMonster.Seeds

public section

namespace Certificates

open CertificateChecks

open CFSG.Blueprint CFSG.KC.BM

open CFSG.Blueprint.NativeSporadic in
theorem certificate101702 : ∃ T Y, T ∈ seedMonoid 2 4370 1 BSeed1 BSeed2 ∧ Y ∈ seedMonoid 2 4370 1 BSeed1 BSeed2 ∧
    CFSG.KC.BM.TwoDFiveA.Fact101702 T Y :=
  KernelBM.TwoDFiveA.fact101702_mem
    (by rw [← CertificateChecks.KernelBM.genA₁_eq_stripMat]; exact Submonoid.subset_closure (Set.mem_insert _ _))
    (by rw [← CertificateChecks.KernelBM.genA₂_eq_stripMat]; exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl))

end Certificates

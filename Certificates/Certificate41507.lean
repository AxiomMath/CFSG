module

public import Certificates.Data.WCSporRot
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenCensusRot
import Certificates.Kernel.BabyMonster.MultSeven.Glue
import Certificates.Kernel.BabyMonster.Seeds

public section

namespace Certificates

open CFSG.Blueprint

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance in
theorem certificate41507 : ∃ x y h k : CFSG.Blueprint.NativeSporadic.B, RotSevenData x y h k :=
  CFSG.KC.BM.MultSevenGlue.rotSevenData_of_seeds
    (by rw [← CertificateChecks.KernelBM.genA₁_eq_stripMat]; exact Submonoid.subset_closure (Set.mem_insert _ _))
    (by rw [← CertificateChecks.KernelBM.genA₂_eq_stripMat]; exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl))

end Certificates

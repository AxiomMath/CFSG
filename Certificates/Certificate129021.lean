module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.Heisenberg
import Certificates.Kernel.BabyMonster.Three.Cert
import Certificates.Kernel.BabyMonster.Seeds
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec

public section

namespace Certificates

open CFSG.Blueprint

open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit in
theorem certificate129021 : ∃ (x y : Fin 4 → CFSG.Blueprint.NativeSporadic.B) (z : CFSG.Blueprint.NativeSporadic.B),
    HeisCfg 3 4 x y z ∧ ∀ i, y i ^ 3 = 1 :=
  CFSG.KC.BM.ThreeCert.cert129021_of_seeds
    (by rw [← CertificateChecks.KernelBM.genA₁_eq_stripMat]; exact Submonoid.subset_closure (Set.mem_insert _ _))
    (by rw [← CertificateChecks.KernelBM.genA₂_eq_stripMat]; exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl))

end Certificates

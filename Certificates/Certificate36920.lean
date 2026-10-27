module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.Heisenberg
public import CFSG.HardMathSupport.Solomon.Coordinator.B3B.BNFCheck
public import CFSG.HardMathSupport.Solomon.Coordinator.B3B.BNFProd
import Certificates.Kernel.BabyMonster.Three.Cert
import Certificates.Kernel.BabyMonster.Seeds
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec

public section

namespace Certificates

open CFSG.Blueprint

open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit CFSG.HardMathSupport.Solomon.Coordinator.B3B in
theorem certificate36920 : ∃ (x y : Fin 4 → CFSG.Blueprint.NativeSporadic.B) (z : CFSG.Blueprint.NativeSporadic.B)
      (g : Fin 2 → CFSG.Blueprint.NativeSporadic.B),
    HeisCfg 3 4 x y z ∧ (∀ i, y i ^ 3 = 1) ∧
    (∀ (k : Fin 2) (j : Fin 4),
      g k * x j * (g k)⁻¹ = nfProd x y z (nfXData.getD (4 * k.val + j.val) [])) ∧
    (∀ (k : Fin 2) (j : Fin 4),
      g k * y j * (g k)⁻¹ = nfProd x y z (nfYData.getD (4 * k.val + j.val) [])) ∧
    (∀ k : Fin 2, g k * z * (g k)⁻¹ = z ^ 2) ∧ Matrix.rank (z.val.val - 1) = 2916 :=
  CFSG.KC.BM.ThreeCert.cert36920_of_seeds
    (by rw [← CertificateChecks.KernelBM.genA₁_eq_stripMat]; exact Submonoid.subset_closure (Set.mem_insert _ _))
    (by rw [← CertificateChecks.KernelBM.genA₂_eq_stripMat]; exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl))

end Certificates

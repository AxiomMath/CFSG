module

public import Certificates.Data.CFSGNative.ComponentPrimary.BabyMonster
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.BabyMonster.MultSeven.Glue
import Certificates.Kernel.BabyMonster.Seeds

public section

namespace Certificates

open CFSG.Blueprint

theorem certificate291120 : ∃ x y h : CFSG.Blueprint.NativeSporadic.B,
    x ^ 7 = 1 ∧ y ^ 7 = 1 ∧ x * y = y * x ∧
      Nat.card (Subgroup.closure ({x, y} : Set CFSG.Blueprint.NativeSporadic.B)) = 7 ^ 2 ∧
      h * x * h⁻¹ = x ^ 0 * y ^ 1 ∧ h * y * h⁻¹ = x ^ 3 * y ^ 5 :=
  CFSG.KC.BM.MultSevenGlue.square_of_seeds
    (by rw [← CertificateChecks.KernelBM.genA₁_eq_stripMat]; exact Submonoid.subset_closure (Set.mem_insert _ _))
    (by rw [← CertificateChecks.KernelBM.genA₂_eq_stripMat]; exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl))

end Certificates

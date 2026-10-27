module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.Heisenberg
import Certificates.Kernel.W4RowFi22W.Glue
public import CFSG.Sporadic.FischerOddCore.Fi22ExtBase

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore in
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit in
theorem certificate1037102 : (∀ k < 6, fi22ExtRep k * fi22ExtRep k = 1) ∧
    ((∃ c ∈ fi22P, orderOf (fi22ExtRep 0 * (c * fi22ExtRep 0 * c⁻¹)) = 13) ∧
      (∃ c ∈ fi22P, orderOf (fi22ExtRep 3 * (c * fi22ExtRep 3 * c⁻¹)) = 11) ∧
      ∃ c ∈ fi22P, orderOf (fi22ExtRep 5 * (c * fi22ExtRep 5 * c⁻¹)) = 11) ∧
    (∃ c ∈ fi22P, orderOf (fi22ExtRep 1 * (c * fi22ExtRep 1 * c⁻¹)) = 5 ∧
      ∃ g ∈ fi22P, g * (fi22ExtRep 1 * (c * fi22ExtRep 1 * c⁻¹)) * g⁻¹ =
        (fi22ExtRep 1 * (c * fi22ExtRep 1 * c⁻¹)) ^ 2) ∧
    ∀ k < 6, ∃ (x y : Fin 3 → Equiv.Perm (Fin 3510)) (z : Equiv.Perm (Fin 3510)),
      (∀ i, x i ∈ fi22P) ∧ (∀ i, y i ∈ fi22P) ∧ z ∈ fi22P ∧ HeisCfg 3 3 x y z ∧
        (∀ i, y i ^ 3 = 1) ∧ fi22ExtRep k * x 0 * (fi22ExtRep k)⁻¹ = (x 0)⁻¹ :=
  ⟨fun _ hk => mul_eq_one_iff_eq_inv.2 (KernelW4F22.t_inv hk).symm, KernelW4F22.w4f22_dihedral,
    KernelW4F22.w4f22_five, fun _ hk => KernelW4F22.w4f22_heisCfg hk⟩

end Certificates

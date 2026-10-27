module

public import CFSG.Monster.B.Fischer.Fi22OmegaMaxInputs
public import CFSG.HardMathSupport.Solomon.Coordinator.I24_2Fi22D4
import Certificates.Kernel.Fi22Omega.Index

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Fischer CFSG.Certificates.SetOrbit CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.RankThree.Native in
open scoped Pointwise in
theorem certificate1023301 :
    (MulAction.stabilizer fi22P (ptSet 3510 fi22OmegaU0)).index = 61776 ∧
      IsCoatom (MulAction.stabilizer fi22P (ptSet 3510 fi22OmegaU0)) ∧
      i242Y ≤ MulAction.stabilizer (Equiv.Perm (Fin 3510)) (ptSet 3510 fi22OmegaU0) ∧
      fi22FiveQ ≤ MulAction.stabilizer (Equiv.Perm (Fin 3510)) (ptSet 3510 fi22OmegaU0) :=
  ⟨KernelFi22Omega.index_eq, KernelFi22Omega.isCoatom_M0, KernelFi22Omega.i242Y_le_stab,
    KernelFi22Omega.fiveQ_le_stab⟩

end Certificates

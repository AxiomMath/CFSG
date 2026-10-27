module

public import CFSG.RankThree.Native.Fi22FiveDefs
public import Certificates.Data.Fi22Pump
import Certificates.Kernel.Sporadic.Fi22.Pump36908G
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22WitnessBase

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi22 (J a b) in
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three (xRep) in
open CFSG.Monster.B.Fischer CFSG.RankThree.Native in
open CFSG.HardMathSupport.Solomon.Coordinator.Fi22Pump (sigmaArr) in
theorem certificate36908 : 
    (∃ σ : Equiv.Perm (Fin 3510), (∀ v : Fin 3510, (sigmaArr ())[(v : ℕ)]! = σ v) ∧
        σ * MulAction.toPerm a = fi22GenPerm 0 * σ ∧
        σ * MulAction.toPerm b = fi22GenPerm 1 * σ ∧
        ∃ Y₁ Y₂ : Equiv.Perm (Fin 3510), Y₁ ∈ fi22P ∧ Y₂ ∈ fi22P ∧ orderOf Y₁ = 5 ∧
          orderOf Y₂ = 5 ∧
          Y₁ * (σ * MulAction.toPerm (xRep 3) * σ⁻¹) = σ * MulAction.toPerm (xRep 3) * σ⁻¹ * Y₁ ∧
          Y₂ * (σ * MulAction.toPerm (xRep 3) * σ⁻¹) = σ * MulAction.toPerm (xRep 3) * σ⁻¹ * Y₂ ∧
          1080 < Nat.card (Subgroup.closure ({Y₁, Y₂} : Set (Equiv.Perm (Fin 3510))))) ∧
    Nat.card {v : Fin 3510 // xRep 0 • v = v} = 0 ∧
    Nat.card {v : Fin 3510 // xRep 1 • v = v} = 27 ∧
    Nat.card {v : Fin 3510 // xRep 2 • v = v} = 36 ∧
    Nat.card {v : Fin 3510 // xRep 3 • v = v} = 126 ∧
    ∀ Z ∈ fi22P, orderOf Z = 3 → Z * fi22FiveLine 0 = fi22FiveLine 0 * Z →
      Nat.card {v : Fin 3510 // Z v = v} = 126 ∧ ∃ q ∈ fi22FiveQ, Z * q ≠ q * Z :=
  KernelSpor.Pump36908.facts

end Certificates

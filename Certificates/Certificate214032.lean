module

public import Certificates.Data.Fi22Pump
import Certificates.Kernel.Sporadic.Fi22.Pair214032G
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22WitnessBase

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three (xRep) in
open CFSG.Monster.B.Fischer CFSG.RankThree.Native in
open CFSG.HardMathSupport.Solomon.Coordinator.Fi22Pump (sigmaArr) in
theorem certificate214032 : 
    ∃ σ : Equiv.Perm (Fin 3510), (∀ v : Fin 3510, (sigmaArr ())[(v : ℕ)]! = σ v) ∧
      ∃ Y₁ Y₂ : Equiv.Perm (Fin 3510), Y₁ ∈ fi22P ∧ Y₂ ∈ fi22P ∧ orderOf Y₁ = 5 ∧
        orderOf Y₂ = 5 ∧
        Y₁ * (σ * MulAction.toPerm (xRep 3) * σ⁻¹) = σ * MulAction.toPerm (xRep 3) * σ⁻¹ * Y₁ ∧
        Y₂ * (σ * MulAction.toPerm (xRep 3) * σ⁻¹) = σ * MulAction.toPerm (xRep 3) * σ⁻¹ * Y₂ ∧
        405 ∣ Nat.card (Subgroup.closure ({Y₁, Y₂} : Set (Equiv.Perm (Fin 3510)))) :=
  KernelSpor.Pair214032.facts214032

end Certificates

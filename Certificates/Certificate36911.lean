module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Reps
import Certificates.Kernel.Fi23Pump.Glue

public section

namespace Certificates

open CertificateChecks.KernelFi23Pump

open CFSG.Sporadic.Fi23 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 in
theorem certificate36911 : 
    (∃ v ∈ Subgroup.centralizer ({t3 0} : Set J), orderOf v = 13 ∧
      ¬ 5 ∣ Nat.card (Subgroup.centralizer ({v} : Set J))) ∧
    ¬ 5 ∣ Nat.card (Subgroup.centralizer ({t3 1} : Set J)) ∧
    ¬ 25 ∣ Nat.card (Subgroup.centralizer ({t3 2} : Set J)) ∧
    (∃ y₁ ∈ Subgroup.centralizer ({t3 2} : Set J), ∃ y₂ ∈ Subgroup.centralizer ({t3 2} : Set J),
      orderOf y₁ = 5 ∧ orderOf y₂ = 5 ∧ 1080 < Nat.card (Subgroup.closure ({y₁, y₂} : Set J))) ∧
    ¬ 5 ∣ Nat.card (Subgroup.centralizer ({t3 3} : Set J)) :=
  ⟨fact_3A, fact_3B, fact_3C, fact_3C_pair, fact_3D⟩

end Certificates

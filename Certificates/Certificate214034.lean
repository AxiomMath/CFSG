module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Reps
import Certificates.Kernel.Fi23Pair.Glue

public section

public section

namespace Certificates

open CertificateChecks.KernelFi23Pair

open CFSG.Sporadic.Fi23 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 in
theorem certificate214034 : 
    (∃ a ∈ Subgroup.centralizer ({t3 0} : Set J), ∃ b ∈ Subgroup.centralizer ({t3 0} : Set J),
      orderOf a = 7 ∧ orderOf b = 7 ∧ 81 ∣ Nat.card (Subgroup.closure ({a, b} : Set J))) ∧
    ¬ 7 ∣ Nat.card (Subgroup.centralizer ({t3 1} : Set J)) ∧
    ¬ 7 ∣ Nat.card (Subgroup.centralizer ({t3 2} : Set J)) ∧
    ¬ 7 ∣ Nat.card (Subgroup.centralizer ({t3 3} : Set J)) :=
  ⟨fact_3A, fact_3B, fact_3C, fact_3D⟩

end Certificates

end

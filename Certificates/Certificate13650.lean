module

import Certificates.Kernel.ThLocal.Glue
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCentSoundBase1

public section

namespace Certificates

open CFSG.Sporadic.Th CFSG.HardMathSupport.Timmesfeld.SporadicBalance in
theorem certificate13650 :     ∃ Q : Subgroup ↥J, Nat.card Q = 3 ^ 10 ∧ ThCent.zJ ∈ Q ∧ ThCent.zJ ^ 3 = 1 ∧
      (∀ q ∈ Q, q * ThCent.zJ = ThCent.zJ * q) ∧
      (∃ u : ↥J, orderOf u = 2 ∧ u * ThCent.zJ = ThCent.zJ * u) ∧
      ∀ s ∈ Q, orderOf s = 3 → ∃ t : ↥J, IsConj s t ∧
        3 ^ 7 ≤ Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set ↥J)) ∧
        ∃ E : Subgroup ↥J, E ≤ Subgroup.centralizer ({t} : Set ↥J) ∧
          CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
          ∀ x ∈ E, x ≠ 1 → IsConj x ThCent.zJ ∨ IsConj x (ThCent.zJ ^ 2) :=
  CertificateChecks.KernelThLocal.th_local13650

end Certificates

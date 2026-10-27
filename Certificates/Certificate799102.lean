module

public import CFSG.RankThree.PartTwo.Sec21.Holder214ThetaHSData
import Certificates.Kernel.HS799102.GlueInv
import Certificates.Kernel.HS799102.GlueM12

public section

namespace Certificates

open CertificateChecks.KernelHS799102 in
open CFSG.RankThree.PartTwo.Sec21.Holder214Theta CFSG.RankThree.Native CFSG.Monster.B.Co2 in
open scoped commutatorElement in
theorem certificate799102 :
    (CFSG.Monster.B.Co2.permOfArr 100 hsThC1 ∈ hs100P ∧ CFSG.Monster.B.Co2.permOfArr 100 hsThC2 ∈ hs100P ∧
      CFSG.Monster.B.Co2.permOfArr 100 hsThC1 ^ 3 = 1 ∧ CFSG.Monster.B.Co2.permOfArr 100 hsThC2 ^ 3 = 1 ∧
      CFSG.Monster.B.Co2.permOfArr 100 hsThC1 * CFSG.Monster.B.Co2.permOfArr 100 hsThC2 =
        CFSG.Monster.B.Co2.permOfArr 100 hsThC2 * CFSG.Monster.B.Co2.permOfArr 100 hsThC1 ∧
      CFSG.Monster.B.Co2.permOfArr 100 hsThC1 ≠ 1 ∧ CFSG.Monster.B.Co2.permOfArr 100 hsThC2 ≠ 1 ∧
      CFSG.Monster.B.Co2.permOfArr 100 hsThC2 ≠ CFSG.Monster.B.Co2.permOfArr 100 hsThC1 ∧
      CFSG.Monster.B.Co2.permOfArr 100 hsThC2 ≠ CFSG.Monster.B.Co2.permOfArr 100 hsThC1 ^ 2 ∧
      CFSG.Monster.B.Co2.permOfArr 100 hsThV3 = CFSG.Monster.B.Co2.permOfArr 100 hsThV1 * CFSG.Monster.B.Co2.permOfArr 100 hsThV2 ∧
      (∀ i < 4, CFSG.Monster.B.Co2.permOfArr 100 (hsThArr (5 + i)) ∈ hs100P ∧
        CFSG.Monster.B.Co2.permOfArr 100 (hsThArr (5 + i)) * CFSG.Monster.B.Co2.permOfArr 100 hsThV1 =
          CFSG.Monster.B.Co2.permOfArr 100 hsThV1 * CFSG.Monster.B.Co2.permOfArr 100 (hsThArr (5 + i)) ∧
        CFSG.Monster.B.Co2.permOfArr 100 (hsThArr (5 + i)) * CFSG.Monster.B.Co2.permOfArr 100 hsThV2 =
          CFSG.Monster.B.Co2.permOfArr 100 hsThV2 * CFSG.Monster.B.Co2.permOfArr 100 (hsThArr (5 + i))) ∧
      ⁅CFSG.Monster.B.Co2.permOfArr 100 (hsThArr 5), CFSG.Monster.B.Co2.permOfArr 100 (hsThArr 6)⁆ = CFSG.Monster.B.Co2.permOfArr 100 hsThC1 ∧
      ⁅CFSG.Monster.B.Co2.permOfArr 100 (hsThArr 7), CFSG.Monster.B.Co2.permOfArr 100 (hsThArr 8)⁆ = CFSG.Monster.B.Co2.permOfArr 100 hsThC2) ∧
    (∀ x ∈ hs100R, x ^ 2 = 1 → x * CFSG.Monster.B.Co2.permOfArr 100 hsThC1 = CFSG.Monster.B.Co2.permOfArr 100 hsThC1 * x →
      x * CFSG.Monster.B.Co2.permOfArr 100 hsThC2 = CFSG.Monster.B.Co2.permOfArr 100 hsThC2 * x →
      x = 1 ∨ x = CFSG.Monster.B.Co2.permOfArr 100 hsThV1 ∨ x = CFSG.Monster.B.Co2.permOfArr 100 hsThV2 ∨
        x = CFSG.Monster.B.Co2.permOfArr 100 hsThV3) ∧
    (∀ Q : Subgroup (Equiv.Perm (Fin 100)), IsPGroup 2 Q →
      Q ≤ ⁅hs100P ⊓ Subgroup.centralizer {CFSG.Monster.B.Co2.permOfArr 100 hsThV1},
        hs100P ⊓ Subgroup.centralizer {CFSG.Monster.B.Co2.permOfArr 100 hsThV1}⁆ →
      ⁅hs100P ⊓ Subgroup.centralizer {CFSG.Monster.B.Co2.permOfArr 100 hsThV1},
        hs100P ⊓ Subgroup.centralizer {CFSG.Monster.B.Co2.permOfArr 100 hsThV1}⁆ ≤
          Subgroup.normalizer (Q : Set (Equiv.Perm (Fin 100))) → Q = ⊥) ∧
    (∀ Q : Subgroup (Equiv.Perm (Fin 100)), IsPGroup 2 Q →
      Q ≤ ⁅hs100P ⊓ Subgroup.centralizer {CFSG.Monster.B.Co2.permOfArr 100 hsThV2},
        hs100P ⊓ Subgroup.centralizer {CFSG.Monster.B.Co2.permOfArr 100 hsThV2}⁆ →
      ⁅hs100P ⊓ Subgroup.centralizer {CFSG.Monster.B.Co2.permOfArr 100 hsThV2},
        hs100P ⊓ Subgroup.centralizer {CFSG.Monster.B.Co2.permOfArr 100 hsThV2}⁆ ≤
          Subgroup.normalizer (Q : Set (Equiv.Perm (Fin 100))) → Q = ⊥) ∧
    (∀ Q : Subgroup (Equiv.Perm (Fin 100)), IsPGroup 2 Q →
      Q ≤ ⁅hs100P ⊓ Subgroup.centralizer {CFSG.Monster.B.Co2.permOfArr 100 hsThV3},
        hs100P ⊓ Subgroup.centralizer {CFSG.Monster.B.Co2.permOfArr 100 hsThV3}⁆ →
      ⁅hs100P ⊓ Subgroup.centralizer {CFSG.Monster.B.Co2.permOfArr 100 hsThV3},
        hs100P ⊓ Subgroup.centralizer {CFSG.Monster.B.Co2.permOfArr 100 hsThV3}⁆ ≤
          Subgroup.normalizer (Q : Set (Equiv.Perm (Fin 100))) → Q = ⊥) ∧
    (∀ Q : Subgroup (Equiv.Perm (Fin 100)), IsPGroup 2 Q →
      Q ≤ ⁅hs100P ⊓ Subgroup.centralizer {CFSG.Monster.B.Co2.permOfArr 100 hsThV1} ⊓
          Subgroup.centralizer {CFSG.Monster.B.Co2.permOfArr 100 hsThV2},
        hs100P ⊓ Subgroup.centralizer {CFSG.Monster.B.Co2.permOfArr 100 hsThV1} ⊓
          Subgroup.centralizer {CFSG.Monster.B.Co2.permOfArr 100 hsThV2}⁆ →
      ⁅hs100P ⊓ Subgroup.centralizer {CFSG.Monster.B.Co2.permOfArr 100 hsThV1} ⊓
          Subgroup.centralizer {CFSG.Monster.B.Co2.permOfArr 100 hsThV2},
        hs100P ⊓ Subgroup.centralizer {CFSG.Monster.B.Co2.permOfArr 100 hsThV1} ⊓
          Subgroup.centralizer {CFSG.Monster.B.Co2.permOfArr 100 hsThV2}⁆ ≤
          Subgroup.normalizer (Q : Set (Equiv.Perm (Fin 100))) → Q = ⊥) :=
  ⟨basic_facts, fun _ hx => invol_eq hx, o2_v1, o2_v2, o2_v3, o2_v12⟩

end Certificates

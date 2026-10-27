module

public import CFSG.RankThree.PartTwo.KFacts.ONanKS152J2Sound
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutData
import Certificates.Kernel.KS152Gen.Final

public section

namespace Certificates

open CFSG.RankThree.PartTwo.KFacts.KS152J2 CFSG.ComponentClassification.J2Cover in
theorem certificate9566 : ∃ (Tp Wp Sp : Subgroup (Equiv.Perm (Fin 315))) (z0 y0 : Equiv.Perm (Fin 315)),
    Tp ≤ genGroup 315 autStrong[0]! autStrong[1]! ∧ Nat.card Tp = 128 ∧
      Wp ≤ genGroup 315 autStrong[0]! autStrong[1]! ∧
      Wp ≤ Subgroup.closure ((fun x : Equiv.Perm (Fin 315) => x ^ 2) '' (Tp : Set _)) ∧
      Sp ≤ genGroup 315 autStrong[0]! autStrong[1]! ∧ Nat.card Sp = 27 ∧ z0 ≠ 1 ∧ z0 ∈ Sp ∧
      Sp ≤ Subgroup.centralizer ({z0} : Set (Equiv.Perm (Fin 315))) ∧
      y0 ∈ genGroup 315 autStrong[0]! autStrong[1]! ∧ y0 ^ 5 = 1 ∧ y0 ≠ 1 ∧ z0 * y0 = y0 * z0 ∧
      ∀ g ∈ genGroup 315 autStrong[0]! autStrong[1]!,
        genGroup 315 autStrong[0]! autStrong[1]! ≤ Wp ⊔ Subgroup.zpowers (g * y0 * g⁻¹) := CFSG.KD.KS152Gen.facts

end Certificates

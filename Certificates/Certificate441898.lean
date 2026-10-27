module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XSetup
import Certificates.Kernel.HN1408.XCentGlue

public section

namespace Certificates

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section4.XModel in
theorem certificate441898 : Nat.card ↥P1408 = 177408000 → ∀ T : ↥XP, T * T = 1 →
    (Nat.card ↥(centralizer ({T} : Set ↥XP)) = 768 ∨
      Nat.card ↥(centralizer ({T} : Set ↥XP)) = 384) →
    (∀ g ∈ XP, (∀ x ∈ closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408))),
        x * (T : Equiv.Perm (Fin 1408)) = T * x → g * x = x * g) →
      ∃ z₀ ∈ closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408))),
        (∀ x ∈ closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408))),
          z₀ * x = x * z₀) ∧ (g = z₀ ∨ g = z₀ * T)) ∧
    (∀ y ∈ XP, ∃ n ∈ closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408))),
      ∃ c ∈ XP, c * (T : Equiv.Perm (Fin 1408)) = T * c ∧ y = n * c) :=
  CFSG.KD.HN1408.XCent.xCentK

end Certificates

end

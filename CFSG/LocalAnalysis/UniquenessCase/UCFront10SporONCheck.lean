module

public import Certificates.Certificate812105

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10.ONK

open CFSG.ONSchreier CFSG.ONSchreier.Native Subgroup

theorem onK_check :
    (∀ (P : Sylow 2 ↥onM120Chain.originalSubgroup) (J : Subgroup ↥onM120Chain.originalSubgroup),
      (P : Subgroup ↥onM120Chain.originalSubgroup) ≤ J → J ≠ P → 3 ∣ Nat.card J) ∧
    (∀ r : ℕ, r = 5 ∨ r = 7 → ∃ y ∈ onM120Chain.originalSubgroup, orderOf y = r ∧
      ∀ k : ℕ, 0 < k → k < r →
        Nat.card ↥(centralizer {y ^ k} ⊓ onM120Chain.originalSubgroup) = r) ∧
    (∀ g ∈ onT32Chain.originalSubgroup, g * g = 1 → g ≠ 1 →
      (∀ j < 6, g * (permOfArr 32 Data.T32Chain.generators[j]! * g *
          (permOfArr 32 Data.T32Chain.generators[j]!)⁻¹) =
        permOfArr 32 Data.T32Chain.generators[j]! * g *
          (permOfArr 32 Data.T32Chain.generators[j]!)⁻¹ * g) →
      ∃ i < 7, g = onKPerm 32 onKD[i]!) ∧
    (∀ i < 7, ∀ j < 7, onKPerm 32 onKD[i]! * onKPerm 32 onKD[j]! =
        onKPerm 32 onKD[j]! * onKPerm 32 onKD[i]! →
      onKPerm 32 onKD[i]! ≠ onz32 → onKPerm 32 onKD[j]! ≠ onz32 →
      onKPerm 32 onKD[j]! ≠ onKPerm 32 onKD[i]! →
      onKPerm 32 onKD[j]! ≠ onKPerm 32 onKD[i]! * onz32 →
      ∃ w : Equiv.Perm (Fin 32),
        ((∃ a < 6, ∃ b < 6, w = permOfArr 32 Data.T32Chain.generators[a]! *
            permOfArr 32 Data.T32Chain.generators[b]! *
            (permOfArr 32 Data.T32Chain.generators[a]!)⁻¹ *
            (permOfArr 32 Data.T32Chain.generators[b]!)⁻¹) ∨
          ∃ a < 6, w = permOfArr 32 Data.T32Chain.generators[a]! ^ 4) ∧
        ¬ (w * onKPerm 32 onKD[i]! = onKPerm 32 onKD[i]! * w ∧
          w * onKPerm 32 onKD[j]! = onKPerm 32 onKD[j]! * w)) ∧
    (∃ e ∈ onT32Chain.originalSubgroup, e * e = 1 ∧ e ≠ 1 ∧ e ≠ onz32 ∧
      ∀ t ∈ onT32Chain.originalSubgroup, t * e = e * t ∨ t * e = e * onz32 * t) :=
  Certificates.certificate812105

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10.ONK

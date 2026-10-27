module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.OmGood
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.OmConj
import CFSG.SignalizerFunctorTheorem.NonLocal.OrthIrr

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.SignalizerFunctorTheorem.NonLocal.Orth
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem involGood_matrixProjectiveDerived_three [Finite K] (hK : Nat.card K = 3) (hd : 7 ≤ d)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K (Fin d → K), Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hrep : SemilinearRepresentation Q) : InvolGood (matrixProjectiveDerived Q) := by
  have hex : ∀ u w : Fin d → K, ∃ x : matrixDerived Q,
      matrixLinearIso (d := d) (K := K) x.val = eichler Q u w :=
    exists_matrixDerived_eichler hQ hT
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP K 3 := charP_of_card_eq_prime (by rwa [Fintype.card_eq_nat_card])
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  intro α hα
  obtain ⟨γ, σ₀, x, hconj, hinv, hx⟩ := exists_conj_inv_omega hK2 (by omega) hQ hex hrep hα
  obtain ⟨hxo, hxg⟩ : orderOf x = 3 ∧ IsExtraGood x := by
    rcases hx with ⟨u, w, hu0, hu, huw, hw, rfl⟩ |
      ⟨u₁, u₂, z₁, z₂, hu₁0, hu₁, hu₂, h12, hu₂s, hz₁, hz₁', hz₂, hz₂', hz, hz₁s, rfl⟩
    · exact isExtraGood_omegaEichler hK hQ hex hd hu0 hu huw hw
    · exact isExtraGood_omegaHeis hK hQ hex hd hu₁0 hu₁ hu₂ h12 hu₂s hz₁ hz₁' hz₂ hz₂' hz hz₁s
  exact Or.inl (exists_inv_extraGood_of_conj hconj hxo hinv hxg)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.OmGood
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.OmConj
public import CFSG.SignalizerFunctorTheorem.NonLocal.OrthIrr

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.SignalizerFunctorTheorem.NonLocal.Orth
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem involInvertsGood_matrixProjectiveDerived [Finite K] {p e : ℕ} [CharP K p]
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) (hd : 7 ≤ d)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K (Fin d → K), Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hrep : SemilinearRepresentation Q) : InvolInvertsGood p (matrixProjectiveDerived Q) := by
  have hex : ∀ u w : Fin d → K, ∃ x : matrixDerived Q,
      matrixLinearIso (d := d) (K := K) x.val = eichler Q u w :=
    exists_matrixDerived_eichler hQ hT
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  intro α hα
  obtain ⟨γ, σ₀, x, hconj, hinv, hx⟩ := exists_conj_inv_omega hK2 (by omega) hQ hex hrep hα
  obtain ⟨hxo, hxg⟩ : orderOf x = p ∧ IsSpecialGood p x := by
    rcases hx with ⟨u, w, hu0, hu, huw, hw, rfl⟩ |
      ⟨u₁, u₂, z₁, z₂, hu₁0, hu₁, hu₂, h12, hu₂s, hz₁, hz₁', hz₂, hz₂', hz, hz₁s, rfl⟩
    · exact good_omegaEichler hp hp2 hK h3 hQ hex hd hu0 hu huw hw
    · exact good_omegaHeis hp hp2 hK h3 hQ hex hu₁0 hu₁ hu₂ h12 hu₂s hz₁ hz₁' hz₂ hz₂' hz hz₁s
  exact exists_inv_good_of_conj hconj hxo hinv (Or.inl hxg)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

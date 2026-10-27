module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.OmPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.Map
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.OmGood

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.SignalizerFunctorTheorem.NonLocal.Orth
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem isExtraGood_omegaHeis [Finite K] (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate)
    (hex : ∀ u w : Fin d → K, ∃ x : matrixDerived Q,
      matrixLinearIso (d := d) (K := K) x.val = eichler Q u w)
    (hd : 7 ≤ d) {u₁ u₂ z₁ z₂ : Fin d → K} (hu₁0 : u₁ ≠ 0) (hu₁ : Q u₁ = 0) (hu₂ : Q u₂ = 0)
    (h12 : polar Q u₁ u₂ = 0) (hu₂s : u₂ ∉ Submodule.span K {u₁})
    (hz₁ : polar Q u₁ z₁ = 0) (hz₁' : polar Q u₂ z₁ = 0) (hz₂ : polar Q u₁ z₂ = 0)
    (hz₂' : polar Q u₂ z₂ = 0) (hz : polar Q z₁ z₂ = 0)
    (hz₁s : z₁ ∉ Submodule.span K {u₁, u₂}) :
    orderOf (matrixProjectiveProjection Q (eMat hex u₁ z₁ * eMat hex u₂ z₂)) = 3 ∧
      IsExtraGood (matrixProjectiveProjection Q (eMat hex u₁ z₁ * eMat hex u₂ z₂)) := by
  obtain ⟨ι₁, ι₂, h₁, h₂, hcomm, hcen, hι⟩ :=
    exists_heis_pair_omega hQ hex hd hu₁0 hu₁ hu₂ h12 hu₂s hz₁ hz₁' hz₂ hz₂' hz hz₁s
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP K 3 := charP_of_card_eq_prime (by rwa [Fintype.card_eq_nat_card])
  have hx1 : (⟨1, 0, 0⟩ : Heis K) ≠ 1 := fun h => one_ne_zero (congrArg Heis.a h)
  rw [← hι]
  exact ⟨(orderOf_injective ι₁ h₁ _).trans
    (orderOf_eq_prime (Heis.pow_prime_eq_one Nat.prime_three (by norm_num) _) hx1),
    isExtraGood_of_heis_pair hK h₁ h₂ hcomm hcen _⟩

theorem isExtraGood_omegaEichler [Finite K] (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate)
    (hex : ∀ u w : Fin d → K, ∃ x : matrixDerived Q,
      matrixLinearIso (d := d) (K := K) x.val = eichler Q u w)
    (hd : 7 ≤ d) {u w : Fin d → K} (hu0 : u ≠ 0) (hu : Q u = 0) (huw : polar Q u w = 0)
    (hw : w ∉ Submodule.span K {u}) :
    orderOf (matrixProjectiveProjection Q (eMat hex u w)) = 3 ∧
      IsExtraGood (matrixProjectiveProjection Q (eMat hex u w)) := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP K 3 := charP_of_card_eq_prime (by rwa [Fintype.card_eq_nat_card])
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  obtain ⟨u₂, hu₂Q, hu₂u, hu₂w, hu₂s, hwu₂⟩ :=
    exists_line_orthogonal_of_notMem_span (Q := Q) hK2 hd hw
  have h := isExtraGood_omegaHeis (u₁ := u) (u₂ := u₂) (z₁ := w) (z₂ := 0)
    hK hQ hex hd hu0 hu hu₂Q hu₂u hu₂s huw hu₂w
    (polar_zero_right Q u) (polar_zero_right Q u₂) (polar_zero_right Q w) hwu₂
  rw [eMat_zero hex u₂, mul_one] at h
  exact h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.OmHeisHom
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.Heis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.SignalizerFunctorTheorem.NonLocal.Orth
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem good_omegaHeis [Finite K] {p e : ℕ} [CharP K p] (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) (hQ : (polarBilin Q).Nondegenerate)
    (hex : ∀ u w : Fin d → K, ∃ x : matrixDerived Q,
      matrixLinearIso (d := d) (K := K) x.val = eichler Q u w)
    {u₁ u₂ z₁ z₂ : Fin d → K} (hu₁0 : u₁ ≠ 0) (hu₁ : Q u₁ = 0) (hu₂ : Q u₂ = 0)
    (h12 : polar Q u₁ u₂ = 0) (hu₂s : u₂ ∉ Submodule.span K {u₁})
    (hz₁ : polar Q u₁ z₁ = 0) (hz₁' : polar Q u₂ z₁ = 0) (hz₂ : polar Q u₁ z₂ = 0)
    (hz₂' : polar Q u₂ z₂ = 0) (hz : polar Q z₁ z₂ = 0)
    (hz₁s : z₁ ∉ Submodule.span K {u₁, u₂}) :
    orderOf (matrixProjectiveProjection Q (eMat hex u₁ z₁ * eMat hex u₂ z₂)) = p ∧
      IsSpecialGood p (matrixProjectiveProjection Q (eMat hex u₁ z₁ * eMat hex u₂ z₂)) := by
  obtain ⟨ι, hι, hι1⟩ := exists_heis_omega hQ hex hu₁0 hu₁ hu₂ h12 hu₂s hz₁ hz₁' hz₂ hz₂' hz hz₁s
  have : Fact p.Prime := ⟨hp⟩
  have hx1 : (⟨1, 0, 0⟩ : Heis K) ≠ 1 := fun h => one_ne_zero (congrArg Heis.a h)
  rw [← hι1]
  exact ⟨(orderOf_injective ι hι _).trans
    (orderOf_eq_prime (Heis.pow_prime_eq_one hp hp2 _) hx1),
    isSpecialGood_of_heis hp hp2 hK h3 hι _⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

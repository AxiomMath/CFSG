module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.SEITZ2.SU3Tv

public section

namespace CFSG.RankThree.PartOne.SEITZ5

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.SEITZ2

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem siegel_of_three [CharP K 2] (hσ : ∀ c, σ (σ c) = c) {e w : Fin n → K} {μ : K}
    (he : herm σ e e = 0) (hw : herm σ w w = 0) (hew : herm σ e w = 0) (hμ : σ μ * μ = 1)
    {t₁ t₂ t₃ : SUid σ n} (h₁ : IsTv σ t₁ (e + μ • w) 1) (h₂ : IsTv σ t₂ e 1)
    (h₃ : IsTv σ t₃ w 1) (x : Fin n → K) :
    (t₁ * t₂ * t₃) • x = x + (μ * herm σ e x) • w + (σ μ * herm σ w x) • e := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hwe : herm σ w e = 0 := herm_eq_zero_comm σ hσ hew
  rw [mul_smul, mul_smul, h₃ x, h₂ _, h₁ _]
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, he, hw, hew, hwe,
    mul_zero, add_zero, one_mul]
  match_scalars
  · ring
  · linear_combination (herm σ w x) * hμ + (herm σ w x) * h2
  · linear_combination (herm σ e x) * h2

end CFSG.RankThree.PartOne.SEITZ5

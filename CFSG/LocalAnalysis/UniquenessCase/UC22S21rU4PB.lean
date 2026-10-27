module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4PA
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3PB
public import CFSG.LocalAnalysis.UniquenessCase.UCFront12
import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace U4P

variable {D : Data G} {L K : Subgroup G} {n p : ℕ}

theorem false_of_eq_one (u : U4P D L K n p) {Ch : Choice2011 G} (h211 : S21_1 D Ch)
    (h1930 : H1930 D) (c : Ctx21 D Ch) {H₁ H₂ : Subgroup G} (hH₁ : H₁ ∈ hSet D.T D.M)
    (hH₂ : H₂ ∈ hSet D.T D.M) (hL0 : c.L0 ≤ H₁ ⊓ H₂)
    (hfX : ∀ X : Subgroup G, X ≤ D.M → D.T ≤ X → F12.InF 1 (⊤ : Subgroup (Bar2 X)) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hA : ∀ A : Subgroup G, A ≤ L → Nat.card A = r → A ∈ uniqueSet D.M)
    {b : G} (hb : b ∈ c.B0) (hbN : b ∈ normalizer (D.T : Set G)) (hbo : orderOf b = r)
    {x₀ x₁ : Bar2 D.M} (hx₀ : x₀ ∈ barImage D.M L) (hx₁ : x₁ ∈ barImage D.M K)
    (hx₀q : x₀ ^ r = 1) (hx₁q : x₁ ^ r = 1) (hx₀1 : x₀ ≠ 1)
    (hbx : uc22p21cPi D.M ⟨b, c.hBM hb⟩ = x₀ * x₁) : False :=
  u.toR3Pair.false_of_eq_one h211 h1930 c hH₁ hH₂ hL0 hfX hr hr2 hA hb hbN hbo hx₀ hx₁ hx₀q hx₁q
    hx₀1 hbx

theorem false_of_ne_one (u : U4P D L K n p) {Ch : Choice2011 G} (h211 : S21_1 D Ch)
    (h869 : F08.R869NS5 D) (h1930 : H1930 D) (c : Ctx21 D Ch) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hrL : r ∣ Nat.card L)
    (hA : ∀ A : Subgroup G, A ≤ L → Nat.card A = r → A ∈ uniqueSet D.M)
    {b : G} (hb : b ∈ c.B0) (hbN : b ∈ normalizer (D.T : Set G)) (hbo : orderOf b = r)
    {x₀ x₁ : Bar2 D.M} (hx₀ : x₀ ∈ barImage D.M L) (hx₁ : x₁ ∈ barImage D.M K)
    (hx₀q : x₀ ^ r = 1) (hx₁q : x₁ ^ r = 1)
    (hc₀ : ∀ f ∈ barImage D.M L, uc22p21cPi D.M ⟨b, c.hBM hb⟩ * f *
      (uc22p21cPi D.M ⟨b, c.hBM hb⟩)⁻¹ = x₀ * f * x₀⁻¹)
    (hc₁ : ∀ f ∈ barImage D.M K, uc22p21cPi D.M ⟨b, c.hBM hb⟩ * f *
      (uc22p21cPi D.M ⟨b, c.hBM hb⟩)⁻¹ = x₁ * f * x₁⁻¹)
    (hc : uc22p21cPi D.M ⟨b, c.hBM hb⟩ * (x₀ * x₁)⁻¹ ∈ centralizer
      ((barImage D.M L ⊔ barImage D.M K : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)))
    (hc1 : uc22p21cPi D.M ⟨b, c.hBM hb⟩ * (x₀ * x₁)⁻¹ ≠ 1) : False :=
  u.toR3Pair.false_of_ne_one h211 h869 h1930 c hr hr2 hrL hA hb hbN hbo hx₀ hx₁ hx₀q hx₁q hc₀ hc₁ hc
    hc1

end U4P

end CFSG.LocalAnalysis.UniquenessCase.UC22

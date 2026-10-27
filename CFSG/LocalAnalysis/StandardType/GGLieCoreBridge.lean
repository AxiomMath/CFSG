module

public import CFSG.LocalAnalysis.StandardType.GGSixA3PositionDefs
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LocalAnalysis.StandardType.GGSkeleton
public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompatDefs
public import CFSG.LocalAnalysis.StandardType.GGFinModelInput
public import CFSG.LocalAnalysis.StandardType.GGLatRootBridge

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel
open CFSG.Open (StatedLieTag)

@[expose] def GGLieBridgeHyp
    (t : StatedLieTag) (n f p : ℕ) {G : Type} [Group G]
    (ψ : (ggU t n f).K →* G) (G₀ D : Subgroup G) : Prop :=
  ψ.range = G₀ ∧ ψ.ker ≤ Subgroup.center (ggU t n f).K ∧
    LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) t n 2 f ∧
    D ≤ Subgroup.normalizer (G₀ : Set G) ∧ (∀ b ∈ D, GGPsiInnerDiag (ggU t n f).D ψ b) ∧
    IsElemAbelian p D ∧ D ⊓ Subgroup.centralizer (G₀ : Set G) = ⊥

theorem ggLieBridge_inf_eq_bot_of_not_dvd {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {D C : Subgroup X} (hD : IsElemAbelian p D) (hC : ¬ p ∣ Nat.card C) : D ⊓ C = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  haveI := Fact.mk hp
  by_contra hx1
  have hord : orderOf x = p := orderOf_eq_prime (hD.2 x hx.1) hx1
  apply hC
  rw [← hord]
  exact Subgroup.orderOf_dvd_natCard C hx.2

theorem ggLieBridgeHyp_of_a3Hyp
    {t : StatedLieTag} {X : Type} [Group X] [Finite X] {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {G₀ D J : Subgroup X} (h : GGA3Hyp t X n f ψ G₀ D J) :
    GGLieBridgeHyp t n f 3 ψ G₀ D := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, -, -⟩ := h
  exact ⟨h1, h2, h3, h5, h6, h7, ggLieBridge_inf_eq_bot_of_not_dvd Nat.prime_three h7 h4⟩

@[expose] def GGLieBridgeOut
    (t : StatedLieTag) (f p : ℕ) {G : Type} [Group G] (G₀ D J : Subgroup G) : Prop :=
  ∃ (θ : ↥G₀ →* ModGL (langTag t) GGL) (A : Subgroup (ModGL (langTag t) GGL)),
    θ.ker = Subgroup.center ↥G₀ ∧ θ.range = ⁅ggFixGp t f, ggFixGp t f⁆ ∧
    A ≤ ggFixGp t f ∧ IsElemAbelian p A ∧ Nat.card A = Nat.card D ∧
    (∀ d ∈ D, ∃ a ∈ A, ∀ x : ↥G₀, ∀ h : d * (x : G) * d⁻¹ ∈ G₀, θ ⟨_, h⟩ = a * θ x * a⁻¹) ∧
    (∀ a ∈ A, ∃ d ∈ D, ∀ x : ↥G₀, ∀ h : d * (x : G) * d⁻¹ ∈ G₀, θ ⟨_, h⟩ = a * θ x * a⁻¹) ∧
    (IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set G)) →
      IsComponentOf ((J.subgroupOf G₀).map θ)
        (⁅ggFixGp t f, ggFixGp t f⁆ ⊓
          Subgroup.centralizer (A : Set (ModGL (langTag t) GGL))))

@[expose] def GGLieBridge
    : Prop :=
  ∀ (p : ℕ) {G : Type} [Group G] [Finite G] (t : StatedLieTag) (n f : ℕ)
    (ψ : (ggU t n f).K →* G) (G₀ D J : Subgroup G),
    p.Prime → p ≠ 2 → GGExcFive t → 1 ≤ f → GGLieBridgeHyp t n f p ψ G₀ D →
    GGLieBridgeOut t f p G₀ D J

end CFSG.StandardType.LieCore

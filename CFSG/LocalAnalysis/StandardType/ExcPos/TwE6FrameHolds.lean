module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6Partner
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6Placement
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6BaseOfPlacement
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6FrameDefs
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6TTFiveHolds
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6TTThreeSplit
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6TTThreeUnitary
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6RankFive

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.LieCore CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LieType.Universal CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


@[expose] def TwE6PlaceAt (cond : ℕ → ℕ → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .twistedE6 n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X), GGSixPosHyp .twistedE6 n f ψ p G₀ B₁ D J L x →
    cond p f → ∀ A : Subgroup X, TwE6BigGroup n f p ψ G₀ B₁ A → ∀ hf : 1 ≤ f,
    ∀ θ : ↥G₀ →* ModGL (langTag .twistedE6) GGL,
    (∀ (k : (ggU .twistedE6 n f).K) (h : ψ k ∈ G₀), θ ⟨ψ k, h⟩ = ggIotaK .twistedE6 n f hf k) →
    θ.ker = Subgroup.center ↥G₀ → θ.range = ⁅ggFixGp .twistedE6 f, ggFixGp .twistedE6 f⁆ →
    ∀ Θ : ↥A →* ModGL (langTag .twistedE6) GGL, (∀ a : ↥A, Θ a ∈ ggFixGp .twistedE6 f) →
    (∀ a : ↥A, Θ a = 1 ↔ (a : X) ∈ Subgroup.centralizer (G₀ : Set X)) →
    (∀ a : ↥A, GGLiePartner G₀ θ (a : X) (Θ a)) → Function.Injective Θ →
    (p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) ∧ ∃ E : Subgroup (ModGL (langTag .twistedE6) GGL),
      (∀ a : ↥A, (a : X) ∈ D → Θ a ∈ E) ∧ TwE6LawPos p f E

theorem twE6FrameAt_of_place {cond : ℕ → ℕ → Prop} (hplace : TwE6PlaceAt cond)
    (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .twistedE6 n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X) (hP : GGSixPosHyp .twistedE6 n f ψ p G₀ B₁ D J L x)
    (hc : cond p f) : ∃ B : ExcBase .E6 f p G₀ B₁ D J x, TwE6BaseCompat n f p ψ B := by
  have hP' := hP
  obtain ⟨hψr, hψk, hLM, -, hp, hp2, hB₁N, hB₁inn, hB₁el, -, hDB, hDcard,
    -, -, hJ, -, hx, hx1, -, -, -, -, -, -, -, -, -, -, -, -, hlast⟩ := hP
  have hf : 1 ≤ f := by
    have hCE : ChevalleyExceptionalModel (↥G₀ ⧸ Subgroup.center ↥G₀) .twistedE6 2 f :=
      LieModel.chevalleyExceptionalModel hLM (by decide)
    exact hCE.1.2.1
  obtain ⟨A, hB₁A, hAel, hAN, hAinn, hAC, hArest⟩ := hlast (Or.inr rfl)
  have hA : TwE6BigGroup n f p ψ G₀ B₁ A :=
    ⟨hB₁A, hAel, hAN, hAinn, hAC, hArest⟩
  have hHyp : GGLieBridgeHyp .twistedE6 n f p ψ G₀ A :=
    ⟨hψr, hψk, hLM, hAN, hAinn, hAel, hAC⟩
  obtain ⟨θ, Θ, hθψ, hθker, hθrange, hΘR, hΘone, hpart⟩ :=
    exists_twE6_partner hf hp hp2 hHyp
  have hΘinj : Function.Injective Θ := by
    have hker : ∀ a : ↥A, Θ a = 1 → a = 1 := by
      intro a ha
      have hmem : (a : X) ∈ (⊥ : Subgroup X) := by
        rw [← hAC]
        exact ⟨a.2, (hΘone a).mp ha⟩
      exact Subtype.ext (Subgroup.mem_bot.mp hmem)
    rw [injective_iff_map_eq_one]
    exact hker
  obtain ⟨hreg, E, hDE, hpos⟩ := hplace X n f ψ p G₀ B₁ D J L x hP' hc A hA hf θ hθψ hθker
    hθrange Θ hΘR hΘone hpart hΘinj
  exact exists_twE6_base hf hp hp2 hreg hB₁A hDB (hB₁el.mono hDB) hDcard hx hx1 hAN hJ
    θ Θ hθψ hθker hθrange hΘR hΘone hpart E hDE hpos

theorem twE6Frame_of_units (hC : TwE6TTFive) (hD : TwE6TTThreeSplit) (hE : TwE6TTThreeUnitary)
    (hR5 : TwE6RankFive) : TwE6Frame := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hP hres
  refine twE6FrameAt_of_place (cond := fun p f => ¬ (p = 3 ∧ 3 ∣ 2 ^ f + 1 ∧ ¬ 9 ∣ 2 ^ f + 1))
    ?_ X n f ψ p G₀ B₁ D J L x hP hres
  intro X _ _ n f ψ p G₀ B₁ D J L x hP hres A hA hf _ _ _ _ Θ hΘR _ _ hΘinj
  exact twE6_placement hC hD hE hR5 hf hP hres hA Θ hΘR hΘinj

theorem twE6Frame_holds : TwE6Frame :=
  twE6Frame_of_units twE6TTFive_holds twE6TTThreeSplit_holds twE6TTThreeUnitary
    twE6RankFive_holds

end CFSG.StandardType.LieKnownR2.ExcPos

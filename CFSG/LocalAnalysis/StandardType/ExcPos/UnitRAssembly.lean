module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6FrameHolds
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6PairDefs
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6ResidualToral

public noncomputable section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.LieCore CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LieType.Universal CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


@[expose] def TwE6ResidualCond (p f : ℕ) : Prop := p = 3 ∧ 3 ∣ 2 ^ f + 1 ∧ ¬ 9 ∣ 2 ^ f + 1

@[expose] def TwE6PlaceNT : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .twistedE6 n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X), GGSixPosHyp .twistedE6 n f ψ p G₀ B₁ D J L x →
    TwE6ResidualCond p f → ∀ A : Subgroup X, TwE6BigGroup n f p ψ G₀ B₁ A → ∀ hf : 1 ≤ f,
    ∀ θ : ↥G₀ →* ModGL (langTag .twistedE6) GGL,
    (∀ (k : (ggU .twistedE6 n f).K) (h : ψ k ∈ G₀), θ ⟨ψ k, h⟩ = ggIotaK .twistedE6 n f hf k) →
    θ.ker = Subgroup.center ↥G₀ → θ.range = ⁅ggFixGp .twistedE6 f, ggFixGp .twistedE6 f⁆ →
    ∀ Θ : ↥A →* ModGL (langTag .twistedE6) GGL, (∀ a : ↥A, Θ a ∈ ggFixGp .twistedE6 f) →
    (∀ a : ↥A, Θ a = 1 ↔ (a : X) ∈ Subgroup.centralizer (G₀ : Set X)) →
    (∀ a : ↥A, GGLiePartner G₀ θ (a : X) (Θ a)) → Function.Injective Θ →
    ¬ NoOffTwE6Three.IsToralE6 GGL ((B₁.subgroupOf A).map Θ) →
    ∃ E : Subgroup (ModGL (langTag .twistedE6) GGL),
      (∀ a : ↥A, (a : X) ∈ D → Θ a ∈ E) ∧ TwE6LawPos p f E

theorem twE6PlaceAt_residual_of_nt (hnt : TwE6PlaceNT) : TwE6PlaceAt TwE6ResidualCond := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hpos hres A hA hf θ hθψ hθker hθrange Θ hΘR hΘone hpart hΘinj
  have hpos' := hpos
  obtain ⟨-, -, -, -, -, -, -, -, hB₁el, hB₁card, hDB, -⟩ := hpos
  obtain ⟨hp3, h3, h9⟩ := hres
  refine ⟨Or.inr (hp3 ▸ h3), ?_⟩
  by_cases hT : NoOffTwE6Three.IsToralE6 GGL ((B₁.subgroupOf A).map Θ)
  · subst hp3
    exact twE6_residualPlace_of_toral hf h3 hA.1 hDB hB₁el hB₁card Θ hΘR hΘinj hT
  · exact hnt X n f ψ p G₀ B₁ D J L x hpos' ⟨hp3, h3, h9⟩ A hA hf θ hθψ hθker hθrange Θ hΘR hΘone
      hpart hΘinj hT

theorem excBase_b_eq_one_of_dvd {X : Type} [Group X] {f p : ℕ} (hf : 1 ≤ f) (hp3 : p = 3)
    (h3 : 3 ∣ 2 ^ f + 1) {G₀ B₁ D J : Subgroup X} {x : X}
    (B : ExcBase .E6 f p G₀ B₁ D J x) : B.b = 1 := by
  unfold ExcBase.b ExcBase.rootsJ
  rcases B.orbit with h | ⟨-, -, hdvd, -⟩
  · exact h
  · exfalso
    subst hp3
    have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
    rw [hcard] at hdvd
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    generalize 2 ^ f = N at hdvd h3 h1
    omega

theorem excUR_of_place (hplace : TwE6PlaceAt TwE6ResidualCond) (hpair : TwE6PairOne) :
    ExcUR := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hpos hp3 h3 h9
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · rw [h] at h3
      norm_num at h3
    · exact h
  obtain ⟨B, hB⟩ := twE6FrameAt_of_place hplace X n f ψ p G₀ B₁ D J L x hpos ⟨hp3, h3, h9⟩
  have hb : B.b = 1 := excBase_b_eq_one_of_dvd hf hp3 h3 B
  obtain ⟨R, Rm, hRJ, hRmJ, hG, ⟨Pd⟩⟩ := hpair X n f ψ p G₀ B₁ D J L x hpos B hB hb
  exact ⟨R, Rm, hRJ, hRmJ, hG, ExcPacket.ofBasePair B Pd, by
    rw [ExcPacket.ofBasePair_b]
    exact hb⟩

theorem excUR_of_pieces (hnt : TwE6PlaceNT) (hpair : TwE6PairOne) : ExcUR :=
  excUR_of_place (twE6PlaceAt_residual_of_nt hnt) hpair

end CFSG.StandardType.LieKnownR2.ExcPos

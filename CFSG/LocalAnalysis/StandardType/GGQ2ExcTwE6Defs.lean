module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcPlacementDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Conj

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Open (IsElemAbelian)

noncomputable section

@[expose] def ExcTwE6Cover :
    Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G},
    GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 E H →
    ∃ hEN : E ≤ Subgroup.normalizer (H : Set G), commutator H = ⊤ ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K), Nat.card K = 4 ∧
        (∀ c, σ c = c ^ 2) ∧ ∃ ψ : ↥H →* ↥(twistedE6RootGroup K σ), Function.Surjective ψ ∧
          ψ.ker = Subgroup.center ↥H ∧ ∀ e : ↥E, ∃ φ ∈ (RecipeExcLang.twConj K σ).range,
            ∀ l : ↥H, φ (ψ l) = ψ (ggGamma H hEN e l)

@[expose] def ExcTwE6RankFive : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting 3 B Bs x L D J →
    GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs (ggG0 3 B x L D J) →
      3 ^ 5 ≤ Nat.card Bs

@[expose] def ExcTwE6ModelFrame :
    Prop :=
  ∀ {K : Type} [Field K] [Finite K] {σ : K ≃+* K}, Nat.card K = 4 → (∀ c, σ c = c ^ 2) →
    ∀ {A : Subgroup (ModGL TwistTag.E6.tag K)}, IsElemAbelian 3 A →
      A ≤ RecipeExcLang.twInndiagGroup K σ → 3 ^ 5 ≤ Nat.card A →
      (∀ c ∈ twistedE6RootGroup K σ, (∀ a ∈ A, a * c = c * a) → c ^ 3 = 1 → c ∈ A) →
      (∃ mf : ModelFrame (twistedE6RootGroup K σ) A (excRaw 2), mf.CompNormal) ∨
        ∃ mf : ModelFrame (twistedE6RootGroup K σ) A (excRaw 3), mf.CompNormal

@[expose] def ModelFrameOfEquivCover : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {H E : Subgroup G} {M : Type} [Group M] {R : RawFrameData}
    (hEN : E ≤ Subgroup.normalizer (H : Set G)) (π : ↥H →* M) (ρ : ↥E →* M),
    π.ker ≤ Subgroup.center ↥H → ¬ 3 ∣ Nat.card π.ker → commutator H = ⊤ →
    IsElemAbelian 3 E → Function.Injective ρ →
    (∀ (e : ↥E) (l : ↥H), π (ggGamma H hEN e l) = ρ e * π l * (ρ e)⁻¹) →
    (∀ (e : ↥E) (he : (e : G) ∈ H), ρ e = π ⟨e, he⟩) →
    (∀ e : ↥E, ρ e ∈ π.range → (e : G) ∈ H) →
    ∀ mf : ModelFrame π.range ρ.range R, mf.CompNormal → Nonempty (ModelFrame H E R)

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

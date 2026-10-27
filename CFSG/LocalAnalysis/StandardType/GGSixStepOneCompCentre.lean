module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs

@[expose] def GGLayerCentreOddInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    Odd (Nat.card (Subgroup.centralizer (G₀ : Set G))) → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ E : Subgroup G, IsPGroup p E → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      E ≤ Subgroup.normalizer (G₀ : Set G) → (∀ e ∈ E, GGPsiInnerDiag (ggU t n f).D ψ e) →
        Odd (Nat.card (Subgroup.center
          ↥(LargeEvenLayer (G₀ ⊓ Subgroup.centralizer (E : Set G)))))

@[expose] def GGLayerPerfectInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    Odd (Nat.card (Subgroup.centralizer (G₀ : Set G))) → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ E : Subgroup G, IsPGroup p E → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      E ≤ Subgroup.normalizer (G₀ : Set G) → (∀ e ∈ E, GGPsiInnerDiag (ggU t n f).D ψ e) →
        ∀ X : Subgroup G, X ≤ G₀ ⊓ Subgroup.centralizer (E : Set G) → ⁅X, X⁆ = X →
          X ≤ LargeEvenLayer (G₀ ⊓ Subgroup.centralizer (E : Set G))

end Inputs

section Proof

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ}
  {ψ : U →* G}

theorem GGSixCtxV2.d_isPGroup (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) : IsPGroup p D :=
  fun e => ⟨1, Subtype.ext (by simpa using h.d_elem.2 e e.2)⟩

theorem GGSixCtxV2.d_comm (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) :
    ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val (h.d_elem.1.is_comm.comm (⟨a, ha⟩ : ↥D) ⟨b, hb⟩)

theorem GGSixCtxV2.d_innerDiag (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) :
    ∀ e ∈ D, GGPsiInnerDiag Δ ψ e := fun e he => h.2.2.2.2.2.2.1.2 e (h.d_le_bstar he)

omit [Finite G] in
theorem ggCentralizer_zpowers_eq (d : G) :
    Subgroup.centralizer (Subgroup.zpowers d : Set G) = Subgroup.centralizer {d} := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem GGSixCtxV2.centre_odd
    (hlc : ∀ E : Subgroup G, E ≤ D →
      Odd (Nat.card (Subgroup.center
        ↥(LargeEvenLayer (ggG0 p B x L D J ⊓ Subgroup.centralizer (E : Set G))))))
    (hlp : ∀ E : Subgroup G, E ≤ D → ∀ X : Subgroup G,
      X ≤ ggG0 p B x L D J ⊓ Subgroup.centralizer (E : Set G) → ⁅X, X⁆ = X →
        X ≤ LargeEvenLayer (ggG0 p B x L D J ⊓ Subgroup.centralizer (E : Set G)))
    (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) :
    Odd (Nat.card (Subgroup.center ↥J)) ∧
      ∀ d ∈ D, d ≠ 1 → Odd (Nat.card (Subgroup.center ↥(ggKd p B x L D J d))) := by
  refine ⟨?_, fun d hd _ => ?_⟩
  · have hJ := h.j_isComponentOf_inf
    exact odd_card_center_of_le_layer (le_largeEvenLayer hJ) (largeEvenLayer_le_normalizer hJ)
      (hlc D le_rfl)
  · have hdD : Subgroup.zpowers d ≤ D := Subgroup.zpowers_le.mpr hd
    have hlc' := hlc _ hdD
    have hlp' := hlp _ hdD
    rw [ggCentralizer_zpowers_eq] at hlc' hlp'
    have hJE : J ≤ LargeEvenLayer (ggG0 p B x L D J ⊓ Subgroup.centralizer {d}) :=
      hlp' J (h.le_ggG0_inf hd) (commutator_self_eq_of_commutator_eq_top h.j_comp.2.2.1)
    exact odd_card_center_of_le_layer (ggKd_le_layer hJE) layer_le_normalizer_ggKd hlc'

section CtxU

theorem ggSixCentreOddInput_of_layer (hlc : GGLayerCentreOddInput) (hlp : GGLayerPerfectInput) :
    GGSixCentreOddInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx hodd
  have hE : ∀ E : Subgroup G, E ≤ D → IsPGroup p E ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧
      E ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) ∧
      ∀ e ∈ E, GGPsiInnerDiag (ggU t n f).D ψ e := fun E hED =>
    ⟨hctx.d_isPGroup.to_le hED, fun a ha b hb => hctx.d_comm a (hED ha) b (hED hb),
      hED.trans hctx.d_le_ggM, fun e he => hctx.d_innerDiag e (hED he)⟩
  refine hctx.centre_odd (fun E hED => ?_) (fun E hED => ?_)
  · obtain ⟨h1, h2, h3, h4⟩ := hE E hED
    exact hlc G t n f ψ _ hctx.presents hodd p hctx.prime hctx.ne_two E h1 h2 h3 h4
  · obtain ⟨h1, h2, h3, h4⟩ := hE E hED
    exact hlp G t n f ψ _ hctx.presents hodd p hctx.prime hctx.ne_two E h1 h2 h3 h4

end CtxU

end Proof

end CFSG.StandardType

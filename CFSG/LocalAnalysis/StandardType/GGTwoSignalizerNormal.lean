module

public import CFSG.LocalAnalysis.StandardType.GGTwoSignalizerGen
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompDefs
public import CFSG.Timmesfeld.Final.Simple
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

namespace GGTwoSig

theorem sup_eq_of_normalized {G : Type} [Group G] {G₀ Q V : Subgroup G}
    (hG₀ : CFSG.Assembly.IsQuasisimple ↥G₀) (hQ : GGRadicalTwo G₀ Q) (hQne : Q ≠ ⊥)
    (hV : V ∈ ggOppositeRadicals G₀ Q)
    (hN : G₀ ≤ Subgroup.normalizer ((Q ⊔ V : Subgroup G) : Set G)) : Q ⊔ V = G₀ := by
  rcases ggLe_center_or_eq_of_normalized hG₀ (sup_le hQ.le hV.1.le) hN with hc | h
  · exfalso
    apply hQne
    have hVle : V ≤ V ⊓ (G₀ ⊓ Subgroup.normalizer (Q : Set G)) := by
      intro v hv
      have hvc : v ∈ Subgroup.centralizer (G₀ : Set G) := hc (Subgroup.mem_sup_right hv)
      exact ⟨hv, hV.1.le hv, Subgroup.centralizer_le_normalizer (Q : Set G)
        (Subgroup.centralizer_le hQ.le hvc)⟩
    rw [hV.2.2] at hVle
    have hV1 : V = ⊥ := le_bot_iff.mp hVle
    have hcard : Nat.card Q = 1 := by rw [← hV.2.1, hV1, Subgroup.card_bot]
    exact Subgroup.eq_bot_of_card_eq Q hcard
  · exact h

section Simple

theorem isQuasisimple_of_presents {G : Type} [Group G] {U : Type} [Group U]
    {G₀ : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ} {ψ : U →* G}
    (h : GGPresentsG0 G₀ Δ t n f ψ) : CFSG.Assembly.IsQuasisimple ↥G₀ :=
  ⟨h.2.2.1, CFSG.Timmesfeld.isSimpleGroup_of_lieModel h.2.2.2⟩

end Simple

end GGTwoSig

section Inputs

@[expose] def GGOppositeRadicalCountNormalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    ∀ Q : Subgroup G, Q ≠ ⊥ → GGRadicalTwo G₀ Q →
      (∃ k : ℕ, Nat.card (ggOppositeRadicals G₀ Q) = 2 ^ k) ∧
        ∀ V ∈ ggOppositeRadicals G₀ Q,
          G₀ ≤ Subgroup.normalizer ((Q ⊔ V : Subgroup G) : Set G)

end Inputs

section Assembly

theorem ggOppositeRadicalCountInput_of_normal (h : GGOppositeRadicalCountNormalInput) :
    GGOppositeRadicalCountInput := by
  intro G _ _ t n f ψ G₀ hpres Q hQ hrad
  obtain ⟨hcount, hnorm⟩ := h G t n f ψ G₀ hpres Q hQ hrad
  exact ⟨hcount, fun V hV => GGTwoSig.sup_eq_of_normalized
    (GGTwoSig.isQuasisimple_of_presents hpres) hrad hQ hV (hnorm V hV)⟩

theorem ggTwoSignalizerGenInput_of_oppositeRadicalCountNormal
    (h : GGOppositeRadicalCountNormalInput) : GGTwoSignalizerGenInput :=
  ggTwoSignalizerGenInput_of_oppositeRadicalCount (ggOppositeRadicalCountInput_of_normal h)

end Assembly

end CFSG.StandardType

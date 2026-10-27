module

public import CFSG.LocalAnalysis.StandardType.GGTwoSignalizerRadical
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneInputs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs

@[expose] def GGOppositeRadicalExistsInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    ∀ Q : Subgroup G, Q ≠ ⊥ → GGRadicalTwo G₀ Q →
      ∃ V ∈ ggOppositeRadicals G₀ Q, Q ⊔ V = G₀

@[expose] def GGOppositeRadicalConjInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    ∀ Q : Subgroup G, Q ≠ ⊥ → GGRadicalTwo G₀ Q →
      ∀ V ∈ ggOppositeRadicals G₀ Q, ∀ V' ∈ ggOppositeRadicals G₀ Q,
        ∃ u ∈ Q, V' = V.map (MulAut.conj u).toMonoidHom

@[expose] def GGOppositeRadicalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    ∀ Q : Subgroup G, Q ≠ ⊥ → GGRadicalTwo G₀ Q →
      ∃ V ∈ ggOppositeRadicals G₀ Q, Q ⊔ V = G₀ ∧
        ∀ V' ∈ ggOppositeRadicals G₀ Q, ∃ u ∈ Q, V' = V.map (MulAut.conj u).toMonoidHom

theorem ggOppositeRadicalInput_iff : GGOppositeRadicalInput ↔
    GGOppositeRadicalExistsInput ∧ GGOppositeRadicalConjInput := by
  constructor
  · intro h
    refine ⟨fun G _ _ t n f ψ G₀ hpres Q hQ hrad => ?_,
      fun G _ _ t n f ψ G₀ hpres Q hQ hrad V hV V' hV' => ?_⟩
    · obtain ⟨V, hV, hgen, -⟩ := h G t n f ψ G₀ hpres Q hQ hrad
      exact ⟨V, hV, hgen⟩
    · obtain ⟨V₀, -, -, htr⟩ := h G t n f ψ G₀ hpres Q hQ hrad
      obtain ⟨u, hu, rfl⟩ := htr V hV
      obtain ⟨u', hu', rfl⟩ := htr V' hV'
      refine ⟨u' * u⁻¹, Q.mul_mem hu' (Q.inv_mem hu), ?_⟩
      rw [← GGTwoSig.map_conj_mul, mul_assoc, inv_mul_cancel, mul_one]
  · rintro ⟨hex, hconj⟩ G _ _ t n f ψ G₀ hpres Q hQ hrad
    obtain ⟨V, hV, hgen⟩ := hex G t n f ψ G₀ hpres Q hQ hrad
    exact ⟨V, hV, hgen, fun V' hV' => hconj G t n f ψ G₀ hpres Q hQ hrad V hV V' hV'⟩

theorem ggTwoSignalizerGenInput_of_oppositeRadical (hex : GGOppositeRadicalExistsInput)
    (hconj : GGOppositeRadicalConjInput) : GGTwoSignalizerGenInput := by
  intro G _ _ t n f ψ G₀ hpres p hp hp2 E hEp hEG₀ T hTG₀ hT hT2 hET
  exact GGTwoSig.exists_two_signalizers hp hp2 hEp hEG₀ hTG₀ hT hT2 hET
    (hex G t n f ψ G₀ hpres) (hconj G t n f ψ G₀ hpres)

theorem ggTwoSignalizerGenInput_of_oppositeRadicalInput (h : GGOppositeRadicalInput) :
    GGTwoSignalizerGenInput :=
  ggTwoSignalizerGenInput_of_oppositeRadical (ggOppositeRadicalInput_iff.mp h).1
    (ggOppositeRadicalInput_iff.mp h).2

@[expose] def GGOppositeRadicalCountInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    ∀ Q : Subgroup G, Q ≠ ⊥ → GGRadicalTwo G₀ Q →
      (∃ k : ℕ, Nat.card (ggOppositeRadicals G₀ Q) = 2 ^ k) ∧
        ∀ V ∈ ggOppositeRadicals G₀ Q, Q ⊔ V = G₀

theorem ggOppositeRadicalCountInput_of_oppositeRadicalInput (h : GGOppositeRadicalInput) :
    GGOppositeRadicalCountInput := by
  intro G _ _ t n f ψ G₀ hpres Q hQ hrad
  obtain ⟨V₀, hV₀, hgen, htr⟩ := h G t n f ψ G₀ hpres Q hQ hrad
  exact GGTwoSig.count_of_conj hrad hV₀ hgen htr

theorem ggTwoSignalizerGenInput_of_oppositeRadicalCount (h : GGOppositeRadicalCountInput) :
    GGTwoSignalizerGenInput := by
  intro G _ _ t n f ψ G₀ hpres p hp hp2 E hEp hEG₀ T hTG₀ hT hT2 hET
  exact GGTwoSig.exists_two_signalizers_of_count hp hp2 hEp hEG₀ hTG₀ hT hT2 hET
    (h G t n f ψ G₀ hpres)

end Inputs

end CFSG.StandardType

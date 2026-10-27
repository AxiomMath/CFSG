module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplit

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

theorem largeEvenRawDatum_or {lab : LargeEvenLabel} {Q₁ Q₂ : LargeEvenRawCont}
    (h : LargeEvenRawDatum lab fun R _ I F => Q₁ R I F ∨ Q₂ R I F) :
    LargeEvenRawDatum lab Q₁ ∨ LargeEvenRawDatum lab Q₂ := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [LargeEvenRawDatum] at h ⊢
  all_goals try split_ifs at h ⊢
  all_goals first
    | (obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := h
       rcases hq with hq | hq
       exacts [Or.inl ⟨K, i1, i2, hK, b, c, hbc, hq⟩, Or.inr ⟨K, i1, i2, hK, b, c, hbc, hq⟩])
    | (obtain ⟨K, i1, i2, hK, hq⟩ := h
       rcases hq with hq | hq
       exacts [Or.inl ⟨K, i1, i2, hK, hq⟩, Or.inr ⟨K, i1, i2, hK, hq⟩])

theorem largeEvenMarking_or {X : Type*} [Group X] {P Q : LargeEvenMarkProp X}
    (h : LargeEvenMarking X fun lab R _ I F θ => P lab R I F θ ∨ Q lab R I F θ) :
    LargeEvenMarking X P ∨ LargeEvenMarking X Q := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  have hraw' : LargeEvenRawDatum lab fun R _ I F =>
      (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : X ⧸ Subgroup.center X ≃* R, P lab R I F θ) ∨
      (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : X ⧸ Subgroup.center X ≃* R, Q lab R I F θ) := by
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨hs, hna, θ, hθ | hθ⟩
    exacts [Or.inl ⟨hs, hna, θ, hθ⟩, Or.inr ⟨hs, hna, θ, hθ⟩]
  rcases largeEvenRawDatum_or hraw' with h' | h'
  exacts [Or.inl ⟨hX, lab, hlab, h'⟩, Or.inr ⟨hX, lab, hlab, h'⟩]

section Inputs

@[expose] def GGNonsplitNbrHalfSplitInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ 2 ^ f - 1 → ¬ p ∣ 2 ^ f + 1 →
    ∀ x y : G, x ^ p = 1 → y ^ p = 1 → x * y = y * x →
      x ∈ Subgroup.normalizer (G₀ : Set G) → y ∈ Subgroup.normalizer (G₀ : Set G) →
      GGPsiInnerDiag (ggU t n f).D ψ x → GGPsiInnerDiag (ggU t n f).D ψ y →
      ∀ K K' : Subgroup G, IsComponentOf K (G₀ ⊓ Subgroup.centralizer {x}) →
        ¬ p ∣ Nat.card K → IsComponentOf K' (G₀ ⊓ Subgroup.centralizer {y}) → K ≤ K' →
        x ∈ Subgroup.normalizer (K' : Set G) →
          ¬ LargeEvenMarking K' fun lab _ _ _ _ _ =>
            LargeEvenHalfSplit p lab (Subgroup.center K' = ⊥)

@[expose] def GGNonsplitNbrPrimeFieldInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ 2 ^ f - 1 → ¬ p ∣ 2 ^ f + 1 →
    ∀ x y : G, x ^ p = 1 → y ^ p = 1 → x * y = y * x →
      x ∈ Subgroup.normalizer (G₀ : Set G) → y ∈ Subgroup.normalizer (G₀ : Set G) →
      GGPsiInnerDiag (ggU t n f).D ψ x → GGPsiInnerDiag (ggU t n f).D ψ y →
      ∀ K K' : Subgroup G, IsComponentOf K (G₀ ⊓ Subgroup.centralizer {x}) →
        ¬ p ∣ Nat.card K → IsComponentOf K' (G₀ ⊓ Subgroup.centralizer {y}) → K ≤ K' →
        x ∈ Subgroup.normalizer (K' : Set G) →
          ¬ LargeEvenMarking K' fun lab _ _ I F θ =>
            LargeEvenPrimeField p lab I F
              (LargeEvenInduces θ fun j j' => (j' : G) = x⁻¹ * j * x)

theorem ggNonsplitNbrMarkingInput_of_split (hHS : GGNonsplitNbrHalfSplitInput)
    (hPF : GGNonsplitNbrPrimeFieldInput) : GGNonsplitNbrMarkingInput := by
  intro G _ _ t n f ψ G₀ hpres p hp hp2 hq1 hq2 x y hxp hyp hxy hxN hyN hxD hyD K K' hK hpK
    hK' hKK' hxK' hmark
  rcases largeEvenMarking_or hmark with h | h
  · exact hHS G t n f ψ G₀ hpres p hp hp2 hq1 hq2 x y hxp hyp hxy hxN hyN hxD hyD K K' hK hpK
      hK' hKK' hxK' h
  · exact hPF G t n f ψ G₀ hpres p hp hp2 hq1 hq2 x y hxp hyp hxy hxN hyN hxD hyD K K' hK hpK
      hK' hKK' hxK' h

theorem ggSixLayerCXNonsplitInput_of_split3 (hlift : GGNonsplitCompLiftInput)
    (hHS : GGNonsplitNbrHalfSplitInput) (hPF : GGNonsplitNbrPrimeFieldInput) :
    GGSixLayerCXNonsplitInput :=
  ggSixLayerCXNonsplitInput_of_kg hlift (ggNonsplitNbrMarkingInput_of_split hHS hPF)

end Inputs

end CFSG.StandardType

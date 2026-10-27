module

public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeCFMcL

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace NbrLangTypeA

variable {K : Type*} [Group K]

theorem ggMarkingAll_mono {Q Q' : LargeEvenMarkProp K}
    (hQQ' : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : K ⧸ Subgroup.center K ≃* R), Q lab R I F θ → Q' lab R I F θ)
    (h : GGMarkingAll Q) : GGMarkingAll Q' := fun P hP =>
  largeEvenMarking_mono (fun lab R _ I F θ hθ => ⟨hθ.1, hQQ' lab R I F θ hθ.2⟩) (h P hP)

theorem ggMarkingAll_of_and {Q₁ Q₂ Q : LargeEvenMarkProp K} (h₁ : GGMarkingAll Q₁)
    (h₂ : GGMarkingAll Q₂)
    (h : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : K ⧸ Subgroup.center K ≃* R), Q₁ lab R I F θ → Q₂ lab R I F θ → Q lab R I F θ) :
    GGMarkingAll Q := by
  intro P hP
  refine largeEvenMarking_mono ?_ (h₂ _ (h₁ P hP))
  rintro lab R _ I F θ ⟨⟨hPθ, hQ₁⟩, hQ₂⟩
  exact ⟨hPθ, h lab R I F θ hQ₁ hQ₂⟩

end NbrLangTypeA

open NbrLangTypeA

@[expose] def GGNbrLangTorusAxisOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
        GGMarkingAll (K := ↥K) fun lab _ _ I F θ => S p lab →
          (∀ (b : G) (hb : b ∈ Bs), ∃ u ∈ I, ∃ f ∈ Subgroup.closure F,
            ggLAut K θ ⟨b, hN hb⟩ = u * f) →
          ∀ (b₀ : G) (hb₀ : b₀ ∈ Bs), ggLAut K θ ⟨b₀, hN hb₀⟩ ∉ I →
            ∃ B₀ : Subgroup G, B₀ ≤ Bs ∧ Nat.card B₀ * p = Nat.card Bs ∧ b₀ ∉ B₀ ∧
              (∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I → b ∈ B₀) ∧
              ∃ T : Subgroup G, T ≤ Subgroup.centralizer (B₀ : Set G) ∧
                (∀ a ∈ T, ∀ c ∈ T, a * c = c * a) ∧
                b₀ ∈ Subgroup.normalizer (T : Set G) ∧
                (∀ t ∈ T, b₀ * t * b₀⁻¹ = t → ∃ s ∈ T,
                  t = ((List.range p).map fun i => b₀ ^ i * s * (b₀ ^ i)⁻¹).prod) ∧
                ∃ e ∈ B₀ ⊓ T, e ≠ 1

theorem GGNbrLangTorusAxisOn.mono {S S' : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S' p lab → S p lab) (h : GGNbrLangTorusAxisOn S) :
    GGNbrLangTorusAxisOn S' := by
  intro G _ _ p B Bs x L D J hC y K hK hN
  exact ggMarkingAll_mono (fun lab R _ I F θ hQ hS' => hQ (hS p lab hS'))
    (h G p B Bs x L D J hC y K hK hN)

theorem GGNbrLangTorusAxisOn.or {S S' : ℕ → LargeEvenLabel → Prop}
    (h : GGNbrLangTorusAxisOn S) (h' : GGNbrLangTorusAxisOn S') :
    GGNbrLangTorusAxisOn fun p lab => S p lab ∨ S' p lab := by
  intro G _ _ p B Bs x L D J hC y K hK hN
  refine ggMarkingAll_of_and (h G p B Bs x L D J hC y K hK hN)
    (h' G p B Bs x L D J hC y K hK hN) ?_
  rintro lab R _ I F θ hQ hQ' (hS | hS)
  · exact hQ hS
  · exact hQ' hS

theorem ggNbrLangTorusAxisOn_true_of {S : ℕ → LargeEvenLabel → Prop}
    (h : GGNbrLangTorusAxisOn S) (h' : GGNbrLangTorusAxisOn fun p lab => ¬ S p lab) :
    GGNbrLangTorusAxisOn fun _ _ => True :=
  (h.or h').mono fun p lab _ => em (S p lab)

theorem ggNbrLangTorusAxisInput_of_on (h : GGNbrLangTorusAxisOn fun _ _ => True) :
    GGNbrLangTorusAxisInput := by
  intro G _ _ p B Bs x L D J hC y K hK hN
  exact ggMarkingAll_mono (fun lab R _ I F θ hQ => hQ trivial) (h G p B Bs x L D J hC y K hK hN)

@[expose] def GGNbrInnerWeylOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      Bs ≤ Subgroup.normalizer (K : Set G) → ∀ hxK : x ∈ Subgroup.normalizer (K : Set G),
        GGMarkingAll (K := ↥K) fun lab _ _ I _ θ => S p lab →
          ggLAut K θ ⟨x, hxK⟩ ∈ I →
            ∃ w ∈ K, (∀ b ∈ Bs, w * b * w⁻¹ ∈ Subgroup.centralizer (Bs : Set G)) ∧
              w * x * w⁻¹ ∉ Subgroup.zpowers x

theorem GGNbrInnerWeylOn.mono {S S' : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S' p lab → S p lab) (h : GGNbrInnerWeylOn S) : GGNbrInnerWeylOn S' := by
  intro G _ _ p B Bs x L D J hC y K hK hN hxK
  exact ggMarkingAll_mono (fun lab R _ I F θ hQ hS' => hQ (hS p lab hS'))
    (h G p B Bs x L D J hC y K hK hN hxK)

theorem GGNbrInnerWeylOn.or {S S' : ℕ → LargeEvenLabel → Prop} (h : GGNbrInnerWeylOn S)
    (h' : GGNbrInnerWeylOn S') : GGNbrInnerWeylOn fun p lab => S p lab ∨ S' p lab := by
  intro G _ _ p B Bs x L D J hC y K hK hN hxK
  refine ggMarkingAll_of_and (h G p B Bs x L D J hC y K hK hN hxK)
    (h' G p B Bs x L D J hC y K hK hN hxK) ?_
  rintro lab R _ I F θ hQ hQ' (hS | hS)
  · exact hQ hS
  · exact hQ' hS

theorem ggNbrInnerWeylOn_true_of {S : ℕ → LargeEvenLabel → Prop} (h : GGNbrInnerWeylOn S)
    (h' : GGNbrInnerWeylOn fun p lab => ¬ S p lab) : GGNbrInnerWeylOn fun _ _ => True :=
  (h.or h').mono fun p lab _ => em (S p lab)

theorem ggNbrInnerWeylInput_of_on (h : GGNbrInnerWeylOn fun _ _ => True) :
    GGNbrInnerWeylInput := by
  intro G _ _ p B Bs x L D J hC y K hK hN hxK
  exact ggMarkingAll_mono (fun lab R _ I F θ hQ => hQ trivial)
    (h G p B Bs x L D J hC y K hK hN hxK)

end CFSG.StandardType

end

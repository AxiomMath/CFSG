module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangAxisOn

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGNbrLangAxisInnerOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
        GGMarkingAll (K := ↥K) fun lab _ _ I F θ => S p lab →
          (∀ hx : x ∈ Bs, ggLAut K θ ⟨x, hN hx⟩ ∈ I) →
          (∀ (b : G) (hb : b ∈ Bs), ∃ u ∈ I, ∃ f ∈ Subgroup.closure F,
            ggLAut K θ ⟨b, hN hb⟩ = u * f) →
          ∀ (b₀ : G) (hb₀ : b₀ ∈ Bs), ggLAut K θ ⟨b₀, hN hb₀⟩ ∉ I →
            ∃ B₀ : Subgroup G, B₀ ≤ Bs ∧ Nat.card B₀ * p = Nat.card Bs ∧ b₀ ∉ B₀ ∧
              (∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I → b ∈ B₀) ∧
              ∃ k ∈ Subgroup.centralizer (B₀ : Set G), ∃ e ∈ B₀, e ≠ 1 ∧
                k * b₀ * k⁻¹ = e * b₀

@[expose] def GGNbrLangAxisOuterOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
        GGMarkingAll (K := ↥K) fun lab _ _ I F θ => S p lab →
          (∀ hx : x ∈ Bs, ggLAut K θ ⟨x, hN hx⟩ ∉ I) →
          (∀ (b : G) (hb : b ∈ Bs), ∃ u ∈ I, ∃ f ∈ Subgroup.closure F,
            ggLAut K θ ⟨b, hN hb⟩ = u * f) →
          ∀ (b₀ : G) (hb₀ : b₀ ∈ Bs), ggLAut K θ ⟨b₀, hN hb₀⟩ ∉ I →
            ∃ B₀ : Subgroup G, B₀ ≤ Bs ∧ Nat.card B₀ * p = Nat.card Bs ∧ b₀ ∉ B₀ ∧
              (∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I → b ∈ B₀) ∧
              ∃ k ∈ Subgroup.centralizer (B₀ : Set G), ∃ e ∈ B₀, e ≠ 1 ∧
                k * b₀ * k⁻¹ = e * b₀

theorem GGNbrLangAxisInnerOn.mono {S S' : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S' p lab → S p lab) (h : GGNbrLangAxisInnerOn S) : GGNbrLangAxisInnerOn S' := by
  intro G _ _ p B Bs x L D J hC y K hK hN
  exact NbrLangTypeA.ggMarkingAll_mono (fun lab R _ I F θ hQ hS' => hQ (hS p lab hS'))
    (h G p B Bs x L D J hC y K hK hN)

theorem GGNbrLangAxisInnerOn.or {S S' : ℕ → LargeEvenLabel → Prop} (h : GGNbrLangAxisInnerOn S)
    (h' : GGNbrLangAxisInnerOn S') : GGNbrLangAxisInnerOn fun p lab => S p lab ∨ S' p lab := by
  intro G _ _ p B Bs x L D J hC y K hK hN
  refine NbrLangTypeA.ggMarkingAll_of_and (h G p B Bs x L D J hC y K hK hN)
    (h' G p B Bs x L D J hC y K hK hN) ?_
  rintro lab R _ I F θ hQ hQ' (hS | hS)
  · exact hQ hS
  · exact hQ' hS

theorem GGNbrLangAxisOuterOn.mono {S S' : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S' p lab → S p lab) (h : GGNbrLangAxisOuterOn S) : GGNbrLangAxisOuterOn S' := by
  intro G _ _ p B Bs x L D J hC y K hK hN
  exact NbrLangTypeA.ggMarkingAll_mono (fun lab R _ I F θ hQ hS' => hQ (hS p lab hS'))
    (h G p B Bs x L D J hC y K hK hN)

theorem GGNbrLangAxisOuterOn.or {S S' : ℕ → LargeEvenLabel → Prop} (h : GGNbrLangAxisOuterOn S)
    (h' : GGNbrLangAxisOuterOn S') : GGNbrLangAxisOuterOn fun p lab => S p lab ∨ S' p lab := by
  intro G _ _ p B Bs x L D J hC y K hK hN
  refine NbrLangTypeA.ggMarkingAll_of_and (h G p B Bs x L D J hC y K hK hN)
    (h' G p B Bs x L D J hC y K hK hN) ?_
  rintro lab R _ I F θ hQ hQ' (hS | hS)
  · exact hQ hS
  · exact hQ' hS

theorem ggNbrLangAxisOn_of_inner_outer {S : ℕ → LargeEvenLabel → Prop}
    (hI : GGNbrLangAxisInnerOn S) (hO : GGNbrLangAxisOuterOn S) : GGNbrLangAxisOn S := by
  intro G _ _ p B Bs x L D J hcfg y K hK hN
  refine NbrLangTypeA.ggMarkingAll_of_and (hI G p B Bs x L D J hcfg y K hK hN)
    (hO G p B Bs x L D J hcfg y K hK hN) ?_
  intro lab R _ I F θ hInner hOuter hS hall
  by_cases hxi : ∀ hx : x ∈ Bs, ggLAut K θ ⟨x, hN hx⟩ ∈ I
  · exact hInner hS hxi hall
  · refine hOuter hS ?_ hall
    intro hx hP
    exact hxi fun hx' => by
      have hEq : (⟨x, hN hx'⟩ : Subgroup.normalizer (K : Set G)) = ⟨x, hN hx⟩ :=
        Subtype.ext rfl
      rw [hEq]
      exact hP

end CFSG.StandardType

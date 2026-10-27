
module

public import CFSG.Quasithin.Background.C2Defs
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable (G : Type) [Group G] [Finite G]

@[expose] def A3Orbits : Prop :=
  ∀ (X T L : Subgroup G), IsSQTKIn X → IsSylowTwoOf T X → L ∈ cComp X →
    conjSubgroupsBy X L = conjSubgroupsBy T L ∧
    ((∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set G)) ∨
      ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) ∧
        conjSubgroupsBy T L = {L, conjByElt t L} ∧
        ⁅L, conjByElt t L⁆ ≤ pCoreOf 2 X ∧
        (L ⊔ pCoreOf 2 X) ⊓ (conjByElt t L ⊔ pCoreOf 2 X) = pCoreOf 2 X ∧
        T ≤ Subgroup.normalizer ((L ⊔ conjByElt t L : Subgroup G) : Set G))

@[expose] def ASC19Statement : Prop :=
  ∀ H B₁ B₂ : Subgroup G,
    ((∃ B : Subgroup G, IsBlock2 H B ∧ IsAltType B 3) → CharTwo (oTwoThreeIn H)) →
    IsBlock2 H B₁ → IsBlock2 H B₂ → B₁ ≠ B₂ → ⁅B₁, B₂⁆ = ⊥

@[expose] def ASC111Statement : Prop :=
  ∀ (H K S : Subgroup G) (ι : Type) (B : ι → Subgroup G), Finite ι →
    (∀ i, IsBlock2 H (B i)) → (∀ i j, i ≠ j → ⁅B i, B j⁆ = ⊥) → K = ⨆ i, B i → K ≤ H →
    IsSylowTwoOf S H → (∀ h ∈ H, ∃ k ∈ K, ∃ s ∈ S, h = k * s) →
    H ⊓ Subgroup.centralizer ((⁅pCoreOf 2 K, K⁆ : Subgroup G) : Set G) = pCoreOf 2 H

@[expose] def ASC129Statement : Prop :=
  ∀ (H T M : Subgroup G), IsSQTKIn H → CharTwo H → IsSylowTwoOf T H → cgsIn H T ≤ M → M ≤ H →
    ∃ (r : ℕ) (Lb : Fin r → Subgroup G), r ≤ 2 ∧
      (∀ i, IsChi0Block H (Lb i) ∧ IsBorelOfBlock (Lb i) (Lb i ⊓ M) ∧
        ⁅Lb i, thompsonJ T⁆ = Lb i) ∧
      ∀ h ∈ H, ∃ m ∈ M, ∃ x : Fin r → G, (∀ i, x i ∈ Lb i) ∧ h = m * (List.ofFn x).prod

end CFSG.Quasithin

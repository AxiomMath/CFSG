module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL4546Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGL45CentOutsideInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGL45Config p B Bs x L D J X B₂ d y K U U₁ → B < Bs →
      Bs ⊓ Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer (K : Set G) ≤ B

theorem GGL45Config.inf_centralizer_inf_le {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) {b : G}
    (hb : b ∈ Bs ⊓ Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer (K : Set G))
    (hbB : b ∈ B) : b ∈ Subgroup.zpowers d := by
  have hL44 := hcfg.2.2.2.2.2.1
  have hBK : B ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y :=
    inf_centralizer_eq_zpowers_of_sHat hL44.2.2.1.1
  have hby : b ∈ Subgroup.zpowers y := hBK ▸ ⟨hbB, hb.2⟩
  rwa [hL44.2.2.2.1] at hby

theorem ggL45CentInput_of_outside (h : GGL45CentOutsideInput) : GGL45CentInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hcfg b hb
  have hBBs : B ≤ Bs := hcfg.1.1.2.1.1
  have hbB : b ∈ B := by
    rcases hBBs.lt_or_eq with hlt | heq
    · exact h G p B Bs x L D J X B₂ d y K U U₁ hcfg hlt hb
    · exact heq ▸ hb.1.1
  exact hcfg.inf_centralizer_inf_le hb hbB

end CFSG.StandardType

end

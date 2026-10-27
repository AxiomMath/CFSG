module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProofE6Hyp
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProofE8

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank

local instance noOffRestFactThreeR : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

local instance noOffRestFactFiveR : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

section Frames

@[expose] def GGSixBstarE6ThreeFrameOn (P : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), P t n f p →
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ →
    GGBstarModelFrame (TableBExc.E6Three.adPerm .E6 3) p (ggM p B x L D J) Bs ∨
      GGBstarModelFrame NoOffRest.hypPerm p (ggM p B x L D J) Bs

theorem ggSixBstarNoOffenderOn_of_e6ThreeFrameOn {P : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (h : GGSixBstarE6ThreeFrameOn P) (hP3 : ∀ t n f p, P t n f p → p = 3) :
    GGSixBstarNoOffenderOn P := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain rfl := hP3 t n f p hP
  rcases h G 3 B Bs x L D J t n f ψ hP hctx hC with hF | hF
  · exact hF.noOffender (NoOffRest.adPerm_injective (by norm_num))
      NoOffRest.actNoOffender_adPerm_E6
  · exact hF.noOffender NoOffRest.hypPerm_injective NoOffRest.actNoOffender_hypPerm_E6

@[expose] def GGSixBstarE8FiveFrameOn (P : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), P t n f p →
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ →
    GGBstarModelFrame (NoOffRest.eigPerm 5 2) p (ggM p B x L D J) Bs ∨
      GGBstarModelFrame (NoOffRest.eigPerm 5 3) p (ggM p B x L D J) Bs

theorem ggSixBstarNoOffenderOn_of_e8FiveFrameOn {P : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (h : GGSixBstarE8FiveFrameOn P) (hP5 : ∀ t n f p, P t n f p → p = 5) :
    GGSixBstarNoOffenderOn P := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain rfl := hP5 t n f p hP
  rcases h G 5 B Bs x L D J t n f ψ hP hctx hC with hF | hF
  · exact hF.noOffender NoOffRest.eigPerm_two_injective NoOffRest.actNoOffender_eigPerm_two
  · exact hF.noOffender NoOffRest.eigPerm_three_injective NoOffRest.actNoOffender_eigPerm_three

end Frames

end CFSG.StandardType

module

public import CFSG.OddTranspositions.AscTheoremTwo
public import CFSG.OddTranspositions.FaithfulBlocks
public import CFSG.OddTranspositions.PartThree.EightEight.Core
public import CFSG.OddTranspositions.PartThree.Statements
public import CFSG.Timmesfeld.Bridge.Asc72Triangle

import CFSG.OddTranspositions.BlockGraph
import CFSG.OddTranspositions.PartThree.EightEight.ThirdKind
import CFSG.OddTranspositions.PartThree.EightEight.Seventeen
import CFSG.OddTranspositions.PartThree.EightSeven

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

@[expose] def IsStarTriangle (hC : HypothesisC D) (x w y : G) : Prop :=
  IsTriangle D x w y ∧ IsThirdKind x w y ∧ x ∈ DalphaStar D hC.alpha ∧
    w ∈ DalphaStar D hC.alpha ∧ y ∈ DalphaStar D hC.alpha ∧
    ∀ γ ∈ blockClass hC.alpha, w ∈ γ → x ∉ γ ∧ y ∉ γ

@[expose] def EightEightStar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D),
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) →
    ¬ (∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) →
    ¬ Group.IsSolvable (Halpha D hC.alpha) → FaithfulOnBlocks hC.alpha →
    ¬ O4PairData G D →
    derivedSeries (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 1 ≠
      derivedSeries (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 2 →
    ∀ x w y : G, ¬ IsStarTriangle hC x w y

theorem exists_isStarTriangle (h2 : AschbacherTheoremTwo) (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (h3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2) :
    ∃ x w y : G, IsStarTriangle hC x w y := by
  by_cases htwo : ∃ β ∈ Dalpha D hC.alpha, ∃ a ∈ β, ∃ x ∈ β, a ≠ x ∧ Commute a x
  · obtain ⟨β, hβ, a, ha, x, hx, hax, hcommax⟩ := htwo
    obtain ⟨γ, hγ, hγperp, htri3⟩ :=
      exists_isThirdKind_of_commute_of_mem h86 h87 hC hrad hO4 hF hne hβ ha hx hax hcommax
    obtain ⟨c, hc⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hγ.1
    obtain ⟨htri, hthird⟩ := htri3 c hc
    refine ⟨a, c, x, htri, hthird, ⟨β, hβ, ha⟩, ⟨γ, hγ, hc⟩, ⟨β, hβ, hx⟩, ?_⟩
    intro ω hω hcω
    have hωγ : ω = γ :=
      eq_of_mem_of_mem_blockClass hC.isBlock_alpha hω hγ.1 ⟨c, hcω, hc⟩
    constructor
    · intro haω
      have hγβ : γ = β :=
        eq_of_mem_of_mem_blockClass hC.isBlock_alpha hγ.1 hβ.1 ⟨a, hωγ ▸ haω, ha⟩
      exact hγperp (by rw [hγβ]; exact mem_perp_iff.mpr (Or.inr rfl))
    · intro hxω
      have hγβ : γ = β :=
        eq_of_mem_of_mem_blockClass hC.isBlock_alpha hγ.1 hβ.1 ⟨x, hωγ ▸ hxω, hx⟩
      exact hγperp (by rw [hγβ]; exact mem_perp_iff.mpr (Or.inr rfl))
  · have hnoComm : ∀ β ∈ Dalpha D hC.alpha, ∀ a ∈ β, ∀ b ∈ β, a ≠ b → ¬ Commute a b := by
      intro β hβ a ha b hb hab hcommab
      exact htwo ⟨β, hβ, a, ha, b, hb, hab, hcommab⟩
    obtain ⟨x, w, y, htri, hthird, hxS, hwS, hyS, _⟩ :=
      exists_isThirdKind_of_reach h2 h86 hC hrad h3 hO4 hne
    obtain ⟨β, hβ, hxβ⟩ := hxS
    obtain ⟨δ, hδ, hyδ⟩ := hyS
    obtain ⟨ε, hε, hwε⟩ := hwS
    have hβδ : β ≠ δ := by
      intro h
      exact (hnoComm β hβ x hxβ y (h ▸ hyδ) htri.2.2.2.1) htri.2.2.2.2.1
    have hδβ : δ ∈ Dalpha D β :=
      mem_Dalpha_of_commute_mem hC.setup.normal hC.setup.oddT hC.isBlock_alpha
        hβ.1 hδ.1 hβδ hxβ hyδ htri.2.2.2.2.1
    have hεβ : ε ≠ β := by
      intro h
      exact htri.2.2.2.2.2.2 ((mem_Dalpha_iff.mp hδβ).2.2.2 w (h ▸ hwε) y hyδ).symm
    have hεδ : ε ≠ δ := by
      intro h
      exact htri.2.2.2.2.2.1 ((mem_Dalpha_iff.mp hδβ).2.2.2 x hxβ w (h ▸ hwε))
    refine ⟨x, w, y, htri, hthird, ⟨β, hβ, hxβ⟩, ⟨ε, hε, hwε⟩,
      ⟨δ, hδ, hyδ⟩, ?_⟩
    intro ω hω hwω
    have hωε : ω = ε :=
      eq_of_mem_of_mem_blockClass hC.isBlock_alpha hω hε.1 ⟨w, hwω, hwε⟩
    constructor
    · intro hxω
      have hωβ : ω = β :=
        eq_of_mem_of_mem_blockClass hC.isBlock_alpha hω hβ.1 ⟨x, hxω, hxβ⟩
      exact hεβ (hωε.symm.trans hωβ)
    · intro hyω
      have hωδ : ω = δ :=
        eq_of_mem_of_mem_blockClass hC.isBlock_alpha hω hδ.1 ⟨y, hyω, hyδ⟩
      exact hεδ (hωε.symm.trans hωδ)

theorem eightEightCore_of_star (h2 : AschbacherTheoremTwo) (h86 : Lemma8_6) (h87 : Theorem8_7)
    (h : EightEightStar) : EightEightCore := by
  intro G _ _ D hC hrad h3 hns hF hO4
  by_contra hneQ
  have hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2 := by
    intro heq
    apply hneQ
    rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective _) 1,
      ← map_derivedSeries_eq (QuotientGroup.mk'_surjective _) 2, heq]
  obtain ⟨x, w, y, hxwy⟩ := exists_isStarTriangle h2 h86 h87 hC hrad h3 hO4 hF hne
  exact h G D hC hrad h3 hns hF hO4 hneQ x w y hxwy

end CFSG.OddTranspositions.PartThree.EightEight

end

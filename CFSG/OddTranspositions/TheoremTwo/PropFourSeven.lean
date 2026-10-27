module

public import CFSG.OddTranspositions.TheoremTwo.PropFourSeven.AtAlpha
public import CFSG.OddTranspositions.TheoremTwo.PropFourSeven.CaseA
public import CFSG.OddTranspositions.TheoremTwo.PropFourSeven.CaseBStep
public import CFSG.OddTranspositions.TheoremTwo.PropFourSeven.CaseBGlobal

public section

namespace CFSG.OddTranspositions.QZ.Config

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.GroupTheory CFSG.OddTranspositions.PropFourSeven

variable {G : Type} [Group G] [Finite G] {D : Set G} {u w v z a : G} {K₁ S' : Subgroup G}

theorem fibre_singleton (hC : HypothesisC D)
    (hQ : Config D u w v z a K₁ S') :
    ∀ (ε : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
        Equiv.Perm (Fin 5)),
      ε '' imageClass hC = transpositions →
      ∀ (d : G) (hd : d ∈ DalphaStar D hC.alpha)
        (d' : G) (hd' : d' ∈ DalphaStar D hC.alpha),
        ε (starImage hC d hd) = ε (starImage hC d' hd') → d = d' := by
  intro ε hε d hd d' hd' h
  have hL := s5Labelling_alpha hC hQ ε hε
  have hlab : labelOf ε d' = labelOf ε d := by
    rw [labelOf_eq_starImage hC ε hd, labelOf_eq_starImage hC ε hd', h]
  by_cases hA : ∀ θ ∈ Dalpha D hC.alpha, ∀ x ∈ θ, ∀ y ∈ DalphaStar D hC.alpha,
      labelOf ε y = labelOf ε x → y ∈ θ
  · obtain ⟨θ, hθ, hdθ⟩ := hd
    exact caseA_singleton hC hQ ε hε hL.block hA θ hθ d hdθ d' (hA θ hθ d hdθ d' hd' hlab)
  · push Not at hA
    obtain ⟨θ₀, hθ₀, x₀, hx₀, y₀, hy₀, hlab₀, hny⟩ := hA
    have hspread := exists_other_block hC hQ ε hε hθ₀ hx₀ hy₀ hlab₀ hny
    exact (false_of_Phi_subset hC hL hspread
      (fun _ hu _ hδ _ hε' hδε => Phi_subset_of_adjacent hC hL hspread hu hδ hε' hδε)).elim

end CFSG.OddTranspositions.QZ.Config


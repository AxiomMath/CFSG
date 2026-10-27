module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitness
public import CFSG.LocalAnalysis.StandardType.GGSixBstarRestSp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Inputs

@[expose] def GGSixRootFusionWitnessOn (P : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), P t n f p →
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r →
        Subgroup.centralizer {r} ≤ ggM p B x L D J →
        Odd ((ggG0 p B x L D J).relIndex (ggM p B x L D J)) →
          ∀ s ∈ ggG0 p B x L D J, orderOf s = 2 →
            GGRootFusionWitnessAlt p Bs D E (ggG0 p B x L D J) (ggM p B x L D J) t f r s

theorem ggSixRootFusionWitnessOn_of_split {P Q : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (h₁ : GGSixRootFusionWitnessOn fun t n f p => P t n f p ∧ Q t n f p)
    (h₂ : GGSixRootFusionWitnessOn fun t n f p => P t n f p ∧ ¬ Q t n f p) :
    GGSixRootFusionWitnessOn P := by
  intro G _ _ p B Bs x L D J t n f ψ hP
  by_cases hQ : Q t n f p
  · exact h₁ G p B Bs x L D J t n f ψ ⟨hP, hQ⟩
  · exact h₂ G p B Bs x L D J t n f ψ ⟨hP, hQ⟩

theorem GGSixRootFusionWitnessOn.mono {P Q : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (h : GGSixRootFusionWitnessOn P) (hQP : ∀ t n f p, Q t n f p → P t n f p) :
    GGSixRootFusionWitnessOn Q :=
  fun G _ _ p B Bs x L D J t n f ψ hQ => h G p B Bs x L D J t n f ψ (hQP t n f p hQ)

theorem ggSixRootFusionWitnessInputFor_of_on {P : StatedLieTag → Prop}
    (h : GGSixRootFusionWitnessOn fun t _ _ _ => P t) : GGSixRootFusionWitnessInputFor P :=
  fun G _ _ p B Bs x L D J t n f ψ hP => h G p B Bs x L D J t n f ψ hP

theorem GGSixRootFusionWitnessInputFor.on {P : StatedLieTag → Prop}
    (h : GGSixRootFusionWitnessInputFor P) : GGSixRootFusionWitnessOn fun t _ _ _ => P t :=
  fun G _ _ p B Bs x L D J t n f ψ hP => h G p B Bs x L D J t n f ψ hP

theorem ggSixRootFusionWitnessOn_of_not_admissible {P : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (hP : ∀ t n f p, P t n f p → ¬ StatedLieAdmissible t n 2 f) :
    GGSixRootFusionWitnessOn P := by
  intro G _ _ p B Bs x L D J t n f ψ hPt hctx
  exact absurd hctx.2.2.2.1.1 (hP t n f p hPt)

theorem ggSixRootFusionWitnessOn_POmegaOdd :
    GGSixRootFusionWitnessOn fun t _ _ _ => t = .POmegaOdd :=
  ggSixRootFusionWitnessOn_of_not_admissible fun t _ _ _ ht h => by
    subst ht
    exact h.2.2.2 rfl

theorem ggSixRootFusionWitnessOn_PSp_of_split (hs : GGSixRootFusionWitnessOn GGPSpSplit)
    (hn : GGSixRootFusionWitnessOn GGPSpNonsplit) :
    GGSixRootFusionWitnessOn fun t _ _ _ => t = .PSp :=
  ggSixRootFusionWitnessOn_of_split (Q := fun _ _ f p => p ∣ 2 ^ f - 1) hs hn

theorem ggSixRootFusionWitnessInputFor_otherClassical_of_on
    (hSp : GGSixRootFusionWitnessOn fun t _ _ _ => t = .PSp)
    (hPlus : GGSixRootFusionWitnessOn fun t _ _ _ => t = .POmegaPlus)
    (hMinus : GGSixRootFusionWitnessOn fun t _ _ _ => t = .POmegaMinus) :
    GGSixRootFusionWitnessInputFor GGOtherClassicalTag := by
  refine ggSixRootFusionWitnessInputFor_of_on ?_
  intro G _ _ p B Bs x L D J t n f ψ ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact hSp G p B Bs x L D J .PSp n f ψ rfl
  · exact ggSixRootFusionWitnessOn_POmegaOdd G p B Bs x L D J .POmegaOdd n f ψ rfl
  · exact hPlus G p B Bs x L D J .POmegaPlus n f ψ rfl
  · exact hMinus G p B Bs x L D J .POmegaMinus n f ψ rfl

end Inputs

end CFSG.StandardType

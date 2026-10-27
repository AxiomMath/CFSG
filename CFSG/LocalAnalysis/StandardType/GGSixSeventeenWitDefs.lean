module

public import CFSG.LocalAnalysis.StandardType.GGSixStepThreeCFSeventeenCases

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Inputs

@[expose] def GGSixSeventeenWitnessOn (P : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), P t n f p →
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G) (L₁ : Subgroup G), GGSixSeventeenPair p B Bs x L D J t f b L₁ →
        (∃ L₂ : Subgroup G, IsComponentOf L₂ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) ∧
          Nat.card (Bs ⊓ Subgroup.centralizer (L₂ : Set G) : Subgroup G) ≤ p ^ 2) ∨
        ∃ e ∈ L₁, GGSixSeventeenDirect p Bs D (ggG0 p B x L D J) e ∨
          (e ∈ Bs ∧ e ≠ 1 ∧ GGSixSeventeenSixteen p B Bs x L D J t f e)

theorem ggSixSeventeenWitnessOn_of_split {P Q : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (h₁ : GGSixSeventeenWitnessOn fun t n f p => P t n f p ∧ Q t n f p)
    (h₂ : GGSixSeventeenWitnessOn fun t n f p => P t n f p ∧ ¬ Q t n f p) :
    GGSixSeventeenWitnessOn P := by
  intro G _ _ p B Bs x L D J t n f ψ hP
  by_cases hQ : Q t n f p
  · exact h₁ G p B Bs x L D J t n f ψ ⟨hP, hQ⟩
  · exact h₂ G p B Bs x L D J t n f ψ ⟨hP, hQ⟩

theorem GGSixSeventeenWitnessOn.mono {P Q : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (h : GGSixSeventeenWitnessOn P) (hQP : ∀ t n f p, Q t n f p → P t n f p) :
    GGSixSeventeenWitnessOn Q :=
  fun G _ _ p B Bs x L D J t n f ψ hQ => h G p B Bs x L D J t n f ψ (hQP t n f p hQ)

theorem ggSixSeventeenWitnessInputFor_of_on {P : StatedLieTag → Prop}
    (h : GGSixSeventeenWitnessOn fun t _ _ _ => P t) : GGSixSeventeenWitnessInputFor P :=
  fun G _ _ p B Bs x L D J t n f ψ hP => h G p B Bs x L D J t n f ψ hP

theorem GGSixSeventeenWitnessInputFor.on {P : StatedLieTag → Prop}
    (h : GGSixSeventeenWitnessInputFor P) : GGSixSeventeenWitnessOn fun t _ _ _ => P t :=
  fun G _ _ p B Bs x L D J t n f ψ hP => h G p B Bs x L D J t n f ψ hP

theorem ggSixSeventeenWitnessOn_of_root {P : StatedLieTag → Prop}
    (h : GGSixSeventeenRootWitnessInputFor P) :
    GGSixSeventeenWitnessOn fun t _ f p => P t ∧ ¬ (t = .E8 ∧ f = 1 ∧ p = 7) := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx s1 b L₁ hpair
  obtain ⟨e, heL, heB, he1, h15 | h16⟩ := h G p B Bs x L D J t n f ψ hP.1 hP.2 hctx s1 b L₁ hpair
  · exact Or.inr ⟨e, heL, Or.inl ⟨heB, he1, Or.inr h15⟩⟩
  · exact Or.inr ⟨e, heL, Or.inr ⟨heB, he1, h16⟩⟩

theorem ggSixSeventeenWitnessOn_of_linear (h : GGSixSeventeenLinearWitnessInput) :
    GGSixSeventeenWitnessOn fun t _ _ _ => GGLinearUnitaryTag t :=
  (ggSixSeventeenWitnessInputFor_linearUnitary h).on

theorem ggSixSeventeenWitnessOn_of_not_admissible {P : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (hP : ∀ t n f p, P t n f p → ¬ StatedLieAdmissible t n 2 f) : GGSixSeventeenWitnessOn P := by
  intro G _ _ p B Bs x L D J t n f ψ hPt hctx
  exact absurd hctx.2.2.2.1.1 (hP t n f p hPt)

theorem ggSixSeventeenWitnessOn_POmegaOdd :
    GGSixSeventeenWitnessOn fun t _ _ _ => t = .POmegaOdd :=
  ggSixSeventeenWitnessOn_of_not_admissible fun t _ _ _ ht h => by
    subst ht
    exact h.2.2.2 rfl

theorem ggSixSeventeenWitnessInputFor_linearUnitary_of_on
    (hSLs : GGSixSeventeenWitnessOn fun t _ f p => t = .PSL ∧ p ∣ 2 ^ f - 1)
    (hSLn : GGSixSeventeenWitnessOn fun t _ f p => t = .PSL ∧ ¬ p ∣ 2 ^ f - 1)
    (hSUs : GGSixSeventeenWitnessOn fun t _ f p => t = .PSU ∧ p ∣ 2 ^ f + 1)
    (hSUn : GGSixSeventeenWitnessOn fun t _ f p => t = .PSU ∧ ¬ p ∣ 2 ^ f + 1) :
    GGSixSeventeenWitnessInputFor GGLinearUnitaryTag := by
  refine ggSixSeventeenWitnessInputFor_of_on ?_
  intro G _ _ p B Bs x L D J t n f ψ ht
  rcases ht with rfl | rfl
  · by_cases hp : p ∣ 2 ^ f - 1
    · exact hSLs G p B Bs x L D J .PSL n f ψ ⟨rfl, hp⟩
    · exact hSLn G p B Bs x L D J .PSL n f ψ ⟨rfl, hp⟩
  · by_cases hp : p ∣ 2 ^ f + 1
    · exact hSUs G p B Bs x L D J .PSU n f ψ ⟨rfl, hp⟩
    · exact hSUn G p B Bs x L D J .PSU n f ψ ⟨rfl, hp⟩

theorem ggSixSeventeenWitnessInputFor_otherClassical_of_on
    (hSp : GGSixSeventeenWitnessOn fun t _ _ _ => t = .PSp)
    (hPlus : GGSixSeventeenWitnessOn fun t _ _ _ => t = .POmegaPlus)
    (hMinus : GGSixSeventeenWitnessOn fun t _ _ _ => t = .POmegaMinus) :
    GGSixSeventeenWitnessInputFor GGOtherClassicalTag := by
  refine ggSixSeventeenWitnessInputFor_of_on ?_
  intro G _ _ p B Bs x L D J t n f ψ ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact hSp G p B Bs x L D J .PSp n f ψ rfl
  · exact ggSixSeventeenWitnessOn_POmegaOdd G p B Bs x L D J .POmegaOdd n f ψ rfl
  · exact hPlus G p B Bs x L D J .POmegaPlus n f ψ rfl
  · exact hMinus G p B Bs x L D J .POmegaMinus n f ψ rfl

end Inputs

end CFSG.StandardType

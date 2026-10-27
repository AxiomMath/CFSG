module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitNsRest
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivSUTag
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivFactors
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivOmega

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Inputs

@[expose] def GGSixSeventeenWitnessDvdOn (P : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), P t n f p →
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G) (L₁ : Subgroup G), GGSixSeventeenPair p B Bs x L D J t f b L₁ →
        p ∣ Nat.card L₁ →
        (∃ L₂ : Subgroup G, IsComponentOf L₂ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) ∧
          Nat.card (Bs ⊓ Subgroup.centralizer (L₂ : Set G) : Subgroup G) ≤ p ^ 2) ∨
        ∃ e ∈ L₁, GGSixSeventeenDirect p Bs D (ggG0 p B x L D J) e ∨
          (e ∈ Bs ∧ e ≠ 1 ∧ GGSixSeventeenSixteen p B Bs x L D J t f e)

theorem GGSixSeventeenWitnessOn.dvdOn {P : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (h : GGSixSeventeenWitnessOn P) : GGSixSeventeenWitnessDvdOn P :=
  fun G _ _ p B Bs x L D J t n f ψ hP hctx s1 b L₁ hpair _ =>
    h G p B Bs x L D J t n f ψ hP hctx s1 b L₁ hpair

theorem ggSixSeventeenWitnessOn_of_dvdOn {P : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (hT : ∀ t n f p, P t n f p → GGNonsplitTag t ∧ GGLayerPDivTag t)
    (h : GGSixSeventeenWitnessDvdOn P) : GGSixSeventeenWitnessOn P := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx s1 b L₁ hpair
  obtain ⟨hT1, hT2⟩ := hT t n f p hP
  exact h G p B Bs x L D J t n f ψ hP hctx s1 b L₁ hpair
    (WitNs.dvd_card_of_isComponentOf_of_tag hT1 hT2 hctx hpair.1 hpair.2.2.1)

@[expose] def GGSixSeventeenWitnessRest8 : Prop :=
  GGSixSeventeenWitnessDvdOn GGPSUNonsplit ∧ GGSixSeventeenWitnessDvdOn GGPSpNonsplit ∧
    GGSixSeventeenWitnessDvdOn (fun t _ _ _ => t = .POmegaPlus) ∧
    GGSixSeventeenWitnessDvdOn (fun t _ _ _ => t = .POmegaMinus) ∧
    GGSixSeventeenE8SevenInput ∧ GGSixSeventeenRootWitnessInputFor GGExceptionalTag

theorem ggSixSeventeenWitnessRest8_of_rest7 (h : GGSixSeventeenWitnessRest7) :
    GGSixSeventeenWitnessRest8 :=
  ⟨h.1.dvdOn, h.2.1.dvdOn, h.2.2.1.dvdOn, h.2.2.2.1.dvdOn, h.2.2.2.2⟩

theorem ggSixSeventeenWitnessRest7_of_rest8 (hU : GGNonsplitTag .PSU)
    (hSp : GGNonsplitTag .PSp) (hPl : GGNonsplitTag .POmegaPlus)
    (hMi : GGNonsplitTag .POmegaMinus) (h : GGSixSeventeenWitnessRest8) :
    GGSixSeventeenWitnessRest7 := by
  obtain ⟨hSU, hSpn, hPlus, hMinus, hE8, hex⟩ := h
  refine ⟨ggSixSeventeenWitnessOn_of_dvdOn ?_ hSU, ggSixSeventeenWitnessOn_of_dvdOn ?_ hSpn,
    ggSixSeventeenWitnessOn_of_dvdOn ?_ hPlus, ggSixSeventeenWitnessOn_of_dvdOn ?_ hMinus, hE8,
    hex⟩
  · rintro t n f p ⟨rfl, -⟩
    exact ⟨hU, ggLayerPDivTag_PSU⟩
  · rintro t n f p ⟨rfl, -⟩
    exact ⟨hSp, ggLayerPDivTag_PSp⟩
  · rintro t n f p rfl
    exact ⟨hPl, ggLayerPDivTag_POmegaPlus⟩
  · rintro t n f p rfl
    exact ⟨hMi, ggLayerPDivTag_POmegaMinus⟩

end Inputs

section Wiring

theorem ggSixSeventeenWitnessInput_of_rest8 (hU : GGNonsplitTag .PSU)
    (hSp : GGNonsplitTag .PSp) (hPl : GGNonsplitTag .POmegaPlus)
    (hMi : GGNonsplitTag .POmegaMinus) (h : GGSixSeventeenWitnessRest8) :
    GGSixSeventeenWitnessInputFor fun _ => True :=
  ggSixSeventeenWitnessInput_of_rest7 (ggSixSeventeenWitnessRest7_of_rest8 hU hSp hPl hMi h)

end Wiring

end CFSG.StandardType

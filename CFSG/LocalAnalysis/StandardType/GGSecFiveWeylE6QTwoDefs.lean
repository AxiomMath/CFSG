module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveDataResDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

section Cfg

variable {G : Type} [Group G] [Finite G]

@[expose] def GGSecFiveE6QTwoCfg (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) :
    Prop :=
  ∃ 𝒦 : Finset (Subgroup G), GGSecFiveRouteCfg p B Bs x L D J 𝒦 ∧ ¬ GGSplitLie p L ∧
    ∃ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
      GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e ∧
      (∃ e' : Fin 6 ≃ ι, M = CoxeterMatrix.E₆.reindex e') ∧
      ∃ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e ∧ Nat.card (ggRankOneIn L Bs r) = 6

end Cfg

@[expose] def GGSecFiveWeylE6QTwoInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → GGSecFiveWeylCase' p B Bs x D J →
      (GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.E₆ ∨
        GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.E₇ ∨
        GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.E₈) →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ¬ (GGInnerDiagOnLabel GGLabQTwo p Bs L ∧
          (GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.E₇ ∨
            GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.E₈)) →
      GGSecFiveE6QTwoCfg p B Bs x L D J →
      GGSecFiveData p B x L D J

@[expose] def GGSecFiveDataResE6QTwoInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → GGIsWeylMatrixE M →
        GGSecFiveE6QTwoCfg p B Bs x L D J → GGSecFiveData p B x L D J

@[expose] def GGSecFiveDataResEOffE6QTwoInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → GGIsWeylMatrixE M →
        ¬ GGSecFiveE6QTwoCfg p B Bs x L D J → GGSecFiveData p B x L D J

theorem ggSecFiveDataResAt_E_of_e6QTwo
    (hE6 : GGSecFiveDataResE6QTwoInput) (hN : GGSecFiveDataResEOffE6QTwoInput) :
    GGSecFiveDataResAt (fun M => GGIsWeylMatrixE M) := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 ι M e hP hM
  by_cases hC : GGSecFiveE6QTwoCfg p B Bs x L D J
  · exact hE6 G p B Bs x L D J 𝒦 hR hT1 ι M e hP hM hC
  · exact hN G p B Bs x L D J 𝒦 hR hT1 ι M e hP hM hC

end CFSG.StandardType

end

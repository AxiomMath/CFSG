module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanADefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSExcl

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGSecFiveNSEnnolaSmallInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e →
        (∃ (n : ℕ) (e' : Fin n ≃ ι), (n = 3 ∨ n = 4) ∧ M = (CoxeterMatrix.A n).reindex e') →
        ¬ GGInnerDiagOnLabel (fun p lab => ggRowP_Ennola p lab ∧ ¬ ggRowP_ESU p lab) p Bs L

@[expose] def GGSecFiveNSU6SmallInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e →
        (∃ (n : ℕ) (e' : Fin n ≃ ι), (n = 3 ∨ n = 4) ∧ M = (CoxeterMatrix.A n).reindex e') →
        ¬ GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs L

@[expose] def GGSecFivePhanSmallFalseInput :
  Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J → ¬ GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e →
        (∃ (n : ℕ) (e' : Fin n ≃ ι), (n = 3 ∨ n = 4) ∧ M = (CoxeterMatrix.A n).reindex e') → False

theorem ggSecFiveDataResPhanASmallInput_of_false
    (h : GGSecFivePhanSmallFalseInput) : GGSecFiveDataResPhanASmallInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hregion hns ι M e hpres hA
  exact (h G p B Bs x L D J 𝒦 hcfg hregion hns ι M e hpres hA).elim

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveDataResDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGSecFiveF4SmallLabelInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (ks : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J ks →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs ks)),
        GGCoxeterPres p (ggAutomizerJoin L Bs ks) M e → GGIsWeylMatrixF4 M →
        GGWeylOfType p (CoxeterMatrix.A 3) (ggAutomizer L Bs) →
        (∀ K ∈ ks, ggAutomizer L Bs ⊔ ggAutomizer K Bs ≠ ggAutomizerJoin L Bs ks) →
        p = 3 ∧ GGHasLabel ⟨.A, 3, 2⟩ (L ⧸ Subgroup.center L) ∧
          ∀ K ∈ ks, GGHasLabel ⟨.A, 5, 1⟩ (K ⧸ Subgroup.center K)

@[expose] def GGSecFiveF4SmallDataInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (ks : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J ks →
      ¬ GGSecFiveTier1Region p B Bs x L D J →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs ks)),
        GGCoxeterPres p (ggAutomizerJoin L Bs ks) M e → GGIsWeylMatrixF4 M →
        GGWeylOfType p (CoxeterMatrix.A 3) (ggAutomizer L Bs) →
        (∀ K ∈ ks, ggAutomizer L Bs ⊔ ggAutomizer K Bs ≠ ggAutomizerJoin L Bs ks) →
        p = 3 → GGHasLabel ⟨.A, 3, 2⟩ (L ⧸ Subgroup.center L) →
        (∀ K ∈ ks, GGHasLabel ⟨.A, 5, 1⟩ (K ⧸ Subgroup.center K)) →
        GGSecFiveData p B x L D J

end CFSG.StandardType

end

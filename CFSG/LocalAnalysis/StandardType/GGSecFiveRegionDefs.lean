module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatLeviDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatRestDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePrimDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylRest5

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT

section Inputs

@[expose] def GGSecFiveTier1Region {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G)
    (x : G) (L D J : Subgroup G) : Prop :=
  ∃ 𝒦 : Finset (Subgroup G), GGSecFiveRouteCfg p B Bs x L D J 𝒦 ∧ GGSplitLie p L ∧
    ∃ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
      GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e ∧ (GGIsWeylMatrixAD M ∨ GGIsWeylMatrixE M)

@[expose] def GGSecFiveWeylAResInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → GGSecFiveWeylCase' p B Bs x D J →
      (∃ n, 1 ≤ n ∧ GGSecFiveWeylAt p B Bs x L D J (CoxeterMatrix.A n)) →
      (¬ ∃ (n f : ℕ) (y : G) (K : Subgroup G), GGTypeANbr p B Bs x L D J n f y K) →
      ¬ GGSecFiveTier1Region p B Bs x L D J → GGSecFiveData p B x L D J

@[expose] def GGSecFiveWeylBRestResInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → GGSecFiveWeylCase' p B Bs x D J →
      (∃ n, 2 ≤ n ∧ GGSecFiveWeylAt p B Bs x L D J (CoxeterMatrix.B n)) →
      (¬ ∃ (n : ℕ) (y : G) (K : Subgroup G), GGTypeAHalfNbr p B Bs x L D J n y K) →
      (¬ ∃ (n f : ℕ) (y : G) (K : Subgroup G), GGTypeCNbr p B Bs x L D J n f y K) →
      ¬ GGSecFiveTier1Region p B Bs x L D J → GGSecFiveData p B x L D J

@[expose] def GGSecFiveWeylDResInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → GGSecFiveWeylCase' p B Bs x D J →
      (∃ n, 4 ≤ n ∧ GGSecFiveWeylAt p B Bs x L D J (ggCoxeterMatrixD n)) →
      ¬ GGSecFiveTier1Region p B Bs x L D J → GGSecFiveData p B x L D J

@[expose] def GGSecFiveWeylEResInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → GGSecFiveWeylCase' p B Bs x D J →
      (GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.E₆ ∨
        GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.E₇ ∨
        GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.E₈) →
      ¬ GGSecFiveTier1Region p B Bs x L D J → GGSecFiveData p B x L D J

@[expose] def GGSecFiveWeylF4ResInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → GGSecFiveWeylCase' p B Bs x D J →
      GGSecFiveWeylAt p B Bs x L D J CoxeterMatrix.F₄ →
      ¬ GGSecFiveTier1Region p B Bs x L D J → GGSecFiveData p B x L D J

@[expose] def GGSecFiveWeylRest5Res : Prop :=
  GGSecFiveWeylAResInput ∧ GGSecFiveWeylBRestResInput ∧ GGSecFiveWeylDResInput ∧
    GGSecFiveWeylEResInput ∧ GGSecFiveWeylF4ResInput

@[expose] def GGSecFiveCompatRestWResInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → GGSecFiveWeylCase' p B Bs x D J →
      (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → GGReflGenerated p (ggAutomizer K Bs) →
        GGScalarsOrWeyl' p B Bs x D J →
          GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) →
      ∀ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
        GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ →
          ¬ GGSecFiveLeviCase p B Bs x L D J → ¬ GGSecFiveTier1Region p B Bs x L D J →
            GGSecFiveCompat p B x L D J

end Inputs

end CFSG.StandardType

end

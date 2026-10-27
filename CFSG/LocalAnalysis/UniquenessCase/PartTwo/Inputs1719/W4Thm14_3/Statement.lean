module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenDefs
public import CFSG.Quasithin.Background.B4Models
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

@[expose] def K14_3FixT : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L T : Subgroup (MulAut W)) (n : ℕ),
      O2Trivial Y → IsBasicModule Y → L ≤ Y → (L.subgroupOf Y).Normal →
      (IsL2 ↥L n ∨ IsSz ↥L n) → 3 ≤ n → IsSylowIn 2 T Y →
        fixV T ≠ fixV (L ⊔ T)

@[expose] def K14_3Ext : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (L : Subgroup (MulAut W)) (n : ℕ), IsL2 ↥L n → 3 ≤ n →
      ∀ I ∈ irrSet L, I ⊓ fixV L ≠ ⊥ → BinaryNaturalSL L I (I ⊓ fixV L) 2 n

@[expose] def K14_3Exc : Prop :=
  ∀ (I : Type) [CommGroup I] [Finite I], (∀ w : I, w ^ 2 = 1) →
    ∀ (X L : Subgroup (MulAut I)) (n : ℕ),
      L ≤ X → (L.subgroupOf X).Normal → IsIrrOn L ⊤ ⊥ →
      (IsL2 ↥L n ∨ IsSz ↥L n) → 3 ≤ n → n ≠ 4 → E3.mParam X = n + 2 →
        n = 6 ∧ IsL2 ↥L 6 ∧ E3.aParam X ≤ 2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

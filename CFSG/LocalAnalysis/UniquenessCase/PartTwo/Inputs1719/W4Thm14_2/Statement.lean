module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.WeakClosure81.SevenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

@[expose] def W4Thm14_2Used : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y L : Subgroup (MulAut W),
      IsKGroup ↥Y → O2Trivial Y → IsBasicModule Y →
      L ≤ Y → (L.subgroupOf Y).Normal →
      (CFSG.LocalAnalysis.UniquenessCase.UC22.IsSL3 ↥L 2 ∨
        CFSG.LocalAnalysis.UniquenessCase.UC22.IsSL3 ↥L 4) →
      (∃ T : Subgroup (MulAut W), T ≤ Y ∧ IsSylowIn 2 T Y ∧ S17.SwapsParabolics T L) →
      E3.mParam Y = 4 →
      ∀ p : ℕ, p.Prime → 3 < p → CFSG.Open.pRank p (⊤ : Subgroup ↥Y) ≤ 1

@[expose] def K14_2Small : Prop :=
  ∀ (I : Type) [CommGroup I] [Finite I], (∀ w : I, w ^ 2 = 1) →
    ∀ X L : Subgroup (MulAut I), L ≤ X → (L.subgroupOf X).Normal → IsIrrOn L ⊤ ⊥ →
      (CFSG.LocalAnalysis.UniquenessCase.UC22.IsSL3 ↥L 2 ∨
        CFSG.LocalAnalysis.UniquenessCase.UC22.IsSL3 ↥L 4) →
      E3.mParam X ≤ 4 →
        (∀ (S : Subgroup (MulAut I)) (x : MulAut I), IsSylowIn 2 S L →
          x ∈ Subgroup.normalizer (L : Set (MulAut I)) →
          x ∈ Subgroup.normalizer (S : Set (MulAut I)) →
          ∀ P : Subgroup (MulAut I), S17.IsMaxParabolicOver L S P →
            P.map (MulAut.conj x).toMonoidHom = P) ∧
        (E3.mParam X ≤ 2 →
          CFSG.LocalAnalysis.UniquenessCase.UC22.IsSL3 ↥L 2 ∧ Subgroup.center ↥L ≠ ⊥ ∧
            rk ↥(⊤ : Subgroup I) = 6 ∧ E3.mParam X = 2 ∧
            ∀ c : MulAut I, (∀ l ∈ L, c * l = l * c) → c ^ 3 = 1)

@[expose] def K14_2Cent : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ L : Subgroup (MulAut W),
      CFSG.LocalAnalysis.UniquenessCase.UC22.IsSL3 ↥L 2 → Subgroup.center ↥L ≠ ⊥ →
      Odd (Nat.card (Subgroup.center ↥L)) →
      rk ↥(⊤ : Subgroup W) ≤ 12 → fixV L = ⊥ → commV L = ⊤ →
      (∃ x ∈ Subgroup.normalizer (L : Set (MulAut W)), ∃ S : Subgroup (MulAut W),
        IsSylowIn 2 S L ∧ x ∈ Subgroup.normalizer (S : Set (MulAut W)) ∧
        ∃ P : Subgroup (MulAut W), S17.IsMaxParabolicOver L S P ∧
          P.map (MulAut.conj x).toMonoidHom ≠ P) →
      ∀ c : MulAut W, (∀ l ∈ L, c * l = l * c) → c ^ 6 = 1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

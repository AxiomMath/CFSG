module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Notation
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.GH74.Uniqueness.SU.SU5Q8D8

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

@[expose] def K49 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H X L Q I : Subgroup G),
    X ≤ H → Nat.card X = 3 →
    L ∈ CFSG.RankThree.PartTwo.oTwoComponentsIn H → IsAlt (Bar2 L) 5 →
    ¬ X ≤ Subgroup.normalizer (L : Set G) →
    Q = CFSG.Open.pCoreOf 2 H → H = X ⊔ L ⊔ Q →
    CFSG.Quasithin.IsExt ↥(CFSG.Quasithin.perfectCore (Subgroup.centralizer (X : Set G)))
      (fun V _ => CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8 (⊤ : Subgroup V))
      (fun Y _ => CFSG.Quasithin.IsAlt 5 Y) →
    I = ⨆ x ∈ X, CFSG.conjugate L x →
    (∀ x ∈ X, ∀ y ∈ X, CFSG.conjugate L x ≠ CFSG.conjugate L y →
      ⁅CFSG.conjugate L x, CFSG.conjugate L y⁆ = ⊥) ∧
    (Q = (Q ⊓ Subgroup.centralizer (I : Set G)) ⊔ ⁅Q, I⁆ ∧
      ⁅Q ⊓ Subgroup.centralizer (I : Set G), ⁅Q, I⁆⁆ = ⊥) ∧
    ((IsMulCommutative ↥(Q ⊓ Subgroup.centralizer (I : Set G)) ∨
        CFSG.Open.pRank 2 (Q ⊓ Subgroup.centralizer (I : Set G)) = 1) →
      CFSG.Open.IsElemAbelian 2
        (CFSG.RankThree.PartOne.omegaOne 2 (Q ⊓ Subgroup.centralizer (I : Set G))) ∧
      H ≤ Subgroup.normalizer
        (CFSG.RankThree.PartOne.omegaOne 2 (Q ⊓ Subgroup.centralizer (I : Set G)) : Set G) ∧
      ∀ (p : ℕ), p.Prime → ∀ E : Subgroup G, E ≤ H → H ≤ Subgroup.normalizer (E : Set G) →
        CFSG.Open.IsElemAbelian p E →
        E ≤ CFSG.RankThree.PartOne.omegaOne 2 (Q ⊓ Subgroup.centralizer (I : Set G)))

@[expose] def K49I : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H X L Q I : Subgroup G),
    X ≤ H → Nat.card X = 3 →
    L ∈ CFSG.RankThree.PartTwo.oTwoComponentsIn H → IsAlt (Bar2 L) 5 →
    ¬ X ≤ Subgroup.normalizer (L : Set G) →
    Q = CFSG.Open.pCoreOf 2 H → H = X ⊔ L ⊔ Q →
    I = ⨆ x ∈ X, CFSG.conjugate L x →
    CFSG.Quasithin.IsExt
      ↥(CFSG.Quasithin.perfectCore (Subgroup.centralizer (X : Set G) ⊓ I))
      (fun V _ => CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8 (⊤ : Subgroup V))
      (fun Y _ => CFSG.Quasithin.IsAlt 5 Y) →
    (∀ x ∈ X, ∀ y ∈ X, CFSG.conjugate L x ≠ CFSG.conjugate L y →
      ⁅CFSG.conjugate L x, CFSG.conjugate L y⁆ = ⊥) ∧
    (Q = (Q ⊓ Subgroup.centralizer (I : Set G)) ⊔ ⁅Q, I⁆ ∧
      ⁅Q ⊓ Subgroup.centralizer (I : Set G), ⁅Q, I⁆⁆ = ⊥) ∧
    ((IsMulCommutative ↥(Q ⊓ Subgroup.centralizer (I : Set G)) ∨
        CFSG.Open.pRank 2 (Q ⊓ Subgroup.centralizer (I : Set G)) = 1) →
      CFSG.Open.IsElemAbelian 2
        (CFSG.RankThree.PartOne.omegaOne 2 (Q ⊓ Subgroup.centralizer (I : Set G))) ∧
      H ≤ Subgroup.normalizer
        (CFSG.RankThree.PartOne.omegaOne 2 (Q ⊓ Subgroup.centralizer (I : Set G)) : Set G) ∧
      ∀ (p : ℕ), p.Prime → ∀ E : Subgroup G, E ≤ H → H ≤ Subgroup.normalizer (E : Set G) →
        CFSG.Open.IsElemAbelian p E →
        E ≤ CFSG.RankThree.PartOne.omegaOne 2 (Q ⊓ Subgroup.centralizer (I : Set G)))

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

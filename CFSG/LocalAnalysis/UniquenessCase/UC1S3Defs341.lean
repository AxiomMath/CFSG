module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InS3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4

@[expose] def K341 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G),
    CFSG.Open.IsElemAbelian 3 A → Nat.card A = 27 →
    Maximal (fun B : Subgroup G => CFSG.Open.IsElemAbelian 3 B) A →
    (∀ x ∈ A, x ≠ 1 → CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({x} : Set G))) →
    (∀ x ∈ A, x ≠ 1 →
      CFSG.Open.twoLocalPrimeRank 3 ↥(Subgroup.centralizer ({x} : Set G)) ≤ 3) →
    (∀ x ∈ A, x ≠ 1 → ∀ L ∈ thetaComponentsAt 3 x, A ≤ Subgroup.normalizer (L : Set G)) →
    (∀ x ∈ A, x ≠ 1 → ∀ L ∈ thetaComponentsAt 3 x, Nat.card (autThetaQuot A L) = 9 →
      thetaAlpha 3 ((autThetaQuot A L).subgroupOf
        (autThetaQuot (Subgroup.centralizer ({x} : Set G)) L)) = ⊥) →
    (∀ E ∈ hyperplanes 3 A,
      Group.IsSolvable ↥(thetaAlpha 3 E) ∧ Nat.Coprime 3 (Nat.card ↥(thetaAlpha 3 E))) ∧
    (∀ E ∈ hyperplanes 3 A, ∀ D ∈ hyperplanes 3 A, thetaAlpha 3 E = thetaAlpha 3 D)

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

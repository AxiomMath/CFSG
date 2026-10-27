module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F09 (Inv9)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)

variable {G : Type} [Group G] [Finite G]

@[expose] def Hyp919c (D : Data G) (L D₃ Y H : Subgroup G) : Prop :=
  L ∈ calC D.M ∧ D₃ ≤ L ∧ Nat.card D₃ = 3 ∧ D₃ ∈ uniqueSet D.M ∧
    Y ≤ D.M ∧ L = (L ⊓ Y) ⊔ pCoreOf 2 L ∧
    ((L ⊓ Y).subgroupOf Y).Normal ∧ (∃ k : ℕ, ((L ⊓ Y).subgroupOf Y).index = 2 ^ k) ∧
    H ≠ ⊤ ∧ Y ≤ H ∧ ¬ H ≤ D.M

@[expose] def R920c (D : Data G) : Prop :=
  ∀ L D₃ Y H : Subgroup G, Hyp919c D L D₃ Y H →
    (∃ q : ℕ, q.Prime ∧ 5 < q ∧ IsL2Odd (Bar2 Y) q ∧
        ∃ A : Subgroup G, A ≤ Y ∧ (Nat.card A).Prime ∧ Odd (Nat.card A) ∧
          ¬ normalizer (A : Set G) ≤ D.M) ∨
    (∃ n : ℕ, 1 < n ∧ IsL2 (Bar2 Y) (2 * n) ∧ pCoreOf 2 D.M ⊓ H = ⊥) ∨
    (∃ n : ℕ, Odd n ∧ IsL2 (Bar2 Y) n ∧
        ((∃ A : Subgroup G, A ∈ uniqueSet D.M ∧ A ≤ Y ∧ (Nat.card A).Prime ∧
            Nat.card A ∣ 2 ^ n - 1) →
          ∀ R ∈ Inv9 (H ⊓ D.M) Y 2, R = ⊥)) ∨
    IsAlt (Bar2 Y) 5

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

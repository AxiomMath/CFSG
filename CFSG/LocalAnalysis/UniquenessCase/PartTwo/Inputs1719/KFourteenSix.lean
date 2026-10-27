module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup

@[expose] def K_UC146N : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N T A K : Subgroup G) (r : ℕ),
    CFSG.Open.IsKGroup ↥N → CFSG.ABGLocalTools.IsSylowOf 2 T N →
    r.Prime → 3 < r → (∃ n : ℕ, Odd n ∧ r ∣ 2 ^ n + 1) →
    A ≤ N → Nat.card A = r → UC22.Permutes A T →
    CFSG.Open.pRank 3 N ≤ 1 → CFSG.Open.pRank r N ≤ 1 →
    (∀ s : ℕ, s.Prime → 3 < s → CFSG.Open.pRank s N ≤ 2) →
    A ⊔ T ≤ K → N ⊓ normalizer (A : Set G) ≤ K →
    UC22.conjClosure N A ≤ K ∨
      (⁅CFSG.Open.pCoreOf 2 (A ⊔ T), A⁆ ≤ CFSG.Open.pCoreOf 2 (UC22.conjClosure N A) ∧
        (Group.IsSolvable ↥(UC22.conjClosure N A) ∨
          (IsSimpleGroup (UC22.BarInf (UC22.conjClosure N A)) ∧
            ((∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 5 < p ^ e ∧
                CFSG.Quasithin.F6.IsL2 p e (UC22.BarInf (UC22.conjClosure N A))) ∨
              ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧
                (CFSG.Blueprint.LieModel (UC22.BarInf (UC22.conjClosure N A)) .PSL 3 p f ∨
                  CFSG.Blueprint.LieModel (UC22.BarInf (UC22.conjClosure N A)) .PSU 3 p f))))) ∨
      ∃ E : Subgroup G, E ≤ K ∧ ⁅E, E⁆ = E ∧ A ≤ normalizer (E : Set G) ∧
        ¬ r ∣ Nat.card E ∧ ¬ ⁅E, A⁆ ≤ UC22.OInf E

@[expose] def K_UC146M : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y A E : Subgroup G) (n r : ℕ),
    UC22.IsSU3 (UC22.Bar2 Y) n → r.Prime → 3 < r → A ≤ Y → Nat.card A = r →
    E ≤ normalizer (Y : Set G) → ⁅E, E⁆ = E → A ≤ normalizer (E : Set G) →
    ¬ r ∣ Nat.card E → ⁅E, A⁆ ≤ UC22.OInf E

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

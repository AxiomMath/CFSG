module

public import CFSG.RankThree.PartTwo.Sec20.OneBasics
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.RankThree.PartTwo.Sec20.OneFrontierCleanStatements

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late


theorem step2051Sylow_core {G : Type} [Group G] [Finite G] {M N : Subgroup G}
    (hcard : Nat.card N = 280 * Nat.card (N ⊓ M : Subgroup G)) (R : Subgroup G)
    (hR : CFSG.ABGLocalTools.IsSylowOf 2 R N)
    (hRM : CFSG.ABGLocalTools.IsSylowOf 2 (R ⊓ M) (M ⊓ N)) : (R ⊓ M).relIndex R = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNM0 : Nat.card (N ⊓ M : Subgroup G) ≠ 0 := Nat.card_pos.ne'
  have h280 : (280 : ℕ).factorization 2 = 3 := by
    rw [show (280 : ℕ) = 2 ^ 3 * 35 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hfac : (Nat.card N).factorization 2 =
      3 + (Nat.card (M ⊓ N : Subgroup G)).factorization 2 := by
    rw [hcard, inf_comm M N, Nat.factorization_mul (by norm_num) hNM0, Finsupp.add_apply, h280]
  have h3 := Subgroup.relIndex_mul_card (R ⊓ M) R
  rw [show R ⊓ M ⊓ R = R ⊓ M by rw [inf_comm, ← inf_assoc, inf_idem], hR.card_eq,
    hRM.card_eq, hfac, pow_add] at h3
  have hpos : 0 < 2 ^ (Nat.card (M ⊓ N : Subgroup G)).factorization 2 := by positivity
  exact Nat.eq_of_mul_eq_mul_right hpos (h3.trans (by norm_num))

theorem step2051Sylow_of (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1) :
    Step2051Sylow := fun _ _ _ _ _ _ _ _ _ hT R hR hRM =>
  step2051Sylow_core (card_eq_of_hyp201One h1812 h184 hT.hyp201One) R hR hRM

end CFSG.RankThree.PartTwo.Sec20

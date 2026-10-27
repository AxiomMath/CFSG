module

public import CFSG.RankThree.PartOne.FOC.SylowData
public import CFSG.RankThree.PartOne.K128.ReeShape
public import CFSG.RankThree.PartOne.FOCD.PRank

public section

namespace CFSG.RankThree.PartOne.FOC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FOCD
open CFSG.RankThree.PartOne.K128 CFSG.RankThree.LargeReeOrder


theorem sylowData_ree {a p : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {T : Type} [Group T] [Finite T]
    (e : T ≃* ReeTag.F4.reeGamma K a) (hp : p.Prime) (hp5 : 5 ≤ p) :
    SylowAbelian p T ∧ PRankLeTwo p T := by
  by_cases hpT : p ∣ Nat.card T
  swap
  · exact ⟨sylowAbelian_of_not_dvd hp hpT, pRankLeTwo_of_not_dvd hp hpT⟩
  have hdvd : p ∣ Nat.card (ReeTag.F4.reeGamma K a) := by
    rw [← Nat.card_congr e.toEquiv]
    exact hpT
  have hpr : ∀ h : CFSG.pRank p (ReeTag.F4.reeGamma K a) ≤ 1,
      SylowAbelian p T ∧ PRankLeTwo p T := fun h => by
    have h2 : CFSG.pRank p T ≤ 1 := by
      rw [pRank_eq_of_mulEquiv_of_one_lt hp.one_lt e]
      exact h
    exact ⟨sylowAbelian_of_pRank_le_one hp (by omega) h2, pRankLeTwo_of_pRank_le_one hp h2⟩
  have hsh : ∀ {e' : ℕ}, K1214.SylowShape p 2 e' (ReeTag.F4.reeGamma K a) →
      SylowAbelian p T ∧ PRankLeTwo p T := fun h => by
    have h' := h.of_mulEquiv e
    exact ⟨sylowAbelian_of_shape hp h', pRankLeTwo_of_sylowShape hp h'⟩
  rcases (large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK).2 p hp (by omega)
      hdvd with h1 | h2 | h3 | h4 | h5
  · exact hsh (sylowShape_ree_phi1 hK hp hp5 h1)
  · exact hsh (sylowShape_ree_phi2 hK hp hp5 h2)
  · exact hsh (sylowShape_ree_phi4 hK hp hp5 h3)
  · exact hpr (pRank_le_one_ree_phi6 hK hp hp5 h4)
  · exact hpr (pRank_le_one_ree_phi12 hK hp hp5 h5)

end CFSG.RankThree.PartOne.FOC

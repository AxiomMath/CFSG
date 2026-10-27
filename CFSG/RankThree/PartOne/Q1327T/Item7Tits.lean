module

public import CFSG.RankThree.PartOne.Q1327T.Item7U3
public import CFSG.RankThree.PartOne.KF.ClsTits
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K133
  CFSG.Sporadic.Schreier.Tits
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem row8U3At_leaf7_ten
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    Row8U3At (K133.leaf7 10) := by
  intro Q _ _ p g Ē hX h
  have hX' := hX
  obtain ⟨hv, ⟨e0⟩⟩ := hX
  have hp := h.prime
  have hp5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have hm : Models.LieModel (Q ⧸ Subgroup.center Q) .Tits 0 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩,
      Or.inr ⟨rfl, ⟨.tits, hv⟩, ⟨rfl, rfl⟩, ⟨e0⟩⟩⟩
  have hZ : Subgroup.center Q = ⊥ := by
    refine center_eq_bot_of_multiplier hp hGA h.quasisimple h.center_p hm ?_
    have hgen : Blueprint.Multiplier.genericOrders .Tits 0 2 1 = (1, 1) := rfl
    have hexc : Blueprint.Multiplier.exceptionalOrders .Tits 0 2 1 = (1, 1) := by
      unfold Blueprint.Multiplier.exceptionalOrders
      split <;> simp_all
    unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
    rw [hgen, hexc]
    simp [hp.one_lt.ne']
  exfalso
  obtain ⟨eS⟩ := titsModelEquiv (Q ⧸ Subgroup.center Q) 2 1
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits hX')
  let ce : Q ≃* (Q ⧸ Subgroup.center Q) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  let eD : Q ≃* titsD := ce.trans eS
  have hdvd : p ^ 2 ∣ 17971200 := by
    rw [← card_titsD, ← Nat.card_congr eD.toEquiv, ← h.card]
    exact Subgroup.card_subgroup_dvd_card Ē
  have hp5' : p = 5 := by
    by_contra hne
    have hp7 : 7 ≤ p := by
      rcases Nat.lt_or_ge p 7 with h6 | h6
      · interval_cases p
        · exact absurd rfl hne
        · exact absurd hp (by norm_num)
      · exact h6
    exact KFU.not_sq_dvd_card_titsD hp hp7 hdvd
  subst hp5'
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  obtain ⟨c, hcE, hc1, Kb, x, hKbc, hKbN, hmodKb, hxK, hxo, hgen⟩ := h.conf
  have := h.elem
  have hc5 : orderOf c = 5 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (A := Ē) c hcE) hc1
  have h4 := KE.tits_not_four_dvd_card_centralizer_of_mulEquiv eD hc5
  apply h4
  have h4Kb : 4 ∣ Nat.card Kb := by
    rw [card_psl2_even hmodKb]
    exact Dvd.dvd.mul_right (by
      have := pow_dvd_pow 2 h.g_two
      simpa using this) _
  exact h4Kb.trans (Subgroup.card_dvd_of_le hKbc)

end CFSG.RankThree.PartOne.Q1327T

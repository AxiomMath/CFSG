module

public import CFSG.RankThree.PartOne.Q1327T.Item7Inv
public import CFSG.RankThree.PartOne.K133X.G2
public import CFSG.RankThree.PartOne.K128.G2Syl
public import CFSG.RankThree.PartOne.SEITZ3.MaxDefs
public import CFSG.RankThree.PartOne.N143X.EvenSmall

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K133 CFSG.Timmesfeld.ExceptionalOrders
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem card_multiplier_G2_dvd_two (f : ℕ) :
    Nat.card (Blueprint.Multiplier.generic .G2 0 2 f × Blueprint.Multiplier.exceptional .G2 0 2 f) ∣
      2 := by
  have hgen : Blueprint.Multiplier.genericOrders .G2 0 2 f = (1, 1) := rfl
  have hexc : Blueprint.Multiplier.exceptionalOrders .G2 0 2 f = (2, 1) ∨
      Blueprint.Multiplier.exceptionalOrders .G2 0 2 f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen]
  rcases hexc with h | h <;> rw [h] <;> simp

theorem factorization_card_sl2 {K : Type} [Field K] [Finite K] {p : ℕ} (hpQ : ¬ p ∣ Nat.card K)
    (hQ : 2 ≤ Nat.card K) :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) K)).factorization p =
      (Nat.card K ^ 2 - 1).factorization p := by
  have hA : Nat.card K ^ 2 - 1 ≠ 0 := by
    have : 4 ≤ Nat.card K ^ 2 := by nlinarith
    omega
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    Nat.factorization_mul (by omega) hA, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hpQ, zero_add]

theorem row8U3At_leaf7_five
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    Row8U3At (K133.leaf7 5) := by
  intro Q _ _ p g Ē hX h
  obtain ⟨q, hq2, hiso⟩ := hX
  have hp := h.prime
  have hp5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have hmodel := K133X.chevalleyExceptionalModel_G2_of_isoLie hq2 hiso
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  have hLie : Models.LieModel (Q ⧸ Subgroup.center Q) .G2 0 2 q.exponent :=
    ⟨hmodel.1, Or.inr ⟨rfl, ⟨.G2 q, hv⟩, ⟨hq2, rfl⟩, ⟨e0⟩⟩⟩
  have hZ : Subgroup.center Q = ⊥ := by
    refine center_eq_bot_of_multiplier hp hGA h.quasisimple h.center_p hLie fun hd => ?_
    have := Nat.le_of_dvd (by norm_num) (hd.trans (card_multiplier_G2_dvd_two q.exponent))
    omega
  refine h.concl_of_inv hZ ?_
  obtain ⟨K, _, _, hK, ⟨θ⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hmodel.2
  have hm : 1 ≤ q.exponent := hmodel.1.2.1
  have : CharP K 2 := N143X.charP_two_of_card hK
  let ce : Q ≃* Q ⧸ Subgroup.center Q :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  let eQ : Q ≃* adjointGroup .G2 K := ce.trans θ
  refine exists_inv_of_equiv eQ ?_
  have hEel : IsElementaryAbelian p (Ē.map eQ.toMonoidHom) := by
    have := h.elem
    have : Fact p.Prime := ⟨hp⟩
    exact IsElementaryAbelian.map _
  have hEcard : Nat.card (Ē.map eQ.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective eQ.injective, h.card]
  have hQ2 : 2 ≤ Nat.card K := by
    rw [hK]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hm
  have hpQ : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  by_cases hd : p ∣ Nat.card K ^ 2 - 1
  · have hord : (Nat.card (adjointGroup .G2 K)).factorization p =
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) K)).factorization p +
          (Nat.card (Matrix.SpecialLinearGroup (Fin 2) K)).factorization p := by
      rw [card_adjointGroup_G2, K128.factorization_ordG2 hp hp5 hQ2 hpQ hd,
        factorization_card_sl2 hpQ hQ2]
      ring
    exact exists_inv_of_prod_sl2 (SEITZ3.a1a1Hom K) SEITZ3.a1a1Hom_injective hp hp2 hord
      (IsElementaryAbelian.isPGroup p _)
  · exfalso
    have hpC : p ∣ Nat.card (adjointGroup .G2 K) := by
      have h1 := Subgroup.card_subgroup_dvd_card (Ē.map eQ.toMonoidHom)
      rw [hEcard] at h1
      exact (dvd_pow_self p two_ne_zero).trans h1
    have hrk := K128.pRank_le_one_G2 K hp hp5 hK hm hpC hd
    have h2 := CFSG.LieType.SteinbergBR.le_pRank_of_card hp.one_lt _ hEel hEcard
    omega

end CFSG.RankThree.PartOne.Q1327T

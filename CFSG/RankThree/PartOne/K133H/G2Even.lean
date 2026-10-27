module

public import CFSG.RankThree.PartOne.K133H.G2Core
public import CFSG.RankThree.PartOne.K133X.G2
public import CFSG.RankThree.PartOne.N143X.EvenSmall
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.RankThree.PartOne.K133H

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K133 CFSG.RankThree.PartOne.Q1327T
  CFSG.RankThree.PartOne.K133B CFSG.Timmesfeld.ExceptionalOrders
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)
open CFSG.RankThree.PartOne.Census3 (IsoLie)

set_option linter.unusedSectionVars false

theorem row8OddAt_leaf7_five : Row8OddAt (K133.leaf7 5) := by
  intro Q _ _ p g Ē hp11 hZ hX h
  obtain ⟨q, hq2, hiso⟩ := hX
  have hp := h.prime
  have hp5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hmodel := K133X.chevalleyExceptionalModel_G2_of_isoLie hq2 hiso
  obtain ⟨K, _, _, hK, ⟨θ⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hmodel.2
  have hm : 1 ≤ q.exponent := hmodel.1.2.1
  have : CharP K 2 := N143X.charP_two_of_card hK
  let ce : Q ≃* Q ⧸ Subgroup.center Q :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  let eQ : Q ≃* adjointGroup .G2 K := ce.trans θ
  have hEel : IsElementaryAbelian p (Ē.map eQ.toMonoidHom) := by
    have := h.elem
    exact IsElementaryAbelian.map _
  have hEcard : Nat.card (Ē.map eQ.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective eQ.injective, h.card]
  have hpQ : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  by_cases hd : p ∣ Nat.card K ^ 2 - 1
  · exact row8OddConcl_of_G2 (ℓ := 2) h eQ hpQ hd
  · exfalso
    have hpC : p ∣ Nat.card (adjointGroup .G2 K) := by
      have h1 := Subgroup.card_subgroup_dvd_card (Ē.map eQ.toMonoidHom)
      rw [hEcard] at h1
      exact (dvd_pow_self p two_ne_zero).trans h1
    have hrk := K128.pRank_le_one_G2 K hp hp5 hK hm hpC hd
    have h2 := CFSG.LieType.SteinbergBR.le_pRank_of_card hp.one_lt _ hEel hEcard
    omega

end CFSG.RankThree.PartOne.K133H

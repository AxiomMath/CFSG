module

public import CFSG.RankThree.GF2n.Smith81.S81CCases
public import CFSG.RankThree.GF2n.Stroth80.Sec1111NotTI
import CFSG.Adapters.StatedClassicalOrders

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G]

theorem card_statedProj_six_lt_card_statedSL_ten {K K' : Type} [Field K] [Finite K] [Field K']
    [Finite K'] (hKK : Nat.card K' = Nat.card K) (hq : 2 ≤ Nat.card K) :
    Nat.card (StatedProj (StatedSL 6 K')) < Nat.card (StatedSL 10 K) := by
  set q := Nat.card K with hqdef
  have hq0 : 0 < q := by omega
  have hP : Nat.card (StatedProj (StatedSL 6 K')) ≤ Nat.card (StatedSL 6 K') := by
    have hpos : 0 < Nat.card (StatedSL 6 K') := Nat.card_pos
    exact Nat.le_of_dvd hpos (Subgroup.card_quotient_dvd_card _)
  have h6 : Nat.card (StatedSL 6 K') ≤ q ^ 35 := by
    rw [CFSG.Open.StatedAPI.card_statedSL_eq_prod (by norm_num), hKK]
    have hprod : ∏ j ∈ Finset.Icc 2 6, (q ^ j - 1) ≤ ∏ j ∈ Finset.Icc 2 6, q ^ j :=
      Finset.prod_le_prod' fun j _ => Nat.sub_le _ _
    rw [Finset.prod_pow_eq_pow_sum] at hprod
    have hsum : ∑ j ∈ Finset.Icc 2 6, j = 20 := by decide
    rw [hsum] at hprod
    calc q ^ (6 * (6 - 1) / 2) * ∏ j ∈ Finset.Icc 2 6, (q ^ j - 1) ≤ q ^ 15 * q ^ 20 :=
          Nat.mul_le_mul (le_of_eq (by norm_num)) hprod
      _ = q ^ 35 := by rw [← pow_add]
  have h10 : q ^ 45 ≤ Nat.card (StatedSL 10 K) := by
    rw [CFSG.Open.StatedAPI.card_statedSL_eq_prod (by norm_num)]
    have hprod : 0 < ∏ j ∈ Finset.Icc 2 10, (q ^ j - 1) := by
      refine Finset.prod_pos fun j hj => ?_
      have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
      have : 2 ≤ q ^ j := le_trans hq (Nat.le_self_pow (by omega) q)
      omega
    calc q ^ 45 = q ^ (10 * (10 - 1) / 2) * 1 := by norm_num
      _ ≤ q ^ (10 * (10 - 1) / 2) * ∏ j ∈ Finset.Icc 2 10, (q ^ j - 1) :=
          Nat.mul_le_mul_left _ hprod
  have hlt : q ^ 35 < q ^ 45 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

theorem noA2All_of_inCaseE3L [Finite G] {M Q Z B : Subgroup G}
    (hc : Cfg M Q Z B) (h3L : InCaseE3L M Q Z B) : NoA2All M Q Z := by
  obtain ⟨t, -, hQ, -, hS⟩ := h3L
  have hq4 : 4 ≤ Nat.card Z := hc.ctx.hyp.q4
  have hq2 : 2 ≤ Nat.card Z := le_trans (by norm_num) hq4
  obtain ⟨h1, -⟩ := hc.conclusion
  rcases h1 with ⟨n, hqn, hL3⟩ | ⟨hQ5, -⟩ | ⟨hQ9, -, -⟩ | ⟨-, hA | hVI⟩
  ·
    exfalso
    obtain ⟨e⟩ := hL3
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hqn
      omega
    have hQ3 : Nat.card Q = Nat.card Z ^ 3 := by
      rw [Nat.card_congr e.toEquiv, Tim79.card_ut3, GaloisField.card 2 n hn0, hqn]
    have h := Nat.pow_right_injective hq2 (hQ3.symm.trans hQ)
    omega
  ·
    exfalso
    have h := Nat.pow_right_injective hq2 (hQ5.symm.trans hQ)
    omega
  ·
    exfalso
    have h := Nat.pow_right_injective hq2 (hQ9.symm.trans hQ)
    omega
  ·
    exact hA.1
  ·
    exfalso
    have hw : Width Q Z 10 := hQ
    obtain ⟨K, _, _, hK, φ, hr, hk, -⟩ := caseVICore_of_caseVI hc.ctx hw hVI
    obtain ⟨hN, K', _, _, hK', ⟨e⟩⟩ := hS
    have h10 : Nat.card (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B))) =
        Nat.card (StatedSL 10 K) := by
      rw [← hk, Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hr]
    have h6 := Nat.card_congr e.toEquiv
    have hlt := card_statedProj_six_lt_card_statedSL_ten (K := K) (K' := K')
      (hK'.trans hK.symm) (hK ▸ hq2)
    omega

end CFSG.RankThree.GF2n.Smith81

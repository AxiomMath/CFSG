module

public import CFSG.RankThree.GF2n.Smith81.S81BLane
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitOrder
import CFSG.Adapters.StatedClassicalOrders
public import CFSG.RankThree.GF2n.Stroth80.Sec1111NotTI

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G]

theorem card_statedProjSU_six_lt_card_statedSL_ten {K K' : Type} [Field K] [Finite K] [Field K']
    [Finite K'] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hK' : Nat.card K' = (2 ^ f) ^ 2)
    (hq : 4 ≤ 2 ^ f) :
    Nat.card (StatedProj (StatedSU 6 (2 ^ f) K')) < Nat.card (StatedSL 10 K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set q := 2 ^ f with hqdef
  have hP : Nat.card (StatedProj (StatedSU 6 q K')) ≤ Nat.card (StatedSU 6 q K') := by
    have hpos : 0 < Nat.card (StatedSU 6 q K') := Nat.card_pos
    exact Nat.le_of_dvd hpos (Subgroup.card_quotient_dvd_card _)
  have hU : Nat.card (StatedSU 6 q K') ≤ 2 * q ^ 35 := by
    have := CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.card_statedSU_le (p := 2) (e := f)
      (n := 6) hK' (by norm_num)
    simpa using this
  have h10 : q ^ 45 ≤ Nat.card (StatedSL 10 K) := by
    rw [CFSG.Open.StatedAPI.card_statedSL_eq_prod (by norm_num), hK]
    have hprod : 0 < ∏ j ∈ Finset.Icc 2 10, (q ^ j - 1) := by
      refine Finset.prod_pos fun j hj => ?_
      have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
      have : 2 ≤ q ^ j := le_trans (by omega) (Nat.le_self_pow (by omega) q)
      omega
    calc q ^ 45 = q ^ (10 * (10 - 1) / 2) * 1 := by norm_num
      _ ≤ q ^ (10 * (10 - 1) / 2) * ∏ j ∈ Finset.Icc 2 10, (q ^ j - 1) :=
          Nat.mul_le_mul_left _ hprod
  have hlt : 2 * q ^ 35 < q ^ 45 := by
    have h10' : 2 < q ^ 10 := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_left hq 10)
    calc 2 * q ^ 35 < q ^ 10 * q ^ 35 := by
          exact Nat.mul_lt_mul_of_pos_right h10' (pow_pos (by omega) 35)
      _ = q ^ 45 := by rw [← pow_add]
  omega

theorem noA2All_of_inCaseE3U [Finite G] {M Q Z B : Subgroup G}
    (hc : Cfg M Q Z B) (h3U : InCaseE3U M Q Z B) : NoA2All M Q Z := by
  obtain ⟨t, -, hQ, -, hS⟩ := h3U
  have hq4 : 4 ≤ Nat.card Z := hc.ctx.hyp.q4
  have hq2 : 2 ≤ Nat.card Z := le_trans (by norm_num) hq4
  obtain ⟨fz, -, hfz, -⟩ := hc.ctx.hyp.cp
  obtain ⟨h1, -⟩ := hc.conclusion
  rcases h1 with ⟨n, hqn, hL3⟩ | ⟨hQ5, -⟩ | ⟨hQ9, -, -⟩ | ⟨-, hA | hVI⟩
  · exfalso
    obtain ⟨e⟩ := hL3
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hqn
      omega
    have hQ3 : Nat.card Q = Nat.card Z ^ 3 := by
      rw [Nat.card_congr e.toEquiv, Tim79.card_ut3, GaloisField.card 2 n hn0, hqn]
    have h := Nat.pow_right_injective hq2 (hQ3.symm.trans hQ)
    omega
  · exfalso
    have h := Nat.pow_right_injective hq2 (hQ5.symm.trans hQ)
    omega
  · exfalso
    have h := Nat.pow_right_injective hq2 (hQ9.symm.trans hQ)
    omega
  · exact hA.1
  · exfalso
    have hw : Width Q Z 10 := hQ
    obtain ⟨K, _, _, hK, φ, hr, hk, -⟩ := caseVICore_of_caseVI hc.ctx hw hVI
    obtain ⟨hN, K', _, _, hK', ⟨e⟩⟩ := hS
    have h10 : Nat.card (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B))) =
        Nat.card (StatedSL 10 K) := by
      rw [← hk, Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hr]
    have h6 := Nat.card_congr e.toEquiv
    rw [hfz] at hK' h6 hq4
    have hlt := card_statedProjSU_six_lt_card_statedSL_ten (K := K) (K' := K') (f := fz)
      (hK.trans hfz) hK' hq4
    omega

end CFSG.RankThree.GF2n.Smith81

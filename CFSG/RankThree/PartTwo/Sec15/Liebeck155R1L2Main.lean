module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2Tau
import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2AbsB
import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2AbsC
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1L65
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1TLeN

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem res1ZExclLeN_l2
    (h142 : Concl142S14) {Q : ∀ (X : Type) [Group X], Prop}
    (hCent : Sylow155R1.Res1CentLeMN Q Res1OpenL2Type) (hCT : Res1L2CThetaZ Q) :
    Sylow155R1.Res1ZExclLeN Q Res1OpenL2Type := by
  intro G _ _ A c L hR hq hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP
    hEA hEO hcomm hfield hLX hLΔ hKX hΩ hMX hMO hE0N z hz2 hzV hzC hzR hAz hKz hCN hJ
  have hYn : Yc.Normal := Sylow155R1.res1_isComponent_normal hS hY.1 hY.2.2.2.1.1
  obtain ⟨-, -, hodd, h3, -, -, -⟩ :=
    res1L2_prop142 hS hC hE h146 hRP hY hP hEA hEO hcomm hz2 hzR hAz
  set J := ⁅pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔
    pPrimeCoreOf 3 (u155 A M X))), Subgroup.zpowers z⁆ with hJdef
  have hJcard : Nat.card J ≠ 1 := fun h => hJ (Subgroup.eq_bot_of_card_eq J h)
  have hp : (Nat.card J).minFac.Prime := Nat.minFac_prime hJcard
  have hpd : (Nat.card J).minFac ∣ Nat.card J := Nat.minFac_dvd _
  set p := (Nat.card J).minFac with hpdef
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at hpd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpd)
  have hp3 : p ≠ 3 := fun h => h3 (h ▸ hpd)
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    by_contra hlt
    have : p = 2 ∨ p = 3 ∨ p = 4 := by omega
    rcases this with h | h | h
    · exact hp2 h
    · exact hp3 h
    · exact absurd (h ▸ hp) (by norm_num)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨jj, hjj⟩ := exists_prime_orderOf_dvd_card' (G := J) p hpd
  have hjp : orderOf (jj : G) = p := by rw [Subgroup.orderOf_coe]; exact hjj
  obtain ⟨D⟩ := res1L2Abs_of_tau h142 hCent hCT hR hq hN hS hC hmax habove hE h146 hRP hIX hY
    hsimple hP hEA hEO hcomm hfield hLX hLΔ hKX hΩ hMX hMO hE0N hz2 hzV hzC hzR hAz hKz hCN hp
    hp5 jj.2 hjp
  obtain ⟨R, hRΘ, hRp, hRmax, hRj⟩ := res1L2T_exists_sylow_normalized D.Θ D.hΘn D.j D.hj
  by_cases hRbot : R = ⊥
  · refine D.false_of_theta_pfree fun Xp hXΘ hXp => ?_
    have hle := res1L2A_card_le_of_maximal D.Θ R Xp hRΘ hXΘ hRp hXp hRmax
    rw [hRbot, Subgroup.card_bot] at hle
    exact Subgroup.eq_bot_of_card_eq Xp (le_antisymm hle Nat.card_pos)
  · by_cases hact : ∃ x ∈ R, D.j * x * D.j⁻¹ ≠ x
    · exact D.false_of_sylow_noncentral R hRΘ hRp hRmax hRj hact
    · push Not at hact
      refine D.false_of_sylow_central R hRΘ hRp hRmax hRbot fun x hx => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.mp (hact x hx)).symm

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2

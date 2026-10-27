module

import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T114
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T114B
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T120
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T131X
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T133
public import CFSG.RankThree.PartTwo.Sec15.Sylow155E0Defs
public import CFSG.RankThree.PartTwo.Sec17.RouteForms

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_orderOf_eq_two_mem_center {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h149 : Item149 A (lB A)) {X K Y M T : Subgroup G}
    (hC : Ctx155 A X K Y M T) (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G))
    (hKX : K = X ⊔ CFSG.Open.pCoreOf 2 K) :
    ∃ z : G, orderOf z = 2 ∧ z ∈ CFSG.Open.pCoreOf 2 K ∧
      z ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 K : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := CFSG.Open.pCoreOf 2 K with hVdef
  have hV2 : IsPGroup 2 ↥V := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K
  have hU1 : CFSG.Open.pCoreOf 2 X ≠ ⊥ := (isCharacteristicP_x_and_pCoreOf_ne_bot h h149 hC hIX).2
  have hUV : CFSG.Open.pCoreOf 2 X ≤ V := pCoreOf_le_pCoreOf_of_le_sup hC.le_k hKX.le
  have hV1 : V ≠ ⊥ := fun h0 => hU1 (eq_bot_iff.mpr (h0 ▸ hUV))
  haveI : Nontrivial ↥V := (Subgroup.nontrivial_iff_ne_bot V).mpr hV1
  haveI : Nontrivial (Subgroup.center ↥V) := hV2.center_nontrivial
  haveI : Fintype (Subgroup.center ↥V) := Fintype.ofFinite _
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (hV2.to_subgroup (Subgroup.center ↥V))
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    have := Finite.one_lt_card (α := Subgroup.center ↥V)
    omega
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 2
    (show 2 ∣ Fintype.card (Subgroup.center ↥V) by
      rw [← Nat.card_eq_fintype_card, hn]
      exact dvd_pow_self 2 hn0)
  refine ⟨((x : ↥V) : G), ?_, (x : ↥V).2, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  · rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp x.2 ⟨g, hg⟩)

theorem exists_involution_of_not_le {A : Subgroup G} {c : G} {L : Subgroup G}
    (hR : Sec15R G A c L) (hbot : Item145BotS14) (h1444 : Item1444 A (lB A))
    (h146 : Item146 A (lB A)) (h149 : Item149 A (lB A)) (h153 : Item153Main A (lB A))
    {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T) (hmax : MaxT155 A X K T)
    (hab : Above155w A X) (hE : End155N A X K Y M T P) (hRP : CFSG.Open.pCoreOf 2 Y ≤ P)
    (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G))
    (hEA : layerOddPreimage
        (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      Subgroup.centralizer (A : Set G))
    (hKX : K = X ⊔ CFSG.Open.pCoreOf 2 K)
    (hE0N : ¬ pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔
      pPrimeCoreOf 3 (u155 A M X))) ≤ n155 A K) :
    ∃ z : G, orderOf z = 2 ∧ z ∈ CFSG.Open.pCoreOf 2 K ∧
      z ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 K : Set G) ∧ z ∈ CFSG.Open.pCoreOf 2 Y ∧
      A ≤ Subgroup.centralizer ({z} : Set G) ∧ K ≤ Subgroup.centralizer ({z} : Set G) ∧
      Subgroup.centralizer ({z} : Set G) ≤ n155 A K ∧
      ⁅pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))),
        Subgroup.zpowers z⁆ ≠ ⊥ := by
  have h : Sec14Std G A c L := hR.toSec14Std
  have hV : CFSG.Open.pCoreOf 2 K ∈ scriptQ A (lB A) :=
    pCoreOf_two_mem_scriptQ_of_eq_sup_x hR hbot h1444 h146 hC hE hRP hKX
  obtain ⟨z, hz2, hzV, hzC⟩ := exists_orderOf_eq_two_mem_center h h149 hC hIX hKX
  obtain ⟨hzR, hAz, hKz⟩ := mem_pCoreOf_two_of_mem_center h h1444 h146 h149 h153
    (hbot G A c L h) hC hmax hab hE hRP hIX hEA hKX hE0N hV hzV hzC
  have hCN := centralizer_le_n155 h153 hC.mem_k hz2 hAz hKz
  refine ⟨z, hz2, hzV, hzC, hzR, hAz, hKz, hCN, fun hJ => hE0N ?_⟩
  refine le_n155_of_le_centralizer h153 hC.mem_k hz2 hAz hKz fun o ho => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  subst hw
  have hc : ⁅o, w⁆ = 1 := by
    have hmem := Subgroup.commutator_mem_commutator ho (Subgroup.mem_zpowers w)
    rw [hJ] at hmem
    exact (Subgroup.mem_bot.mp hmem)
  rw [commutatorElement_eq_one_iff_mul_comm] at hc
  exact hc.symm

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1

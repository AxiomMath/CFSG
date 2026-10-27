module

public import CFSG.OddTranspositions.PartThree.EightFive.CaseTwoStatement

import CFSG.OddTranspositions.PartThree.EightFive.QNotCentralCoreBasic
import CFSG.Timmesfeld.Bridge.OddLocalCommonBasic
import CFSG.OddTranspositions.PartThree.EightFive.Transitive
import CFSG.OddTranspositions.PartThree.LocalBenderCenter
import CFSG.OddTranspositions.SevenThreeQuotient
import CFSG.Timmesfeld.Bridge.Asc72ElemCompQuot
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
import CFSG.GroupTheory.PCore.SolvableRadical
import CFSG.CGT.Timmesfeld75.Statements
import CFSG.CGT.Timmesfeld75.Targets
import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
import CFSG.Permutation.BurnsideSchur

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem mem_solvableRadical_of_commute_of_bender (hS : Setup G D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n) {z : G} (hzdef : (u * v * w) ^ n = z)
    (htrans : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * u * k⁻¹ = x)
    (hB : CFSG.BenderSuzuki.IsBenderGroup
      (localGroup D z ⧸ CFSG.solvableRadical (localGroup D z)))
    {e : localGroup D z} {k : ℕ} (he : e ^ 2 ^ k = 1) (heu : Commute (e : G) u)
    (hew : Commute (e : G) w) : e ∈ CFSG.solvableRadical (localGroup D z) := by
  classical
  set mk := QuotientGroup.mk' (CFSG.solvableRadical (localGroup D z)) with hmk
  obtain ⟨huC, -, hwC, -⟩ := thirdKind_mem_centSet hS htri hn hord
  rw [hzdef] at huC hwC
  have huK : u ∈ localGroup D z := mem_localGroup_of_mem huC
  have hwK : w ∈ localGroup D z := mem_localGroup_of_mem hwC
  rw [← QuotientGroup.eq_one_iff]
  by_contra hne
  have hpow : mk e ^ 2 ^ k = 1 := by rw [← map_pow, he, map_one]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hpow)
  have h2 : 2 ∣ orderOf (mk e) := by
    rcases j with _ | j
    · rw [pow_zero, orderOf_eq_one_iff] at hj
      exact absurd hj hne
    · rw [hj]
      exact dvd_pow_self 2 (Nat.succ_ne_zero j)
  have hs2 : orderOf (mk e ^ (orderOf (mk e) / 2)) = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos _).ne' h2
  have heu' : Commute (mk e) (mk ⟨u, huK⟩) :=
    ((commute_iff_eq _ _).mpr (Subtype.ext heu.eq)).map mk
  have hew' : Commute (mk e) (mk ⟨w, hwK⟩) :=
    ((commute_iff_eq _ _).mpr (Subtype.ext hew.eq)).map mk
  exact not_commute_mk_u_w hS htri hn hn1 hord hzdef htrans huC hwC huK hwK
    (OddLocal.IsBenderGroup.commute_trans hB
      (mk_centSet_orderOf_two hS htri hn hn1 hord hzdef htrans huC huK) hs2
      (mk_centSet_orderOf_two hS htri hn hn1 hord hzdef htrans hwC hwK)
      (heu'.pow_left _).symm (hew'.pow_left _))

theorem mem_pCore_of_mem_solvableRadical (hS : Setup G D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n) {z : G} (hzdef : (u * v * w) ^ n = z)
    (htrans : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * u * k⁻¹ = x)
    {e : localGroup D z} (heR : e ∈ CFSG.solvableRadical (localGroup D z)) {k : ℕ}
    (he : e ^ 2 ^ k = 1) : e ∈ CFSG.pCore 2 (localGroup D z) := by
  classical
  obtain ⟨hzz, -, -, -, -, -⟩ := htri.third_kind hS.oddT hS.normal hn hord
  obtain ⟨huC, hvC, -, hbC⟩ := thirdKind_mem_centSet hS htri hn hord
  rw [hzdef] at hzz huC hvC hbC
  have hzK : z ∈ localGroup D z := by
    have := thirdKind_z_mem_localGroup hS htri hn hord
    rwa [hzdef] at this
  have hne1 : ∀ x ∈ localSet D z,
      QuotientGroup.mk' (CFSG.pCore 2 (localGroup D z)) x ≠ 1 := by
    intro x hx h1
    exact centSet_not_mem_solvableRadical hS htri hn hn1 hord hzdef htrans hx
      (CFSG.pCore_le_solvableRadical 2 _ ((QuotientGroup.eq_one_iff x).mp h1))
  have hSK : Setup (localGroup D z) (localSet D z) :=
    setup_localGroup_of_transitive hS huC (transitive_pair_of_transitive htrans)
  have hSH : Setup (localGroup D z ⧸ CFSG.pCore 2 (localGroup D z))
      (QuotientGroup.mk' (CFSG.pCore 2 (localGroup D z)) '' localSet D z) := by
    obtain ⟨d₀, hd₀⟩ := hSK.isClass
    exact
      { isClass := image_isClass_quotient hd₀ _
        oddT := image_isOddTransp_quotient _ hSK.oddT hne1
        gen := image_closure_eq_top_quotient _ hSK.gen }
  set mk := QuotientGroup.mk' (CFSG.pCore 2 (localGroup D z)) with hmk
  have hmz : mk ⟨z, hzK⟩ = 1 := by
    have hzc : (⟨z, hzK⟩ : localGroup D z) ∈ Subgroup.center (localGroup D z) :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (commute_of_mem_localGroup g.2)
    have hz2 : (⟨z, hzK⟩ : localGroup D z) ^ 2 ^ 1 = 1 :=
      Subtype.ext (by simpa [pow_two] using hzz)
    have hZ : Subgroup.zpowers (⟨z, hzK⟩ : localGroup D z) ≤ CFSG.pCore 2 (localGroup D z) :=
      le_sSup ⟨Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hzc),
        IsPGroup.of_card_dvd_pow (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hz2)⟩
    exact (QuotientGroup.eq_one_iff _).mpr (hZ (Subgroup.mem_zpowers _))
  set uK : localGroup D z := ⟨u, mem_localGroup_of_mem huC⟩ with huK
  set vK : localGroup D z := ⟨v, mem_localGroup_of_mem hvC⟩ with hvK
  set bK : localGroup D z := ⟨u * v * z, mem_localGroup_of_mem hbC⟩ with hbK
  have hub : mk uK ∈ mk '' localSet D z := ⟨uK, huC, rfl⟩
  have hvb : mk vK ∈ mk '' localSet D z := ⟨vK, hvC, rfl⟩
  have hbb : mk bK ∈ mk '' localSet D z := ⟨bK, hbC, rfl⟩
  have hbuv : mk bK = mk uK * mk vK * 1 := by
    rw [show bK = uK * vK * ⟨z, hzK⟩ from Subtype.ext rfl, map_mul, map_mul, hmz]
  have huv : mk uK ≠ mk vK := by
    intro h
    apply hSH.oddT.ne_one hbb
    rw [hbuv, ← h, mul_one, ← map_mul,
      show uK * uK = 1 from Subtype.ext (hS.oddT.mul_self_eq_one htri.1), map_one]
  have hc : Commute (mk uK) (mk vK) :=
    ((commute_iff_eq _ _).mpr (Subtype.ext htri.2.2.2.2.1.eq)).map mk
  have hOodd : Odd (Nat.card (CFSG.oddCore (localGroup D z ⧸ CFSG.pCore 2 (localGroup D z)))) :=
    CFSG.ABGLocalTools.odd_card_oddCore
  have hOu := le_centralizer_of_mul_mul hSH hOodd hub hvb hbb huv hc
    (hSH.oddT.mul_self_eq_one hub) (hSH.oddT.mul_self_eq_one hvb) (hSH.oddT.ne_one hub)
    (hSH.oddT.ne_one hvb) (Subgroup.one_mem _) (mul_one 1) hbuv
  have hOZ : CFSG.oddCore (localGroup D z ⧸ CFSG.pCore 2 (localGroup D z)) ≤
      Subgroup.center (localGroup D z ⧸ CFSG.pCore 2 (localGroup D z)) := by
    refine CFSG.GroupTheory.le_center_of_centralizes_set hSH.gen fun d hd x hx => ?_
    obtain ⟨c, hc_eq⟩ := isConj_iff.mp (hSH.isConj hub hd)
    have hxcO := (inferInstance : (CFSG.oddCore
      (localGroup D z ⧸ CFSG.pCore 2 (localGroup D z))).Normal).conj_mem' x hx c
    have hconj := (Commute.conj_iff c).mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hOu hxcO).2)
    rwa [show c * (c⁻¹ * x * c) * c⁻¹ = x by group, hc_eq] at hconj
  have hO2 : CFSG.pCore 2 (localGroup D z ⧸ CFSG.pCore 2 (localGroup D z)) ≤
      Subgroup.center (localGroup D z ⧸ CFSG.pCore 2 (localGroup D z)) := by
    rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot]
    exact bot_le
  have hRad := otg2_solvableRadical_le_center hO2 hOZ
  have hRmap : (CFSG.solvableRadical (localGroup D z)).map mk ≤
      CFSG.solvableRadical (localGroup D z ⧸ CFSG.pCore 2 (localGroup D z)) := by
    have : Group.IsSolvable (CFSG.solvableRadical (localGroup D z)) :=
      OddTransp.isSolvable_solvableRadical
    exact OddTransp.le_solvableRadical
      ((OddTransp.solvableRadical_normal (localGroup D z)).map mk
        (QuotientGroup.mk'_surjective _))
      (Group.isSolvable_of_surjective (mk.subgroupMap_surjective _))
  have hec := hRad (hRmap ⟨e, heR, rfl⟩)
  have hpow : mk e ^ 2 ^ k = 1 := by rw [← map_pow, he, map_one]
  have hle : Subgroup.zpowers (mk e) ≤
      CFSG.pCore 2 (localGroup D z ⧸ CFSG.pCore 2 (localGroup D z)) :=
    le_sSup ⟨Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hec),
      IsPGroup.of_card_dvd_pow (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hpow)⟩
  rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot] at hle
  exact (QuotientGroup.eq_one_iff e).mp (Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers _)))

end CFSG.OddTranspositions.PartThree

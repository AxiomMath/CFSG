module

public import CFSG.OddTranspositions.PartThree.Eleven.Statements
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Hyp
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Pair
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Quandle
public import CFSG.OddTranspositions.PartThree.EightFive.KBarSetup
public import Certificates.Certificate2326
public import CFSG.OddTranspositions.PartThree.Eleven.OneTwo.LocalHypC
public import CFSG.OddTranspositions.PartThree.Eleven.OneTwo.ConnLemmas
public import CFSG.OddTranspositions.PartThree.Eleven.OneTwo.Wreath
public import CFSG.OddTranspositions.BenderMeetsSq
public import CFSG.OddTranspositions.WidthOne
public import CFSG.OddTranspositions.TheoremTwo.ImageConnected
public import CFSG.Timmesfeld.Bridge.Asc72ZMain
public import TauCeti.Algebra.Group.Subgroup.ZPowers
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.CGT.Timmesfeld75.Targets
public import CFSG.Fischer.NoF25.Local
public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.GroupTheory.PerfectLeOfPGroupQuotient
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan
public import CFSG.OddTranspositions.AlmostSimple
public import CFSG.OddTranspositions.Disconnected
public import CFSG.OddTranspositions.O4PairTenWidth
public import CFSG.OddTranspositions.WreathQuotient
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
public import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Th.Max3.Data
public import CFSG.Timmesfeld.Transvection.Statement

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

section Conn

theorem not_almostSimpleCase_of_localTwoA5 (h91 : Theorem9_1)
    {Y : Type} [Group Y] [Finite Y] {Λ : Set Y} (hS : Setup Y Λ)
    (hns : ¬ ∃ a ∈ Λ, ∃ b ∈ Λ, a ≠ b ∧ Commute a b ∧ a * b ∈ Λ)
    (h128 : ¬ 128 ∣ Nat.card Y) {d : Y} (hd : d ∈ Λ) (hL : LocalTwoA5 Λ d) :
    ¬ AlmostSimpleCase Y Λ := by
  intro hAS
  classical
  obtain ⟨M, hMnorm, hMmin, hMuniq, hMsimple, hCen, hidx, hW, hclass⟩ := hAS
  haveI : M.Normal := hMnorm
  haveI : IsSimpleGroup M := hMsimple
  let N : Subgroup Y := M ⊔ Subgroup.zpowers d
  have hdN : d ∈ N := Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
  let dN : N := ⟨d, hdN⟩
  have hMleN : M ≤ N := le_sup_left
  have hd2 : d * d = 1 := hS.oddT.mul_self_eq_one hd
  have hclass' : IsOddTranspClass (conjSet M d) := hclass d hd
  have hSN : Setup N (conjSet M d) := ⟨hclass'.1, hclass'.2.1, hclass'.2.2⟩
  have hmemΛ : ∀ {u : N}, u ∈ conjSet M d → (u : Y) ∈ Λ := by
    intro u hu
    obtain ⟨m, -, hmu⟩ := hu
    have hm : m * d * m⁻¹ ∈ Λ := hS.normal m d hd
    rwa [← hmu] at hm
  have hMminN : Asc72.IsMinimalNormal (M.subgroupOf N) :=
    isMinimalNormal_subgroupOf hMleN hMsimple
  have hrelIndex_le : (M.subgroupOf N).index ≤ 2 :=
    relIndex_sup_zpowers_le_two (M := M) (u := d) hd2
  have hCenN : Subgroup.centralizer ((M.subgroupOf N : Subgroup N) : Set N) = ⊥ := by
    rw [← le_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    have hxY : (x : Y) ∈ Subgroup.centralizer (M : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Subgroup.mem_centralizer_iff] at hx
      exact congrArg Subtype.val (hx ⟨(y : Y), hMleN hy⟩ hy)
    rw [hCen, Subgroup.mem_bot] at hxY
    exact hxY
  have hradN : ∀ P : Subgroup N, P.Normal → Group.IsSolvable P → P = ⊥ :=
    solvable_normal_eq_bot_of_le hMleN hMsimple hCen hMmin.2.1
  have hnsN : ¬ ∃ a ∈ conjSet M d, ∃ b ∈ conjSet M d,
      a ≠ b ∧ Commute a b ∧ a * b ∈ conjSet M d := by
    rintro ⟨a, ha, b, hb, hne, hcomm, hab⟩
    exact hns ⟨(a : Y), hmemΛ ha, (b : Y), hmemΛ hb, fun h => hne (Subtype.ext h),
      hcomm.map N.subtype, by simpa using hmemΛ hab⟩
  have hconnN : ¬ Disconnected (conjSet M d) := by
    intro hdiscN
    obtain ⟨H, hHtop, ⟨x, hx, hxH⟩, hHC⟩ := exists_subgroup_of_disconnected hSN hdiscN
    have hConcl := theoremOne N (conjSet M d) hSN.isClass hSN.oddT.1 hSN.oddT.2 hSN.gen hradN
      ⟨H, hHtop, ⟨x, hx, hxH⟩, hHC⟩
    rcases hConcl with hB | ⟨f, n, hf, hn, ⟨φ⟩⟩ | hAS'
    · obtain ⟨u, hu, v, hv, hne, hcomm, huv⟩ :=
        CFSG.OddTranspositions.bender_meetsSq hB hSN.isClass hSN.oddT.1
      exact hnsN ⟨u, hu, v, hv, hne, hcomm, huv⟩
    · have h128N : 128 ∣ Nat.card N := by
        rw [Nat.card_congr φ.toEquiv]
        exact dvd_card_l2Wreath hf hn
      exact h128 (h128N.trans (Subgroup.card_subgroup_dvd_card N))
    · obtain ⟨M', -, hM'min, hM'uniq, -, -, hM'idx, -, -⟩ := hAS'
      have hEq : M.subgroupOf N = M' := hM'uniq _ hMminN
      rw [← hEq] at hM'idx
      exact absurd hM'idx (not_lt.mpr hrelIndex_le)
  have hL' : LocalTwoA5 (conjSet M d) dN := by
    refine LocalTwoA5.of_injective (d := dN) N.subtype N.subtype_injective ?_ hL
    ext e
    constructor
    · rintro ⟨e', he', rfl⟩
      exact ⟨hmemΛ he'.1, he'.2.1.map N.subtype, fun h => he'.2.2 (Subtype.ext h)⟩
    · intro he
      have hdeM : d * e ∈ M := by
        have hne : ∀ x ∈ Λ, QuotientGroup.mk' M x ≠ 1 := by
          intro x hx hx1
          have hxM : x ∈ M := (QuotientGroup.eq_one_iff x).mp hx1
          have hle : Λ ⊆ M := by
            intro y hy
            obtain ⟨g, rfl⟩ := isConj_iff.mp (hS.isConj hx hy)
            exact hMnorm.conj_mem x hxM g
          have htop : M = ⊤ := by
            rw [eq_top_iff, ← hS.gen]
            exact (Subgroup.closure_le M).mpr hle
          rw [htop, Subgroup.index_top] at hidx
          omega
        have hSQ : Setup (Y ⧸ M) (QuotientGroup.mk' M '' Λ) :=
          hS.map (QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M) hne
        have hcommQ : Commute (QuotientGroup.mk' M d) (QuotientGroup.mk' M e) :=
          (he.2.1.map (QuotientGroup.mk' M)).symm
        have heq : QuotientGroup.mk' M d = QuotientGroup.mk' M e :=
          eq_of_commute_of_widthOne hSQ hW ⟨d, hd, rfl⟩ ⟨e, he.1, rfl⟩ hcommQ
        have h1 : QuotientGroup.mk' M (d * e) = 1 := by
          rw [map_mul, ← heq, ← map_mul, hS.oddT.mul_self_eq_one hd, map_one]
        exact (QuotientGroup.eq_one_iff (d * e)).mp h1
      obtain ⟨m, hm, hme⟩ :=
        exists_conj_of_mul_mem hS M hCen hclass' hd he.1 hdeM
      have heN : e ∈ N := by
        rw [← hme]
        exact N.mul_mem (N.mul_mem (hMleN hm) hdN) (N.inv_mem (hMleN hm))
      refine ⟨⟨e, heN⟩, ⟨⟨m, hm, hme.symm⟩, ?_, fun h => he.2.2 (congrArg Subtype.val h)⟩, rfl⟩
      apply Subtype.ext
      exact he.2.1.eq
  have hdmem : dN ∈ conjSet M d := ⟨1, M.one_mem, by simp [dN]⟩
  obtain ⟨hC₁, -, -, hrad_eq, hbender⟩ :=
    exists_hypC_of_localTwoA5 hSN hconnN hdmem hL'
  obtain ⟨f, hf, -, h22 | h2⟩ := h91 N (conjSet M d) hC₁ hradN hrad_eq hbender
  ·
    obtain ⟨φ⟩ := h22
    have hsimpleMsub : IsSimpleGroup (M.subgroupOf N) :=
      (Subgroup.subgroupOfEquivOfLe hMleN).isSimpleGroup
    exact not_isSimpleGroup_of_index_le_two_l2Wreath hf φ (M.subgroupOf N) inferInstance
      hrelIndex_le hsimpleMsub
  ·
    obtain ⟨⟨ψ⟩, hCidx⟩ := h2
    have hsub_le_C : M.subgroupOf N ≤ commutator N := by
      by_contra hnot
      have hlt : M.subgroupOf N ⊓ commutator N = ⊥ := by
        rcases hMminN.2.2 (M.subgroupOf N ⊓ commutator N) inferInstance inf_le_left with
          h | h
        · exact h
        · exact absurd (inf_eq_left.mp h) hnot
      have hcomm_le : ⁅M.subgroupOf N, M.subgroupOf N⁆ ≤ M.subgroupOf N ⊓ commutator N := by
        refine le_inf ?_ ?_
        · simpa using Subgroup.commutator_le_inf (M.subgroupOf N) (M.subgroupOf N)
        · have hmono := Subgroup.commutator_mono
            (show M.subgroupOf N ≤ (⊤ : Subgroup N) from le_top)
            (show M.subgroupOf N ≤ (⊤ : Subgroup N) from le_top)
          exact hmono
      rw [hlt, le_bot_iff] at hcomm_le
      have hle_central : M.subgroupOf N ≤ Subgroup.centralizer (M.subgroupOf N : Set N) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm_le
      rw [hCenN, le_bot_iff] at hle_central
      exact hMminN.2.1 hle_central
    have hMsub_eq_C : M.subgroupOf N = commutator N := by
      have hrel := Subgroup.relIndex_mul_index hsub_le_C
      rw [hCidx] at hrel
      have hne : (M.subgroupOf N).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have hrel1 : (M.subgroupOf N).relIndex (commutator N) = 1 := by
        have hpos : 0 < (M.subgroupOf N).relIndex (commutator N) := Nat.pos_of_ne_zero fun h0 => by
          rw [h0, zero_mul] at hrel
          exact hne hrel.symm
        omega
      exact le_antisymm hsub_le_C (Subgroup.relIndex_eq_one.mp hrel1)
    have hMsub_iso : Nonempty (M.subgroupOf N ≃* CFSG.Theory.Comparator.PSL2Model (2 * f)) :=
      hMsub_eq_C ▸ ⟨ψ⟩
    have hMiso : Nonempty (M ≃* CFSG.Theory.Comparator.PSL2Model (2 * f)) :=
      ⟨(Subgroup.subgroupOfEquivOfLe hMleN).symm.trans hMsub_iso.some⟩
    have hcomm_le_M : commutator Y ≤ M := by
      obtain ⟨eM⟩ := hMiso
      have h := CFSG.GH72.commutator_le_sup_centralizer_of_outer_mul_comm M
        (CFSG.GH72.outer_mul_comm_of_mulEquiv_psl2 (F := GaloisField 2 (2 * f)) eM)
      simpa [hCen] using h
    have hindex_le : M.index ≤ 2 := by
      have hdvd : M.index ∣ 2 := by
        rw [Subgroup.index_dvd_two_iff]
        refine ⟨d, fun b => ?_⟩
        let π : Y →* Y ⧸ M := QuotientGroup.mk' M
        have hcomm_quot : ∀ a b : Y, Commute (π a) (π b) := by
          have hbot : commutator (Y ⧸ M) = ⊥ := by
            have hmap := Subgroup.map_commutator (H₁ := (⊤ : Subgroup Y))
              (H₂ := (⊤ : Subgroup Y)) π
            rw [Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective M)] at hmap
            change ⁅(⊤ : Subgroup (Y ⧸ M)), ⊤⁆ = ⊥
            rw [← hmap]
            exact (Subgroup.map_eq_bot_iff (commutator Y) (f := π)).mpr
              (by rw [QuotientGroup.ker_mk']; exact hcomm_le_M)
          haveI hcommQ : IsMulCommutative (Y ⧸ M) :=
            (commutator_eq_bot_iff (Y ⧸ M)).mp hbot
          intro a b
          exact hcommQ.is_comm.comm (π a) (π b)
        have himg : π '' Λ = {π d} := by
          ext x
          constructor
          · rintro ⟨y, hy, rfl⟩
            obtain ⟨g, rfl⟩ := isConj_iff.mp (hS.isConj hd hy)
            rw [map_mul, map_mul, map_inv, (hcomm_quot g d).eq, mul_assoc, mul_inv_cancel,
              mul_one]
            rfl
          · intro hx
            rw [Set.mem_singleton_iff] at hx
            exact ⟨d, hd, hx.symm⟩
        have hgen : Subgroup.closure ({π d} : Set (Y ⧸ M)) = ⊤ := by
          rw [← himg, ← MonoidHom.map_closure, hS.gen, ← MonoidHom.range_eq_map]
          exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective M)
        have hd2q : π d * π d = 1 := by rw [← map_mul, hd2, map_one]
        have htwo : ∀ x : Y ⧸ M, x = 1 ∨ x = π d := by
          intro x
          have hx : x ∈ Subgroup.zpowers (π d) := by
            rw [Subgroup.zpowers_eq_closure, hgen]
            exact Subgroup.mem_top x
          by_cases h1 : π d = 1
          · left
            rw [h1, Subgroup.zpowers_one_eq_bot] at hx
            exact Subgroup.mem_bot.mp hx
          · exact (Subgroup.mem_zpowers_iff_of_orderOf_eq_two
              (orderOf_eq_prime (by rw [pow_two]; exact hd2q) h1)).mp hx
        rcases htwo (π b) with h | h
        · right
          exact (QuotientGroup.eq_one_iff b).mp h
        · left
          have h1 : π (b * d) = 1 := by rw [map_mul, h, hd2q]
          exact (QuotientGroup.eq_one_iff (b * d)).mp h1
      exact Nat.le_of_dvd (by norm_num) hdvd
    exact absurd hidx (not_lt.mpr hindex_le)

theorem not_disconnected_of_localTwoA5 (h91 : Theorem9_1)
    {Y : Type} [Group Y] [Finite Y] {Λ : Set Y} (hS : Setup Y Λ)
    (hrad : ∀ N : Subgroup Y, N.Normal → Group.IsSolvable N → N = ⊥)
    (hns : ¬ ∃ a ∈ Λ, ∃ b ∈ Λ, a ≠ b ∧ Commute a b ∧ a * b ∈ Λ)
    (h128 : ¬ 128 ∣ Nat.card Y) {d : Y} (hd : d ∈ Λ) (hL : LocalTwoA5 Λ d) :
    ¬ Disconnected Λ := by
  intro hdisc
  obtain ⟨H, hHtop, ⟨x, hx, hxH⟩, hHC⟩ := exists_subgroup_of_disconnected hS hdisc
  have hConcl := theoremOne Y Λ hS.isClass hS.oddT.1 hS.oddT.2 hS.gen hrad
    ⟨H, hHtop, ⟨x, hx, hxH⟩, hHC⟩
  rcases hConcl with hB | ⟨f, n, hf, hn, ⟨φ⟩⟩ | hAS
  · obtain ⟨u, hu, v, hv, hne, hcomm, huv⟩ :=
      CFSG.OddTranspositions.bender_meetsSq hB hS.isClass hS.oddT.1
    exact hns ⟨u, hu, v, hv, hne, hcomm, huv⟩
  · have h128Y : 128 ∣ Nat.card Y := by
      rw [Nat.card_congr φ.toEquiv]
      exact dvd_card_l2Wreath hf hn
    exact h128 h128Y
  · exact not_almostSimpleCase_of_localTwoA5 h91 hS hns h128 hd hL hAS

end Conn

end CFSG.OddTranspositions.PartThree

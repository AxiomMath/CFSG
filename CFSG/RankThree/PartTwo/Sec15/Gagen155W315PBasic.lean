module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155W315xFacts
import CFSG.GroupTheory.PRankCommutingPerfect
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec18.Transport

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Proof155P

theorem pRank_five_le_two {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {S M : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining (S : Set G)) : CFSG.Open.pRank 5 M ≤ 2 := by
  have hlt : CFSG.Open.rankThreeLocalRank 5 G < 3 :=
    h.toTheoremFourHyp.localRank_lt 5 (by norm_num) (by norm_num)
  have hle := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_localRank 5 (by norm_num) M
    hM.1.1
  omega

theorem commutator_w155_le {A X Y M P : Subgroup G} (hf : Proof155Wx.Facts155W A X Y M P)
    (hX : X ∈ thetaComponentsIn M) : ⁅w155 A M X, X⁆ ≤ CFSG.Open.pCoreOf 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXM : X ≤ M := (mem_thetaComponentsIn_iff.mp hX).1
  have hXsn : (X.subgroupOf M).IsSubnormal := (mem_thetaComponentsIn_iff.mp hX).2.2.1
  have hpCX : CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 M := by
    have h1 := Late.pCoreOf_le_pCore_of_isSubnormal (K := M) 2 hXsn
    have h2 := Subgroup.map_mono (f := M.subtype) h1
    rw [← CFSG.RankThree.PartTwo.Sec18.pCoreOf_map M.subtype M.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hXM] at h2
    exact h2
  refine Subgroup.commutator_le.mpr ?_
  intro w hw x hx
  have hwU : w ∈ u155 A M X := Proof155Wx.w155_le_u155 A M X hw
  have hc : ⁅x, w⁆ ∈ CFSG.Open.pCoreOf 2 X := hwU.2.2.2 x hx
  rw [← commutatorElement_inv x w]
  exact (CFSG.Open.pCoreOf 2 M).inv_mem (hpCX hc)

theorem pRank_five_w155_le_one {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {X Y M P : Subgroup G} (hf : Proof155Wx.Facts155W A X Y M P) (hX : X ∈ thetaComponentsIn M)
    (h5 : 5 ∣ Nat.card X) : CFSG.Open.pRank 5 (w155 A M X) ≤ 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hXM : X ≤ M := (mem_thetaComponentsIn_iff.mp hX).1
  have hWM : w155 A M X ≤ M :=
    (hf.w_le_i0.trans (Sec14.oPrimeResidualOf_le_self 3 _)).trans (Sec14.delta_le M)
  have hperfX : Group.IsPerfect ↥X := by
    haveI : Group.IsPerfect ↥(X.subgroupOf M) := (mem_thetaComponentsIn_iff.mp hX).2.1
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hXM).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hXM).surjective
  have hle := CFSG.GroupTheory.pRank_add_one_le_of_commutator_le_pCoreOf (q := 5) (by norm_num)
    hWM hXM (commutator_w155_le hf hX) (Subgroup.isPerfect_iff.mp hperfX) h5
  have hM := pRank_five_le_two h hf.mem_mx
  omega

theorem pRank_five_x_le_one {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {X Y M P : Subgroup G} (hf : Proof155Wx.Facts155W A X Y M P) (hX : X ∈ thetaComponentsIn M)
    (h5 : 5 ∣ Nat.card (w155 A M X)) : CFSG.Open.pRank 5 X ≤ 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hXM : X ≤ M := (mem_thetaComponentsIn_iff.mp hX).1
  have hWM : w155 A M X ≤ M :=
    (hf.w_le_i0.trans (Sec14.oPrimeResidualOf_le_self 3 _)).trans (Sec14.delta_le M)
  have hcomm : ⁅X, w155 A M X⁆ ≤ CFSG.Open.pCoreOf 2 M := by
    rw [Subgroup.commutator_comm]
    exact commutator_w155_le hf hX
  have hle := CFSG.GroupTheory.pRank_add_one_le_of_commutator_le_pCoreOf (q := 5) (by norm_num)
    hXM hWM hcomm (Subgroup.isPerfect_iff.mp (Proof155Wx.isPerfect_w155 A M X)) h5
  have hM := pRank_five_le_two h hf.mem_mx
  omega

theorem inSubgroup_theta_le_pPrimeCoreOf {W M : Subgroup G} (hW : CFSG.Open.IsSubnormal W M) :
    inSubgroup (aschbacherSolvableCore 3) W ≤ pPrimeCoreOf 3 M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  induction hW with
  | refl H =>
    have hfacts := map_aschbacherSolvableCore_facts H
    refine Sec14.le_pPrimeCoreOf (Subgroup.map_subtype_le _) hfacts.1 ?_
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hfacts.2.2
  | @step H M K hHM hn hMK ih =>
    have hmono : CFSG.RankThreeEvenClassification.Helpers.thetaCoreOf 3 H ≤
        CFSG.RankThreeEvenClassification.Helpers.thetaCoreOf 3 M :=
      CFSG.RankThreeEvenClassification.Helpers.thetaCoreOf_mono_of_normal 3 Nat.prime_three
        H M hHM hn
    rw [inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf Nat.prime_three H,
      inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf Nat.prime_three M] at *
    exact hmono.trans ih

theorem inf_pPrimeCoreOf_facts {W M : Subgroup G} (hWM : W ≤ M) :
    ((W ⊓ pPrimeCoreOf 3 M).subgroupOf W).Normal ∧ ¬ 3 ∣ Nat.card ↥(W ⊓ pPrimeCoreOf 3 M) ∧
      (W ⊓ pPrimeCoreOf 3 M).subgroupOf W = (pPrimeCoreOf 3 M).subgroupOf W := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨?_, ?_, Subgroup.inf_subgroupOf_left (pPrimeCoreOf 3 M) W⟩
  · refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr ?_
    exact Subgroup.le_normalizer_inf (A := W) (H := W) (K := pPrimeCoreOf 3 M)
      Subgroup.le_normalizer (hWM.trans (Sec14.le_normalizer_pPrimeCoreOf 3 M))
  · have h3O : ¬ 3 ∣ Nat.card ↥(pPrimeCoreOf 3 M) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (Sec14.coprime_card_pPrimeCoreOf 3 M)
    exact fun h3 => h3O (h3.trans (Subgroup.card_dvd_of_le inf_le_right))

end Proof155P

end CFSG.RankThree.PartTwo.Sec15

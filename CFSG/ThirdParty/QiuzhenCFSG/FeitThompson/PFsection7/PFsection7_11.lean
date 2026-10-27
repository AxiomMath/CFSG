module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_5_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_10
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.Basic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.Section7

universe v
universe u

@[expose] public def theorem_7_11_statement
    {G : Type u} [Group G] [Finite G]
    {I : Type*} [Fintype I]
    (L H : I → Subgroup G) : Prop :=
  theorem_7_10_source_hypothesis L H ({1} : Set G) →
    theorem_7_10_lowerBoundData L H ({1} : Set G) →
      False



private theorem theorem_7_11_bound_pos_of_two_mul_le {h e : ℕ}
    (hh : 0 < h) (he : 1 < e) (hle : 2 * e ≤ h - 1) :
    0 < ((e : ℝ) - 1) *
      (((h : ℝ) - 2 * (e : ℝ) - 1) / ((e : ℝ) * (h : ℝ)) +
        2 / ((h : ℝ) * ((h : ℝ) + 2))) := by
  have he0_nat : 0 < e := lt_trans Nat.zero_lt_one he
  have he0 : 0 < (e : ℝ) := by exact_mod_cast he0_nat
  have hh0 : 0 < (h : ℝ) := by exact_mod_cast hh
  have he_minus : 0 < (e : ℝ) - 1 := by
    exact sub_pos.mpr (by exact_mod_cast he)
  have hden1 : 0 < (e : ℝ) * (h : ℝ) := mul_pos he0 hh0
  have hnum_nonneg : 0 ≤ (h : ℝ) - 2 * (e : ℝ) - 1 := by
    have hle' : (2 * e : ℝ) ≤ (h - 1 : ℕ) := by exact_mod_cast hle
    have hh1 : 1 ≤ h := Nat.succ_le_of_lt hh
    rw [Nat.cast_sub hh1] at hle'
    norm_num at hle'
    nlinarith
  have hterm1_nonneg :
      0 ≤ ((h : ℝ) - 2 * (e : ℝ) - 1) / ((e : ℝ) * (h : ℝ)) :=
    div_nonneg hnum_nonneg (le_of_lt hden1)
  have hterm2_pos : 0 < 2 / ((h : ℝ) * ((h : ℝ) + 2)) := by
    positivity
  have hsum_pos :
      0 < ((h : ℝ) - 2 * (e : ℝ) - 1) / ((e : ℝ) * (h : ℝ)) +
        2 / ((h : ℝ) * ((h : ℝ) + 2)) :=
    add_pos_of_nonneg_of_pos hterm1_nonneg hterm2_pos
  exact mul_pos he_minus hsum_pos

private theorem theorem_7_11_one_lt_relIndex_of_frobenius
    {G : Type u} [Group G] [Finite G] {L H : Subgroup G}
    (hfrob : frobeniusWithKernel L H) :
    1 < H.relIndex L := by
  rcases hfrob with ⟨_hHL, hHnorm, R, hcomp, _hHne, hRne, _hfixed⟩
  haveI : (H.subgroupOf L).Normal := hHnorm
  have hindex : (H.subgroupOf L).index = Nat.card R :=
    hcomp.symm.index_eq_card
  have hRcard : 1 < Nat.card R :=
    (Subgroup.one_lt_card_iff_ne_bot R).2 hRne
  rw [Subgroup.relIndex, hindex]
  exact hRcard

public theorem theorem_7_11_two_mul_relIndex_le_card_sub_one
    {G : Type u} [Group G] [Finite G] {L H : Subgroup G}
    (hodd : Odd (Nat.card G)) (hfrob : frobeniusWithKernel L H) :
    2 * H.relIndex L ≤ Nat.card H - 1 := by
  rcases hfrob with ⟨hHL, hHnorm, R, hcomp, hHne, _hRne, hcent⟩
  haveI : (H.subgroupOf L).Normal := hHnorm
  have hindex : H.relIndex L = Nat.card R := by
    rw [Subgroup.relIndex, hcomp.symm.index_eq_card]
  have hHsubcard : Nat.card (H.subgroupOf L) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv
  have hdvdSub : Nat.card R ∣ Nat.card (H.subgroupOf L) - 1 :=
    Section6.frobeniusComplement_card_dvd_normal_subgroup_card_sub_one
      (Q := L) (K := H.subgroupOf L) (R := R) (N := H.subgroupOf L)
      le_rfl hcent
  have hdvd : Nat.card R ∣ Nat.card H - 1 := by
    simpa [hHsubcard] using hdvdSub
  have hHodd : Odd (Nat.card H) :=
    Odd.of_dvd_nat hodd (Subgroup.card_subgroup_dvd_card H)
  have hRodd : Odd (Nat.card R) := by
    exact Odd.of_dvd_nat hodd
      (Nat.dvd_trans (Subgroup.card_subgroup_dvd_card R)
        (Subgroup.card_subgroup_dvd_card L))
  have hHsub_gt : 1 < Nat.card (H.subgroupOf L) :=
    (Subgroup.one_lt_card_iff_ne_bot (H.subgroupOf L)).2 hHne
  have hHgt : 1 < Nat.card H := by
    simpa [hHsubcard] using hHsub_gt
  rcases hdvd with ⟨k, hk⟩
  have hHminus_pos : 0 < Nat.card H - 1 := Nat.sub_pos_of_lt hHgt
  have hkpos : 0 < k := by
    by_contra hnot
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hnot
    have hzero : Nat.card H - 1 = 0 := by
      simpa [hk0] using hk
    exact (Nat.ne_of_gt hHminus_pos) hzero
  have hk_ne_one : k ≠ 1 := by
    intro hk1
    rcases hHodd with ⟨m, hm⟩
    rcases hRodd with ⟨n, hn⟩
    subst k
    omega
  have hk_ge_two : 2 ≤ k := by omega
  have hleR : 2 * Nat.card R ≤ Nat.card R * k := by
    calc
      2 * Nat.card R = Nat.card R * 2 := by rw [Nat.mul_comm]
      _ ≤ Nat.card R * k := Nat.mul_le_mul_left (Nat.card R) hk_ge_two
  rw [hindex]
  exact hleR.trans_eq hk.symm

public theorem theorem_7_11
    {G : Type u} [Group G] [Finite G]
    {I : Type*} [Fintype I]
    (L H : I → Subgroup G) :
    theorem_7_11_statement L H := by
  rw [theorem_7_11_statement]
  intro hsource hboundData
  rcases theorem_7_10 L H ({1} : Set G) hsource hboundData with ⟨i, hi⟩
  dsimp at hi
  simp at hi
  have hodd : Odd (Nat.card G) := hsource.1
  have hfrob : frobeniusWithKernel (L i) (H i) := hsource.2.2.1 i
  have hpos := theorem_7_11_bound_pos_of_two_mul_le
    (h := Nat.card (H i)) (e := (H i).relIndex (L i))
    (Nat.card_pos (α := H i))
    (theorem_7_11_one_lt_relIndex_of_frobenius hfrob)
    (theorem_7_11_two_mul_relIndex_le_card_sub_one hodd hfrob)
  nlinarith

end CFSG.Section7

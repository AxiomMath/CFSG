module

public import CFSG.RankThree.GF2n.Stroth78.Sec3OddInvariant

import CFSG.ClassicalGroups.PCoreSection
import CFSG.LocalAnalysis.RankThreeUC.Section5.OpenPCoreEq
import CFSG.RankThree.GF2n.Stroth78.Sec2Five
import CFSG.RankThree.GF2n.Stroth78.Sec2Six
import CFSG.RankThree.GF2n.Stroth78.Sec3OddCore
import CFSG.RankThree.GF2n.Stroth78.Sec3One

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.ClassicalGroups.PCoreSection CFSG.RankThree.GF2n.Tim79a
open CFSG.LargeExtraspecial.Timmesfeld
open CFSG.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem pCoreOf_Xsub_le_centerIn (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    pCoreOf p (Xsub S a) ≤ centerIn (Xsub S a) := by
  let R : Subgroup (Hbar z) := pCoreOf p (Xsub S a)
  have hRn : R.Normal := pCoreOf_Xsub_normal S a p
  haveI : R.Normal := hRn
  have hOdd : Odd (Nat.card R) := by
    letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := (isPGroup_pCoreOf p (Xsub S a)).exists_card_eq
    rw [hk]
    exact Odd.pow (hp.odd_of_ne_two hp2)
  have hLR : Lbar S a ≤ Subgroup.normalizer (R : Set (Hbar z)) := by
    rw [Subgroup.normalizer_eq_top R]
    exact le_top
  obtain ⟨r, hrR, hr1⟩ :=
    (Subgroup.bot_or_exists_ne_one (Rbar S a)).resolve_left h.Rbar_ne_bot
  have hrE : r ∈ Eset S a :=
    Tset_subset_Eset S a (h.mem_Tset_of_mem_Rbar hrR hr1)
  have hcent : R ≤ Subgroup.centralizer (Xsub S a : Set (Hbar z)) := by
    refine Subgroup.le_centralizer_iff.mpr ?_
    rw [Xsub, Subgroup.closure_le]
    intro α hα
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    obtain ⟨x, hx, hαeq⟩ := ((stroth78_31 S h h217).2.2.2 r hrE α).mp hα
    have hy' : x⁻¹ * y * x ∈ R := by
      have hconj := hRn.conj_mem y hy x⁻¹
      simpa using hconj
    have hcomm : r * (x⁻¹ * y * x) = (x⁻¹ * y * x) * r :=
      commute_of_mem_Rbar_of_odd S h hOdd hLR hrR hy'
    refine (calc α * y = (x * r * x⁻¹) * y := by rw [hαeq]
      _ = x * (r * (x⁻¹ * y * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * y * x) * r) * x⁻¹ := by rw [hcomm]
      _ = y * (x * r * x⁻¹) := by group
      _ = y * α := by rw [hαeq]).symm
  exact le_inf (pCoreOf_le p (Xsub S a)) hcent

theorem card_centerIn_Xsub (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥) :
    Nat.card (centerIn (Xsub S a)) = 1 ∨ Nat.card (centerIn (Xsub S a)) = 3 := by
  let Z : Subgroup (Hbar z) := centerIn (Xsub S a)
  have hXn : (Xsub S a).Normal := Xsub_normal S a
  have hCn : (Subgroup.centralizer (Xsub S a : Set (Hbar z))).Normal :=
    Subgroup.normal_centralizer
  have hZn : Z.Normal := by
    haveI : (Xsub S a).Normal := hXn
    haveI : (Subgroup.centralizer (Xsub S a : Set (Hbar z))).Normal := hCn
    change (Xsub S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z))).Normal
    exact Subgroup.normal_inf_normal _ _
  haveI : Z.Normal := hZn
  have hZc : IsMulCommutative ↥Z := ⟨⟨fun x y => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact Subgroup.mem_centralizer_iff.mp y.2.2 x.val
      ((inf_le_left : Z ≤ Xsub S a) x.2))⟩⟩
  haveI : IsMulCommutative ↥Z := hZc
  haveI : Group.IsNilpotent ↥Z := inferInstance
  have hZodd : Odd (Nat.card Z) :=
    CFSG.LocalAnalysis.RankThreeUC.Section5.OddActorSylowFactorization.odd_of_pCore_bot
      (pCore_two_Hbar_eq_bot S) Z
  have hLZ : Lbar S a ≤ Subgroup.normalizer (Z : Set (Hbar z)) := by
    rw [Subgroup.normalizer_eq_top Z]
    exact le_top
  have hle3 : Nat.card Z ≤ 3 := card_le_three_of_odd S h h217 hZodd hLZ
  obtain ⟨k, hk⟩ := hZodd
  have hk01 : k = 0 ∨ k = 1 := by omega
  rcases hk01 with rfl | rfl
  · left; omega
  · right; omega

theorem stroth78_32 (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥) :
    (∀ p : ℕ, p.Prime → p ≠ 2 → pCoreOf p (Xsub S a) ≤ centerIn (Xsub S a)) ∧
      (Nat.card (centerIn (Xsub S a)) = 1 ∨ Nat.card (centerIn (Xsub S a)) = 3) :=
  ⟨fun p hp hp2 => pCoreOf_Xsub_le_centerIn S h h217 hp hp2,
    card_centerIn_Xsub S h h217⟩

end CFSG.RankThree.GF2n.Stroth78

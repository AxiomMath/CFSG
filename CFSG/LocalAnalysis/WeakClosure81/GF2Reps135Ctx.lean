module

import CFSG.GroupTheory.SylowIntersectionControl.GomiGstar
import CFSG.ClassicalInvolution.SubnormalClosure
import CFSG.GroupTheory.E3Params
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

variable {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)} {t : MulAut W}

omit [Finite W] in
theorem w135_normal_of_ctx (hctx : Is135Context Y L) : (L.subgroupOf Y).Normal := by
  obtain ⟨-, -, -, hF, -, -⟩ := hctx
  have hsub : L.subgroupOf Y = genFittingFStar ↥Y := by
    rw [← hF, Fstar]
    exact Subgroup.comap_map_eq_self_of_injective (f := Y.subtype) Y.subtype_injective _
  rw [hsub]
  exact CFSG.ClassicalInvolution.genFittingFStar_normal ↥Y

theorem w135_o2Trivial_of_ctx (hctx : Is135Context Y L) : O2Trivial L := by
  have hO2 : O2Trivial Y := hctx.2.1
  have hLY : L ≤ Y := hctx.2.2.1
  exact CFSG.GroupTheory.o2Trivial_of_normal hO2 hLY (w135_normal_of_ctx hctx)

theorem w135_odd_card_center (hctx : Is135Context Y L) :
    Odd (Nat.card (Subgroup.center ↥L)) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  have hdvd : 2 ∣ Nat.card (Subgroup.center ↥L) := even_iff_two_dvd.mp hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ :=
    exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥L) 2 hdvd
  set z : ↥L := (x : ↥L) with hz
  have hz2 : orderOf z = 2 := by rw [hz, Subgroup.orderOf_coe, hx]
  have hzc : Subgroup.zpowers z ≤ Subgroup.center ↥L := Subgroup.zpowers_le.mpr x.2
  have hn : (Subgroup.zpowers z).Normal := Subgroup.normal_of_le_center hzc
  set P : Subgroup (MulAut W) := (Subgroup.zpowers z).map L.subtype with hP
  have hPnorm : (P.subgroupOf L).Normal := by
    have hPsub : P.subgroupOf L = Subgroup.zpowers z := by
      rw [hP]
      exact Subgroup.comap_map_eq_self_of_injective (f := L.subtype) L.subtype_injective _
    rw [hPsub]
    exact hn
  have hP2 : IsPGroup 2 P := by
    have hp : IsPGroup 2 (Subgroup.zpowers z) := by
      rw [IsPGroup.iff_card, Nat.card_zpowers, hz2]
      exact ⟨1, by norm_num⟩
    rw [hP]
    exact hp.map L.subtype
  have hbot : P = ⊥ :=
    w135_o2Trivial_of_ctx hctx P (Subgroup.map_subtype_le _) hPnorm hP2
  have hnil : L.subtype z ∈ P := ⟨z, Subgroup.mem_zpowers z, rfl⟩
  rw [hbot] at hnil
  have hz1 : z = 1 := L.subtype_injective (by simpa using hnil)
  rw [hz1, orderOf_one] at hz2
  norm_num at hz2

theorem w135_mParam_le_three (htY : t ∈ Y) (ht2 : orderOf t = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) : E3.mParam Y ≤ 3 := by
  have hdvd : 2 ∣ Nat.card ↥Y := by
    have h := orderOf_dvd_natCard (⟨t, htY⟩ : ↥Y)
    rwa [Subgroup.orderOf_mk, ht2] at h
  have heven : Even (Nat.card ↥Y) := even_iff_two_dvd.mpr hdvd
  rw [E3.mParam, if_pos heven]
  have h3 : rkIdx (fixV (Subgroup.zpowers t)) ≤ 3 := by
    rwa [CFSG.GroupTheory.mQuot_top_eq_rkIdx] at hm
  exact (Nat.sInf_le (s := {n : ℕ | ∃ s ∈ Y, orderOf s = 2 ∧
    n = rkIdx (fixV (Subgroup.zpowers s))}) ⟨t, htY, ht2, rfl⟩).trans h3

theorem w135_card_eq_two_pow_rk (hW : ∀ w : W, w ^ 2 = 1) : Nat.card W = 2 ^ rk W := by
  have hP : IsPGroup 2 W := fun w => ⟨1, by simpa using hW w⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hP
  have hrk : rk W = n := by
    unfold rk
    rw [hn]
    exact padicValNat.prime_pow n
  rw [hn, hrk]

theorem w135_commSub_top_eq_top (hctx : Is135Context Y L) :
    commSub (⊤ : Subgroup W) L = ⊤ := by
  obtain ⟨-, -, -, -, hQ, hIrr⟩ := hctx
  have hstab : StableUnder L (commSub (⊤ : Subgroup W) L) :=
    stableUnder_commSub (H := L) (X := L)
      (fun h hh x hx => L.mul_mem (L.mul_mem hh hx) (L.inv_mem hh))
      (fun _ _ _ _ => Subgroup.mem_top _)
  rcases hIrr.2.2.2 _ hstab bot_le le_top with hbot | htop
  · exfalso
    have hfix : (⊤ : Subgroup W) ≤ fixV L := commSub_eq_bot_iff.mp hbot
    have hLbot : L = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      ext w
      exact mem_fixV.mp (hfix (Subgroup.mem_top w)) x hx
    obtain ⟨a, b, hab⟩ := hQ.2.2
    have : Subsingleton ↥L :=
      ⟨fun x y => by
        have hx : (x : MulAut W) = 1 :=
          (Subgroup.eq_bot_iff_forall (H := L)).mp hLbot x x.2
        have hy : (y : MulAut W) = 1 :=
          (Subgroup.eq_bot_iff_forall (H := L)).mp hLbot y y.2
        exact Subtype.ext (hx.trans hy.symm)⟩
    have : Subsingleton (↥L ⧸ Subgroup.center ↥L) := inferInstance
    exact hab (Subsingleton.elim (a * b) (b * a))
  · exact htop

end CFSG.LocalAnalysis.WeakClosure81

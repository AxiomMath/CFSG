module

import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuGlauberman
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinLinearModel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallOuter
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Finset
open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped commutatorElement

private theorem w135c2_psu_outer_not_commute {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (hctx : Is135Context Y L) (htY : t ∈ Y)
    (ht2 : orderOf t = 2) : ∃ x ∈ L, t * x ≠ x * t := by
  classical
  by_contra hcon
  have hcomm : ∀ l ∈ L, t * l = l * t := by
    intro l hl
    by_contra hne
    exact (hcon ⟨l, hl, hne⟩).elim
  have hmem : ∀ l ∈ L, ⁅t, l⁆ ∈ Zc L := by
    intro l hl
    have h1 : ⁅t, l⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hcomm l hl)
    rw [h1]
    exact (Zc L).one_mem
  exact w135c2_not_mem_Zc_of_order_two hctx ht2 (w135c2_mem_Zc_of_comm hctx htY hmem)

private theorem w135c2_odd_normal_le_center {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} (hQ : IsQuasisimple ↥L) :
    ∀ N : Subgroup ↥L, N.Normal → Odd (Nat.card N) → N ≤ Subgroup.center ↥L := by
  intro N hN hodd
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hQ.2.1
  have hNmap : (N.map (QuotientGroup.mk' (Subgroup.center ↥L))).Normal :=
    hN.map (QuotientGroup.mk' (Subgroup.center ↥L))
      (QuotientGroup.mk'_surjective (Subgroup.center ↥L))
  have hoddmap : Odd (Nat.card ↥(N.map (QuotientGroup.mk' (Subgroup.center ↥L)))) :=
    hodd.of_dvd_nat (Subgroup.card_map_dvd (H := N) (QuotientGroup.mk' (Subgroup.center ↥L)))
  rcases hNmap.eq_bot_or_eq_top with hbot | htop
  · have hle : N ≤ (QuotientGroup.mk' (Subgroup.center ↥L)).ker :=
      (Subgroup.map_eq_bot_iff N).mp hbot
    rwa [QuotientGroup.ker_mk'] at hle
  · exfalso
    have hoddq : Odd (Nat.card (↥L ⧸ Subgroup.center ↥L)) := by
      rw [htop, Subgroup.card_top] at hoddmap
      exact hoddmap
    have hsolv : Group.IsSolvable (↥L ⧸ Subgroup.center ↥L) :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ hoddq
    have hcomm : ∀ a b : ↥L ⧸ Subgroup.center ↥L, a * b = b * a :=
      IsSimpleGroup.comm_iff_isSolvable.mpr hsolv
    obtain ⟨a, b, hab⟩ := hQ.2.2
    exact hab (hcomm a b)

private theorem w135c2_mQuot_le_two_mul {W : Type} [CommGroup W] [Finite W]
    (hW2 : ∀ a : Additive W, (2 : ℕ) • a = 0) (t l : MulAut W) (k : ℕ) :
    E3.mQuot ⊤ (fixV (Subgroup.zpowers ((t * (l⁻¹ * t * l)) ^ k))) ≤
      2 * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
  letI : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule hW2
  haveI : Module.Finite (ZMod 2) (Additive W) := Module.Finite.of_finite
  rw [mQuot_fixV_zpowers_eq_finrank_range_sub_one,
    mQuot_fixV_zpowers_eq_finrank_range_sub_one]
  exact Thm14_5.finrank_range_pow_mul_conj_le (V := Additive W) (G := MulAut W)
    mulAutLinearHom t l k

theorem w135c2_psu_outer_involution {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2) :
    ∃ y ∈ L, y ≠ 1 ∧ y * y = 1 ∧
      E3.mQuot ⊤ (fixV (Subgroup.zpowers y)) ≤ 2 * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
  classical
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun g : MulAut W => (g : W → W)) DFunLike.coe_injective
  have hW2 : ∀ a : Additive W, (2 : ℕ) • a = 0 := fun a => by
    apply Additive.toMul.injective
    show (Additive.toMul a) ^ 2 = 1
    exact hW _
  have htt : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at h1
  have hLY : L ≤ Y := hctx.2.2.1
  have hYN : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mp (w135_normal_of_ctx hctx)
  have htN : t ∈ Subgroup.normalizer (L : Set (MulAut W)) := hYN htY
  have hQ : IsQuasisimple ↥L := hctx.2.2.2.2.1
  have hperf : Group.IsPerfect ↥L := hQ.1
  have htc : ∃ x ∈ L, t * x ≠ x * t := w135c2_psu_outer_not_commute hctx htY ht2
  have hL : ∀ N : Subgroup ↥L, N.Normal → Odd (Nat.card N) → N ≤ Subgroup.center ↥L :=
    w135c2_odd_normal_le_center hQ
  obtain ⟨l, hl, k, hyL, hy1, hy2⟩ :=
    w135c2_exists_involution_pow_mul_conj_of_perfect hperf hL htN htt htc
  exact ⟨(t * (l⁻¹ * t * l)) ^ k, hyL, hy1, hy2, w135c2_mQuot_le_two_mul hW2 t l k⟩

end CFSG.LocalAnalysis.WeakClosure81

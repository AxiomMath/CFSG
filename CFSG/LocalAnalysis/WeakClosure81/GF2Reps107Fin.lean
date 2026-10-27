module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps107Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps107TripleDefs
import CFSG.LocalAnalysis.WeakClosure81.U43TripleHolds
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps107FinZStar
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps107FinGen
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps107FinBound
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps107Base
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Ctx
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13TwoLem
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Sev
import CFSG.GH74.Orders.LieType
public import CFSG.Quasithin.Background.B1Coprime
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)

theorem w107_exists_not_commute {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} (hctx : Is135Context Y L) {t : MulAut W} (ht : orderOf t = 2) :
    ∃ l ∈ L, t * l ≠ l * t := by
  by_contra hnc
  push Not at hnc
  obtain ⟨-, -, -, -, -, hIrr⟩ := hctx
  set C : Subgroup W := fixV (Subgroup.zpowers t) with hC
  have hmem : ∀ l ∈ L, ∀ x ∈ Subgroup.zpowers t, l * x * l⁻¹ ∈ Subgroup.zpowers t := by
    intro l hl x hx
    have hcomm : l * t = t * l := (hnc l hl).symm
    have hconj : l * t * l⁻¹ = t := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← conj_zpow, hconj]
    exact Subgroup.zpow_mem_zpowers t k
  have hstab : StableUnder L C := stableUnder_fixV hmem
  rcases hIrr.2.2.2 C hstab bot_le le_top with hbot | htop
  · have htop_ne : (⊤ : Subgroup W) ≠ ⊥ := ne_of_gt hIrr.1
    have hB : IsPGroup 2 (Subgroup.zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht]; norm_num)
    obtain ⟨m, -, hm1, hmfix⟩ :=
      CFSG.Quasithin.B1.exists_fixed_ne_one hW hB (M := ⊤)
        (fun b _ m _ => Subgroup.mem_top m) htop_ne
    have hmC : m ∈ C := mem_fixV.mpr hmfix
    rw [hbot] at hmC
    exact hm1 (Subgroup.mem_bot.mp hmC)
  · have ht1 : t = 1 := by
      ext v
      have hv : v ∈ C := htop ▸ Subgroup.mem_top v
      simpa using (mem_fixV.mp hv) t (Subgroup.mem_zpowers t)
    rw [ht1, orderOf_one] at ht
    norm_num at ht

theorem w4Lem10_7Fin_of_u43TripleGen (hgen : U43TripleGen) : W4Lem10_7Fin := by
  intro W _ _ hW Y L t hctx hLie hZ3 htz _ htY ht2 hm
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have htt : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht2] at h
    simpa [pow_two] using h
  have htL : ∀ l ∈ L, t * l * t⁻¹ ∈ L := by
    have hconj := conj_mem_of_normal_subgroupOf hctx.2.2.1 (w135_normal_of_ctx hctx)
    exact fun l hl => hconj t htY l hl
  have heven : Even (Nat.card ↥L) := by
    have hcard : Nat.card (↥L ⧸ Subgroup.center ↥L) = 2 ^ 7 * 3 ^ 6 * 5 * 7 := by
      rw [CFSG.GH74.card_of_lieModel_PSU (n := 4) (p := 3) (f := 1)
        (by norm_num) (by norm_num) hLie]
      decide
    have hq := Subgroup.card_quotient_dvd_card (Subgroup.center ↥L)
    rw [hcard] at hq
    exact even_iff_two_dvd.mpr (dvd_trans (by norm_num) hq)
  obtain ⟨g, hne, hcomm, hxL⟩ := exists_conj_ne_commute_mul_mem_of_quasisimple
    hctx.2.2.2.2.1 heven htt htL (w107_exists_not_commute hW hctx ht2)
  have hx1 : g * t * g⁻¹ * t ≠ 1 := by
    intro h1
    apply hne
    have h2 : g * t * g⁻¹ = t⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [inv_eq_of_mul_eq_one_right htt] at h2
    exact h2
  have hx2 : (g * t * g⁻¹ * t) ^ 2 = 1 := by
    have hs2 : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
      calc (g * t * g⁻¹) * (g * t * g⁻¹)
          = g * (t * t) * g⁻¹ := by group
        _ = 1 := by rw [htt]; group
    rw [pow_two]
    calc (g * t * g⁻¹ * t) * (g * t * g⁻¹ * t)
        = (g * t * g⁻¹) * (t * (g * t * g⁻¹)) * t := by group
      _ = (g * t * g⁻¹) * ((g * t * g⁻¹) * t) * t := by rw [← hcomm]
      _ = ((g * t * g⁻¹) * (g * t * g⁻¹)) * (t * t) := by group
      _ = 1 := by rw [hs2, htt, mul_one]
  have ht3 : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) ≤ 3 :=
    w107_rk_commSub_zpowers_le_three hm
  have hevt : Even (rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t))) := by
    have : Nontrivial ↥(Subgroup.center ↥L) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hZ3]
      norm_num
    obtain ⟨z, hz1⟩ := exists_ne (1 : ↥(Subgroup.center ↥L))
    have hz : (z : ↥L) ∈ Subgroup.center ↥L := z.2
    have hz1' : (z : ↥L) ≠ 1 := fun h => hz1 (Subtype.ext h)
    let y : MulAut W := (z : MulAut W)
    have hy3 : y ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := ↥(Subgroup.center ↥L)) (x := z)
      rw [hZ3] at h
      have h' := congrArg (fun w : ↥(Subgroup.center ↥L) => ((w : ↥L) : MulAut W)) h
      simpa [y] using h'
    have hfixV : fixV (Subgroup.zpowers y) = ⊥ := by
      simpa [y] using w107_fixV_center_eq_bot hctx (z := (z : ↥L)) hz hz1'
    have hty : Commute t y := by
      rw [commute_iff_eq]
      simpa [y] using htz (z : ↥L) hz
    have hS : ∀ u ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers t),
        y u ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers t) := by
      refine CFSG.Quasithin.B1.commSub_invariant_of_commute (Y := Subgroup.zpowers t)
        (B := Subgroup.zpowers y) (M := ⊤) ?_ ?_ y (Subgroup.mem_zpowers y)
      · intro a ha b hb
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        exact (hty.zpow_zpow m n).eq
      · intro b _ m _
        exact Subgroup.mem_top m
    have hfix : ∀ u ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers t),
        y u = u → u = 1 := by
      intro u _ hyu
      have hu' : u ∈ fixV (Subgroup.zpowers y) :=
        CFSG.Quasithin.mem_fixV_zpowers_iff_apply.mpr hyu
      rw [hfixV] at hu'
      exact Subgroup.mem_bot.mp hu'
    exact w16h_even_rk_of_fixedFree hW hy3 hS hfix
  have hx4 : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers (g * t * g⁻¹ * t))) ≤ 4 := by
    have h2 := rk_commSub_zpowers_conj_mul_le hW (t := t) g
    obtain ⟨k, hk⟩ := hevt
    omega
  have hle : rk W ≤ 12 := by
    have h3 := w107_rk_le_three_mul_rk_commSub hW hgen hctx.2.2.2.2.1
      (by rw [hZ3]; exact ⟨1, rfl⟩) hLie (w135_commSub_top_eq_top hctx) hxL hx2 hx1
    omega
  have hge : 12 ≤ rk W := w107_twelve_le_rk hW hLie (by rw [hZ3])
  omega

theorem w4Lem10_7Fin_holds : W4Lem10_7Fin :=
  w4Lem10_7Fin_of_u43TripleGen u43TripleGen_holds

end CFSG.LocalAnalysis.WeakClosure81

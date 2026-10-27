module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuSixRow
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslCover
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslDimSingle
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuCover
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuLabelExt
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuNatural
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuOuterInvolution
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuSemilinear
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuLinearDegree
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuLabelRank
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuOuterClassify
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2NatB
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Finset
open Module
open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.LieType.SpecialLinear.ExteriorModel

theorem w135c2_psu_outer
    (hSix : PsuSixOuterRow) {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (htY : t ∈ Y) (htL : t ∉ L) (ht2 : orderOf t = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {n f : ℕ} (hn4 : n ≠ 4)
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSU n 2 f) : W4Lem13_5Concl W Y L t := by
  classical
  have hW2 : ∀ a : Additive W, (2 : ℕ) • a = 0 := fun a => by
    apply Additive.toMul.injective
    show (Additive.toMul a) ^ 2 = 1
    exact hW _
  letI : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule hW2
  haveI : Module.Finite (ZMod 2) (Additive W) := Module.Finite.of_finite
  have hQ : IsQuasisimple ↥L := hctx.2.2.2.2.1
  have hIrr : IsIrrOn L ⊤ ⊥ := hctx.2.2.2.2.2
  obtain ⟨hn3, hf1, hq, K, hKfield, hKfin, hKchar, hKcard, φ, hφs, hker, hodd⟩ :=
    w135c2_psu_cover hW hQ hIrr hlie
  have hirr := w135c2_psl_rep_irreducible hIrr φ hφs
  have hne := w135c2_psl_rep_ne_one hQ φ hφs
  have hnf : ¬ (n = 3 ∧ f = 1) := by
    rintro ⟨h3, h1⟩
    exact hq (by rw [h3, h1]; rfl)
  obtain ⟨s, ε, hs1, hE, h0, hact, hper, hns, hrank, ⟨k, hkfield, hkchar, hcardW⟩,
    hdesc, hrot, hmin, hself⟩ :=
    w135c2_psu_label_ext hn3 (by omega : 0 < f) hKcard (pslRep φ) hirr hne
  have hcardW' : Nat.card W = 2 ^ (s * finrank k (BModel k ε)) := hcardW
  let tau : Additive W ≃ₗ[ZMod 2] Additive W := mulAutLinearEquiv t
  have htt : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at h1
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htau : ∀ v, tau (tau v) = v := by
    intro v
    change mulAutLinear t (mulAutLinear t v) = v
    rw [← Module.End.mul_apply, ← mulAutLinear_mul, htt, mulAutLinear_one]
    rfl
  have hN : ∀ g : SU (unitaryInvolution K 2 f) n,
      ∃ g' : SU (unitaryInvolution K 2 f) n,
        ∀ v : Additive W, tau (pslRep φ g (tau v)) = pslRep φ g' v := by
    intro g
    have hconj : t * (((φ g : ↥L) : MulAut W)) * t⁻¹ ∈ L := by
      have hLY : L ≤ Y := hctx.2.2.1
      have hmem := (w135_normal_of_ctx hctx).conj_mem
        (⟨((φ g : ↥L) : MulAut W), hLY (φ g).2⟩ : ↥Y)
        (Subgroup.mem_subgroupOf.mpr (φ g).2) (⟨t, htY⟩ : ↥Y)
      simpa using (Subgroup.mem_subgroupOf.mp hmem)
    obtain ⟨g', hg'⟩ := hφs ⟨t * (((φ g : ↥L) : MulAut W)) * t⁻¹, hconj⟩
    refine ⟨g', fun v => ?_⟩
    rw [pslRep_apply, pslRep_apply, hg']
    change mulAutLinear t (mulAutLinear ((φ g : ↥L) : MulAut W) (mulAutLinear t v)) =
      mulAutLinear (t * ((φ g : ↥L) : MulAut W) * t⁻¹) v
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← mulAutLinear_mul,
      ← mulAutLinear_mul, htinv]
  let d : ℕ := finrank (ZMod 2)
    (LinearMap.range ((tau : Additive W →ₗ[ZMod 2] Additive W) - 1))
  have hdeq : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) = d := by
    rw [mQuot_fixV_zpowers_eq_finrank_range_sub_one t]
    rfl
  have hd3 : d ≤ 3 := by
    rw [← hdeq]
    exact hm
  have hdpos : 1 ≤ d := by
    change 1 ≤ finrank (ZMod 2)
      (LinearMap.range ((tau : Additive W →ₗ[ZMod 2] Additive W) - 1))
    rw [Submodule.one_le_finrank_iff]
    intro hbot
    have hzero : ((tau : Additive W →ₗ[ZMod 2] Additive W) - 1) = 0 :=
      LinearMap.range_eq_bot.mp hbot
    have hcoe : (tau : Additive W →ₗ[ZMod 2] Additive W) = 1 := sub_eq_zero.mp hzero
    have htriv : ∀ w : W, t w = w := by
      intro w
      have h := congrArg (fun f : Additive W →ₗ[ZMod 2] Additive W =>
        f (Additive.ofMul w)) hcoe
      change mulAutLinear t (Additive.ofMul w) = Additive.ofMul w at h
      rw [mulAutLinear_apply] at h
      simpa using congrArg Additive.toMul h
    have ht1 : t = 1 := MulEquiv.ext htriv
    rw [ht1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  by_cases hcomm : ∀ (T : Module.End (MonoidAlgebra (ZMod 2) (SU (unitaryInvolution K 2 f) n))
      (pslRep φ).asModule) (v : Additive W), tau (T (tau v)) = T v
  ·
    have hsdvd : s ∣ d :=
      w135c2_psu_linear_degree (pslRep φ) hirr hE
        (tau : Additive W →ₗ[ZMod 2] Additive W)
        (fun T v => by
          have h := hcomm T (tau v)
          rw [htau v] at h
          exact h)
    obtain ⟨u, hu⟩ := hsdvd
    have hu1 : 1 ≤ u := by
      rcases Nat.eq_zero_or_pos u with h0 | h0
      · rw [h0, mul_zero] at hu
        omega
      · exact h0
    have hsu : s * u ≤ 3 := by
      rw [← hu]
      exact hd3
    obtain ⟨y, hyL, hy1, hy2, hyd⟩ := w135c2_psu_outer_involution hW hctx htY ht2
    have hyord : orderOf (⟨y, hyL⟩ : ↥L) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
    obtain ⟨yy, hyy2, hyy1, hphiyy⟩ := w135c2_exists_involution_lift φ hodd hyord
      (MonoidHom.mem_range.mpr (hφs ⟨y, hyL⟩))
    have hfinr : finrank (ZMod 2) (LinearMap.range (pslRep φ yy - 1)) =
        E3.mQuot ⊤ (fixV (Subgroup.zpowers y)) := by
      simpa [hphiyy] using w135c2_psl_finrank_range φ yy
    have hmv : movedTop (by omega : 2 ≤ n) ε ≤ 4 * u := by
      have h1 : s * movedTop (by omega : 2 ≤ n) ε ≤ s * (4 * u) := by
        calc s * movedTop (by omega : 2 ≤ n) ε
            ≤ 2 * finrank (ZMod 2) (LinearMap.range (pslRep φ yy - 1)) :=
              hrank yy hyy2 hyy1
          _ = 2 * E3.mQuot ⊤ (fixV (Subgroup.zpowers y)) := by rw [hfinr]
          _ ≤ 2 * (2 * E3.mQuot ⊤ (fixV (Subgroup.zpowers t))) :=
              Nat.mul_le_mul_left 2 hyd
          _ = s * (4 * u) := by rw [hdeq, hu]; ring
      exact Nat.le_of_mul_le_mul_left h1 (by omega)
    rcases w135c2_psu_classify_outer hn3 hn4 hnf hs1 hu1 hsu ε h0 hact hper hns hmv with
      ⟨r₀, j, hone, hεj, hj, hf1'⟩ | ⟨h6, hf1', hs1', hu3, r₀, j, hone, hj3, hεj⟩
    ·
      obtain ⟨β, hβ⟩ := hdesc r₀ j hone hεj hj
      subst hf1'
      exact w135c2_natural hctx htY ht2 hW (w135c2_psu_natural_chev2 hKcard φ hφs β hβ)
    ·
      exfalso
      have hlie6 : LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 6 2 1 := by
        rw [h6, hf1'] at hlie
        exact hlie
      have hcardle : ∀ r : Fin f, (ε r).card ≤ 1 := by
        intro r
        rcases eq_or_ne r r₀ with rfl | hr
        · rw [hεj]; simp
        · rw [hone r hr]; simp
      have hfin20 : finrank k (BModel k ε) = 20 := by
        rw [w135c2_finrank_bModel_of_card_le_one ε hcardle]
        rw [Finset.prod_eq_single_of_mem r₀ (Finset.mem_univ r₀)
          (fun b _ hb => by rw [hone b hb]; simp)]
        rw [hεj, Finset.prod_singleton, hj3, h6]
        decide
      have hcard20 : Nat.card W = 2 ^ 20 := by
        rw [hcardW', hs1', hfin20, one_mul]
      have h4 := hSix W hW Y L t hctx htY htL ht2 hlie6 hcard20
      omega
  ·
    push Not at hcomm
    have hdich : 2 * d = finrank (ZMod 2) (Additive W) := by
      have h := w135c2_psu_semilinear_finrank (pslRep φ) hirr tau htau hN hcomm
      simpa [d] using h
    have hgt := w135c2_psu_label_gt_six (k := k) hn3 hn4 hnf hs1 ε h0 hact hper hns
    have hV : finrank (ZMod 2) (Additive W) = s * finrank k (BModel k ε) := by
      have h1 : Nat.card W = 2 ^ finrank (ZMod 2) (Additive W) := by
        have h1' := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
        rw [Nat.card_zmod] at h1'
        exact h1'
      exact Nat.pow_right_injective (le_refl 2) (h1.symm.trans hcardW')
    omega

end CFSG.LocalAnalysis.WeakClosure81

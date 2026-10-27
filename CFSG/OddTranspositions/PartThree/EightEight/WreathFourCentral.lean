module

public import CFSG.OddTranspositions.PartThree.EightEight.Star
public import CFSG.OddTranspositions.WreathBase
import CFSG.OddTranspositions.PartThree.EightEight.BlockRebase
import CFSG.OddTranspositions.PartThree.EightEight.TheoremWBlock
import CFSG.OddTranspositions.PartThree.EightEight.WreathSwapClass
import CFSG.OddTranspositions.PartThree.EightEight.WreathBlocks
import CFSG.OddTranspositions.PartThree.EightEight.WreathThree
import CFSG.OddTranspositions.PartThree.Ten.TenTwoQ
import CFSG.Timmesfeld.Bridge.Asc72ElemCompQuot
public import CFSG.Timmesfeld.Bridge.Asc72WreathL2
import CFSG.CGT.Timmesfeld75.Statements
import CFSG.CGT.Timmesfeld75.Targets
import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ
open CFSG.OddTranspositions.PartThree.WreathEndgame

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
private theorem ker_comp_mk_eq_center_w4z (hC : HypothesisC (G := G) D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤
      Subgroup.center (Halpha D hC.alpha))
    {f : ℕ} (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
      L2Wreath f 4) :
    ((φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) →*
        L2Wreath f 4).comp
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))).ker =
      Subgroup.center (Halpha D hC.alpha) := by
  let Rθ := CFSG.solvableRadical (Halpha D hC.alpha)
  let π : Halpha D hC.alpha →* L2Wreath f 4 :=
    (φ : _ →* L2Wreath f 4).comp (QuotientGroup.mk' Rθ)
  have hker : π.ker = Rθ := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hxφ : φ (QuotientGroup.mk' Rθ x) = 1 := by simpa [π] using hx
      have hx1 : QuotientGroup.mk' Rθ x = 1 :=
        φ.injective (by simpa using hxφ)
      exact (QuotientGroup.eq_one_iff x).mp hx1
    · intro hx
      have hx1 : QuotientGroup.mk' Rθ x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      simpa [π] using congrArg (⇑φ) hx1
  show π.ker = Subgroup.center (Halpha D hC.alpha)
  rw [hker]
  exact le_antisymm hMZ otg2_center_le_solvableRadical

omit [Finite G] in
private theorem commute_d_of_isTriangle_w4z (hC : HypothesisC (G := G) D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤
      Subgroup.center (Halpha D hC.alpha))
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {d t : Halpha D hC.alpha}
    (hdeq : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) t)
    (htcoe : (t : G) = (x * y * w) ^ n) :
    Commute (d : G) x ∧ Commute (d : G) y ∧ Commute (d : G) w := by
  let Rθ := CFSG.solvableRadical (Halpha D hC.alpha)
  obtain ⟨-, -, hzx, hzy, hzw, -⟩ :=
    IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord
  let xH : Halpha D hC.alpha := ⟨x, Subgroup.subset_closure hx⟩
  let yH : Halpha D hC.alpha := ⟨y, Subgroup.subset_closure hy⟩
  let wH : Halpha D hC.alpha := ⟨w, Subgroup.subset_closure hw⟩
  have hm : d⁻¹ * t ∈ Rθ := by
    have h1 : QuotientGroup.mk' Rθ (d⁻¹ * t) = 1 := by
      rw [map_mul, map_inv, hdeq, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp h1
  have htx : Commute t xH := by
    refine TenTwoQ.commute_coe_iff.mpr ?_
    simpa [xH, htcoe] using hzx
  have hty : Commute t yH := by
    refine TenTwoQ.commute_coe_iff.mpr ?_
    simpa [yH, htcoe] using hzy
  have htw : Commute t wH := by
    refine TenTwoQ.commute_coe_iff.mpr ?_
    simpa [wH, htcoe] using hzw
  have hcent : ∀ z : Halpha D hC.alpha, Commute z (d⁻¹ * t) := fun z =>
    Subgroup.mem_center_iff.mp (hMZ hm) z
  have hd_eq : d = t * (d⁻¹ * t)⁻¹ := by group
  have hdxH : Commute d xH := by
    rw [hd_eq]
    exact htx.mul_left (hcent xH).symm.inv_left
  have hdyH : Commute d yH := by
    rw [hd_eq]
    exact hty.mul_left (hcent yH).symm.inv_left
  have hdwH : Commute d wH := by
    rw [hd_eq]
    exact htw.mul_left (hcent wH).symm.inv_left
  have hdx : Commute (d : G) x := by
    simpa [xH] using TenTwoQ.commute_coe_iff.mp hdxH
  have hdy : Commute (d : G) y := by
    simpa [yH] using TenTwoQ.commute_coe_iff.mp hdyH
  have hdw : Commute (d : G) w := by
    simpa [wH] using TenTwoQ.commute_coe_iff.mp hdwH
  exact ⟨hdx, hdy, hdw⟩

private theorem exists_perfect_coordComm_w4z (hC : HypothesisC (G := G) D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤
      Subgroup.center (Halpha D hC.alpha))
    {f : ℕ} (hf : 2 ≤ f)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f 4)
    {d : Halpha D hC.alpha}
    (hswapd : φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d) ∈
      swapSet f 4)
    {m : Halpha D hC.alpha} (hmM : m ∈ CFSG.solvableRadical (Halpha D hC.alpha)) :
    ∃ R : Subgroup G, ⁅R, R⁆ = R ∧
      (∀ r ∈ R, Commute r (d : G)) ∧ (∀ r ∈ R, Commute r (m : G)) ∧ (m : G) ∈ R := by
  obtain ⟨RH, hRH, hZ, hRHd⟩ := exists_perfect_center_le_of_mem_swapSet hf (by norm_num)
    ⟨DstarH_isClass hC, DstarH_isOddTransp hC, DstarH_closure_eq_top hC⟩
    (φ.surjective.comp (QuotientGroup.mk'_surjective _)) (ker_comp_mk_eq_center_w4z hC hMZ φ)
    hswapd
  refine ⟨RH.map (Halpha D hC.alpha).subtype, ?_, ?_, ?_, ⟨m, hZ (hMZ hmM), rfl⟩⟩
  · rw [← Subgroup.map_commutator, hRH]
  · rintro _ ⟨r, hr, rfl⟩
    exact TenTwoQ.commute_coe_iff.mp (hRHd r hr)
  · rintro _ ⟨r, -, rfl⟩
    exact TenTwoQ.commute_coe_iff.mp (Subgroup.mem_center_iff.mp (hMZ hmM) r)

private theorem false_of_coordComm_w4z (hC : HypothesisC (G := G) D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤
      Subgroup.center (Halpha D hC.alpha))
    {f : ℕ} (hf : 2 ≤ f)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f 4)
    {d m t : Halpha D hC.alpha} (ht_eq : t = d * m)
    (hmM : m ∈ CFSG.solvableRadical (Halpha D hC.alpha))
    (hswapd : φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d) ∈
      swapSet f 4)
    {hC' : HypothesisC (G := G) D} {ρ : Set G} (hα' : hC'.alpha = ρ)
    (hρ : ρ ∈ Dalpha D hC.alpha) (hdρ : (d : G) ∈ ρ)
    {φ' : (Halpha D hC'.alpha ⧸ CFSG.solvableRadical (Halpha D hC'.alpha)) ≃* L2Wreath f 4}
    {t' : Halpha D hC'.alpha} (ht'coe : (t' : G) = (t : G))
    (ht'swap : φ' (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC'.alpha)) t') ∈
      swapSet f 4) : False := by
  obtain ⟨R, hRperf, hRd, hRm, hmR⟩ := exists_perfect_coordComm_w4z hC hMZ hf φ hswapd hmM
  exact false_of_perfect_of_mul_mem_swapSet hC hρ.1 hdρ hα' hf (Or.inr rfl) φ'
    (by rw [ht'coe, ht_eq, Subgroup.coe_mul]) ht'swap hRperf hRd hRm hmR

theorem not_isStarTriangle_of_solvableRadical_le_center (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {f : ℕ} (hf : 2 ≤ f)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f 4)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (x w y : G) : ¬ IsStarTriangle hC x w y := by
  rintro ⟨ht, hthird, hx, hw, hy, -⟩
  obtain ⟨n, hn, -, hord⟩ := hthird
  obtain ⟨t, htcoe, htswap⟩ : ∃ t : Halpha D hC.alpha, (t : G) = (x * y * w) ^ n ∧
      φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) t) ∈ swapSet f 4 :=
    ⟨⟨(x * y * w) ^ n, mul_mul_pow_mem_Halpha hC hx hw hy n⟩, rfl,
      mem_swapSet_of_l2Wreath h86 h87 hC hrad hO4 hF hne hns hf (Or.inr rfl) φ ht hx hw hy hn
        hord rfl⟩
  obtain ⟨d, hd, hdφ⟩ := exists_mem_DstarH_eq_of_mem_swapSet hC hns hf (Or.inr rfl) φ htswap
  have hdeq : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) t := φ.injective hdφ
  obtain ⟨hdx, hdy, hdw⟩ :=
    commute_d_of_isTriangle_w4z hC hMZ ht hx hw hy hn hord hdeq htcoe
  obtain ⟨ρ, hρ, hdρ, hxS, hwS, hyS⟩ :=
    exists_mem_Dalpha_mem_DalphaStar_of_isTriangle h86 h87 hC hrad hO4 hF hne ht hx hw hy hd hdx
      hdy hdw
  obtain ⟨hC', φ', t', hα', ht'coe, ht'swap⟩ :=
    exists_rebase_of_l2Wreath h86 h87 hC hrad hO4 hF hne hns hf (Or.inr rfl) φ ht hρ.1 hxS hwS hyS
      hn hord
  have hswapd : φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d) ∈
      swapSet f 4 := by
    rw [hdeq]
    exact htswap
  have hmM : d⁻¹ * t ∈ CFSG.solvableRadical (Halpha D hC.alpha) := by
    have h1 : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (d⁻¹ * t) = 1 := by
      rw [map_mul, map_inv, hdeq, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp h1
  exact false_of_coordComm_w4z hC hMZ hf φ (by group) hmM hswapd hα' hρ hdρ
    (φ' := φ') (t := t) (by rw [ht'coe, htcoe]) ht'swap

end CFSG.OddTranspositions.PartThree.EightEight

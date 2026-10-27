module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KE64
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Reduced
import CFSG.GroupTheory.PCore.QuasisimpleNormalCore
import CFSG.LocalAnalysis.RankThreeEvenClassification.PrimeElementLifting
import CFSG.Adapters.StatedClassicalOrders
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KDefs
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F09 (Hbar9 img9 L9 Lbar9 IsSL2Cover Hyp91)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem c8k_frattini_lift {H : Subgroup G} {d : ↥H} (hd : orderOf d = 3) {g : Hbar9 H}
    (hg : g ∈ normalizer ((zpowers (d : Hbar9 H) : Subgroup (Hbar9 H)) : Set (Hbar9 H))) :
    ∃ n : ↥H, (n : G) ∈ normalizer ((zpowers (d : G) : Subgroup G) : Set G) ∧
      ∃ k : ℤ, (n : Hbar9 H) = (d : Hbar9 H) ^ k * g := by
  let N : Subgroup ↥H := CFSG.pPrimeCore 3 ↥H
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : Nat.Coprime 3 (Nat.card N) := CFSG.pPrimeCore_coprime_card
  have hS : IsPGroup 3 (Subgroup.zpowers d) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hd]
    norm_num
  have hz : (Subgroup.zpowers d).map (QuotientGroup.mk' N) =
      Subgroup.zpowers (d : Hbar9 H) := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hg' : g ∈ normalizer (((Subgroup.zpowers d).map (QuotientGroup.mk' N) :
      Subgroup (↥H ⧸ N)) : Set (↥H ⧸ N)) := by
    rw [hz]
    exact hg
  rw [CFSG.LocalAnalysis.RankFourTheoremC.normalizer_map_mk N Nat.prime_three hN hS] at hg'
  obtain ⟨n, hn, hng⟩ := Subgroup.mem_map.mp hg'
  have hsub : (Subgroup.zpowers (d : G) : Subgroup G) =
      (Subgroup.zpowers d).map H.subtype := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hnorm : (n : G) ∈ normalizer ((Subgroup.zpowers (d : G) : Subgroup G) : Set G) := by
    rw [hsub, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' := (Subgroup.mem_normalizer_iff.mp hn x).mp hx
      exact ⟨n * x * n⁻¹, hx', by simp⟩
    · rintro ⟨y, hy, hyh⟩
      have hninv : n⁻¹ ∈ normalizer (Subgroup.zpowers d : Set ↥H) := Subgroup.inv_mem _ hn
      have hy' := (Subgroup.mem_normalizer_iff.mp hninv y).mp hy
      have hy'' : n⁻¹ * y * n ∈ Subgroup.zpowers d := by simpa using hy'
      refine ⟨n⁻¹ * y * n, hy'', ?_⟩
      have hyh' : (y : G) = (n : G) * h * (n : G)⁻¹ := hyh
      calc (n : G)⁻¹ * (y : G) * (n : G)
          = (n : G)⁻¹ * ((n : G) * h * (n : G)⁻¹) * (n : G) := by rw [hyh']
        _ = h := by group
  refine ⟨n, hnorm, 0, ?_⟩
  simpa using hng

private theorem c8k_opp_le (Y : Subgroup G) : Opp 3 Y ≤ Y :=
  (Subgroup.closure_le Y).mpr fun _ hz => hz.1

private theorem c8k_opp_conj_mem {Y : Subgroup G} {y : G} (hy : y ∈ Y) {x : G}
    (hx : x ∈ Opp 3 Y) : y * x * y⁻¹ ∈ Opp 3 Y := by
  unfold Opp CFSG.RankThree.PartOne.pElementSubgroup at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem z hz =>
      refine Subgroup.subset_closure ⟨Y.mul_mem (Y.mul_mem hy hz.1) (Y.inv_mem hy), ?_⟩
      obtain ⟨k, hk⟩ := hz.2
      refine ⟨k, ?_⟩
      have h := orderOf_injective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective z
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply] at h
      rw [h, hk]
  | one => simp
  | mul a b _ _ ha hb =>
      have h := Subgroup.mul_mem (Subgroup.closure {x : G | x ∈ Y ∧ ∃ k, orderOf x = 3 ^ k}) ha hb
      convert h using 1 <;> group
  | inv a _ ha =>
      have h := Subgroup.inv_mem (Subgroup.closure {x : G | x ∈ Y ∧ ∃ k, orderOf x = 3 ^ k}) ha
      convert h using 1 <;> group

private theorem c8k_opp_subgroupOf_normal (Y : Subgroup G) :
    ((Opp 3 Y).subgroupOf Y).Normal :=
  ⟨fun _ hx y => Subgroup.mem_subgroupOf.mpr
    (c8k_opp_conj_mem y.2 (Subgroup.mem_subgroupOf.mp hx))⟩

theorem c8k_mem_opp_mul {Y C : Subgroup G} (hCY : C ≤ Y) (hP : C8P0 Y C) :
    ∀ n ∈ Y, ∃ x ∈ Opp 3 Y, ∃ c ∈ C, n = x * c := by
  obtain ⟨P, _, φ, hφs, hφk, ⟨N, hNn, hN64, hL3⟩, hperf⟩ := hP
  haveI : Finite P := Finite.of_surjective φ hφs
  haveI := hNn
  let X : Subgroup G := Opp 3 Y
  let X' : Subgroup ↥Y := X.subgroupOf Y
  have hXn : X'.Normal := c8k_opp_subgroupOf_normal Y
  haveI := hXn
  let R : Subgroup P := X'.map φ
  have hRn : R.Normal := hXn.map φ hφs
  have h3 : ∀ x : P, (∃ k : ℕ, x ^ 3 ^ k = 1) → x ∈ R := by
    intro p hp
    obtain ⟨k, hk⟩ := hp
    obtain ⟨y, hyφ, i, hyi⟩ :=
      CFSG.RankThreeEvenClassification.Helpers.prime_power_element_lifts_surjective 3
        Nat.prime_three φ hφs p k hk
    have hdvd : orderOf y ∣ 3 ^ i := orderOf_dvd_of_pow_eq_one hyi
    obtain ⟨s, -, hys⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hyX : y ∈ X' := by
      refine Subgroup.mem_subgroupOf.mpr ?_
      refine Subgroup.subset_closure ⟨y.2, s, ?_⟩
      rw [Subgroup.orderOf_coe, hys]
    exact Subgroup.mem_map.mpr ⟨y, hyX, hyφ⟩
  have hRtop : R = ⊤ := c8_e64_eq_top hN64 hL3 hperf hRn h3
  intro n hn
  have hnP : φ ⟨n, hn⟩ ∈ R := by rw [hRtop]; exact Subgroup.mem_top _
  obtain ⟨x, hx, hxφ⟩ := Subgroup.mem_map.mp hnP
  have hcK : (x : ↥Y)⁻¹ * ⟨n, hn⟩ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxφ, inv_mul_cancel]
  have hcC : (x : ↥Y)⁻¹ * ⟨n, hn⟩ ∈ C.subgroupOf Y := by
    rw [← hφk]
    exact hcK
  refine ⟨(x : G), Subgroup.mem_subgroupOf.mp hx, ((x : ↥Y)⁻¹ * ⟨n, hn⟩ : ↥Y), ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mp hcC
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group

private theorem c8k_three_dvd_card_lieModel_psl2 {X : Type} [Group X] {e : ℕ} (he : 1 ≤ e)
    (h : CFSG.Blueprint.LieModel X .PSL 2 7 e) : 3 ∣ Nat.card X := by
  have hsc : CFSG.Open.StatedClassicalModel X .PSL 2 7 e :=
    CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num) hsc]
  simp
  have hqodd : Odd (7 ^ e) := (show Odd 7 by norm_num).pow
  have h2 : 2 ∣ 7 ^ e - 1 := by
    obtain ⟨k, hk⟩ := hqodd
    omega
  have h3 : 3 ∣ 7 ^ e - 1 :=
    dvd_trans (by norm_num : 3 ∣ 7 - 1) (Nat.sub_one_dvd_pow_sub_one 7 e)
  have h2sq : 2 ∣ (7 ^ e) ^ 2 - 1 :=
    dvd_trans (by norm_num : 2 ∣ 8) (Nat.eight_dvd_sq_sub_one_of_odd hqodd)
  have h3sq : 3 ∣ (7 ^ e) ^ 2 - 1 :=
    dvd_trans h3 (Nat.sub_one_dvd_pow_sub_one (7 ^ e) 2)
  have h6 : 2 * 3 ∣ (7 ^ e) ^ 2 - 1 :=
    (show Nat.Coprime 2 3 by norm_num).mul_dvd_of_dvd_of_dvd h2sq h3sq
  have hmain : 2 * 3 ∣ 7 ^ e * ((7 ^ e) ^ 2 - 1) := dvd_mul_of_dvd_right h6 _
  have h2main : 2 ∣ 7 ^ e * ((7 ^ e) ^ 2 - 1) := dvd_mul_of_dvd_right h2sq _
  rw [Nat.gcd_eq_left h2, Nat.dvd_div_iff_mul_dvd h2main]
  exact hmain

private theorem c8k_three_dvd_card_isSL2Cover {Q : Type} [Group Q] {e : ℕ} (he : 1 ≤ e)
    (h : IsSL2Cover Q 7 e) : 3 ∣ Nat.card Q := by
  obtain ⟨-, hcent, hlie⟩ := h
  have hq : 3 ∣ Nat.card (Q ⧸ Subgroup.center Q) :=
    c8k_three_dvd_card_lieModel_psl2 he hlie
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q), hcent]
  exact dvd_mul_of_dvd_left hq 2

private theorem c8k_img9_subgroupOf_normal {H Y C : Subgroup G} (hCY : C ≤ Y)
    (hCn : (C.subgroupOf Y).Normal) :
    ((img9 H C).subgroupOf (img9 H Y)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨c, hc, hcn⟩ := Subgroup.mem_map.mp hn
  obtain ⟨y, hy, hgy⟩ := Subgroup.mem_map.mp g.2
  have hyY : (y : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy
  have hcY : (c : G) ∈ Y := hCY (Subgroup.mem_subgroupOf.mp hc)
  have hconj : y * c * y⁻¹ ∈ C.subgroupOf H := by
    have h := hCn.conj_mem (⟨c, hcY⟩ : ↥Y)
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hc)) ⟨y, hyY⟩
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp h)
  refine Subgroup.mem_subgroupOf.mpr ?_
  have hcn' : (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) c = (n : Hbar9 H) := hcn
  have hval : (↑(g * n * g⁻¹) : Hbar9 H) =
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) (y * c * y⁻¹) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hgy, ← hcn',
      map_mul, map_mul, map_inv]
  rw [hval]
  exact Subgroup.mem_map_of_mem _ hconj

theorem c8k_c_centralizes {Y H C : Subgroup G} (hYH : Y ≤ H) (hCY : C ≤ Y)
    (hCn : (C.subgroupOf Y).Normal) (hC3 : ¬ 3 ∣ Nat.card C) {e : ℕ} (he : 1 ≤ e)
    (hS : IsSL2Cover ↥(img9 H (Opp 3 Y)) 7 e) {c : ↥H} (hc : (c : G) ∈ C) :
    ∀ x ∈ img9 H (Opp 3 Y), (c : Hbar9 H) * x = x * (c : Hbar9 H) := by
  let Ybar : Subgroup (Hbar9 H) := img9 H Y
  let Xbar : Subgroup (Hbar9 H) := img9 H (Opp 3 Y)
  let Cbar : Subgroup (Hbar9 H) := img9 H C
  have hCYH : C ≤ H := hCY.trans hYH
  have hXY : Opp 3 Y ≤ Y := c8k_opp_le Y
  have hXbarYbar : Xbar ≤ Ybar := by
    dsimp [Xbar, Ybar, img9]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono H hXY)
  have hCbarYbar : Cbar ≤ Ybar := by
    dsimp [Cbar, Ybar, img9]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono H hCY)
  have hXn : (Xbar.subgroupOf Ybar).Normal := by
    simpa [Xbar, Ybar] using c8k_img9_subgroupOf_normal (H := H) hXY
      (c8k_opp_subgroupOf_normal Y)
  have hCnbar : (Cbar.subgroupOf Ybar).Normal := by
    simpa [Cbar, Ybar] using c8k_img9_subgroupOf_normal (H := H) hCY hCn
  have hLq : CFSG.IsQuasisimple ↥(Xbar.subgroupOf Ybar) := by
    exact CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hXbarYbar) hS.1
  have hNcard : Nat.card (Cbar.subgroupOf Ybar) ∣ Nat.card C := by
    have h1 : Nat.card (Cbar.subgroupOf Ybar) = Nat.card Cbar :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCbarYbar).toEquiv
    rw [h1]
    have h2 : Nat.card Cbar ∣ Nat.card (C.subgroupOf H) := Subgroup.card_map_dvd _ _
    have h3 : Nat.card (C.subgroupOf H) = Nat.card C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCYH).toEquiv
    rwa [h3] at h2
  have hNcop : Nat.Coprime 3 (Nat.card (Cbar.subgroupOf Ybar)) := by
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun hdvd => hC3 (hdvd.trans hNcard)
  have hLcard : Nat.card (Xbar.subgroupOf Ybar) = Nat.card Xbar :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXbarYbar).toEquiv
  have hLp : ¬ Nat.Coprime 3 (Nat.card (Xbar.subgroupOf Ybar)) := by
    rw [hLcard, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    exact fun hdvd => hdvd (c8k_three_dvd_card_isSL2Cover he hS)
  haveI := hCnbar
  haveI := hXn
  have hcent := CFSG.le_centralizer_of_isQuasisimple_of_coprime (p := 3) Nat.prime_three
    (N := Cbar.subgroupOf Ybar) (L := Xbar.subgroupOf Ybar) hLq hNcop hLp
  have hcY : (c : G) ∈ Y := hCY hc
  have hcYbar : (c : Hbar9 H) ∈ Ybar :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hcY)
  have hcCbar : (c : Hbar9 H) ∈ Cbar :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hc)
  let n0 : ↥Ybar := ⟨(c : Hbar9 H), hcYbar⟩
  have hn0 : n0 ∈ Cbar.subgroupOf Ybar := Subgroup.mem_subgroupOf.mpr hcCbar
  intro x hx
  have hxYbar : x ∈ Ybar := hXbarYbar hx
  let x0 : ↥Ybar := ⟨x, hxYbar⟩
  have hx0 : x0 ∈ Xbar.subgroupOf Ybar := Subgroup.mem_subgroupOf.mpr hx
  have hcomm : x0 * n0 = n0 * x0 :=
    (Subgroup.mem_centralizer_iff.mp (hcent hn0)) x0 hx0
  exact (congrArg Subtype.val hcomm).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

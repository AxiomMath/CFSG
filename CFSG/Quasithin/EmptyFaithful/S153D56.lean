module

public import CFSG.Quasithin.EmptyFaithful.S153D53

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

namespace Hyp153

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem two_le_pRank_Y153 (h113 : StageLemma14113) (h : Hyp153 G T Mc M) :
    2 ≤ CFSG.Open.pRank 3 (Y153 Mc M) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ, -⟩ := h.exists_mulEquiv_imageOTwoQuot_of_le_Y153 h113 (le_refl (Y153 Mc M))
  have h2 := S153D.two_le_pRank_Ystar h113 h
  have hp1 : 1 < 3 := by norm_num
  have e0 := pRank_top_subtype (p := 3) (imageOTwoQuot M (Y153 Mc M))
  have e1 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 φ
  have hnd : ¬ 3 ∣ Nat.card (CFSG.Open.pCore 2 ↥(Y153 Mc M)) := by
    intro hd
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥(Y153 Mc M)) 2).exists_card_eq
    rw [hk] at hd
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow hd)) (by norm_num)
  have e2 := CFSG.SectionRank.pRank_quotient_eq (p := 3) (CFSG.Open.pCore 2 ↥(Y153 Mc M)) hnd
  have e3 := pRank_top_subtype (p := 3) (Y153 Mc M)
  omega

end Hyp153

namespace Hyp15310

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp : Subgroup G} {t : G}

theorem case_two_of_pRank_one (h113 : StageLemma14113) (h : Hyp15310 G T Mc M V₁ V₂ Yp t)
    (hr : CFSG.Open.pRank 3 Yp = 1) :
    IsUniqueM (Y153 Mc M ⊔ Sgp153 T V₁) M ∧
      Yp = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) := by
  rcases h.cases with hY | h2
  · exfalso
    have := h.hyp.two_le_pRank_Y153 h113
    rw [← hY, hr] at this
    omega
  · exact h2

end Hyp15310

namespace S153D

section ClaimA

variable {G : Type} [Group G] [Finite G]

theorem mem_of_mul_mem_pCoreOf_pow {M Y : Subgroup G} (hYM : Y ≤ M)
    (hMY : M ≤ Subgroup.normalizer (Y : Set G)) {x y : G} (hxM : x ∈ M) (hy : y ∈ Y) {k : ℕ}
    (hxk : x ^ 3 ^ k = 1) (ho : y⁻¹ * x ∈ pCoreOf 2 M) : x ∈ Y := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (Y.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).mpr hMY
  let q : ↥M →* ↥M ⧸ Y.subgroupOf M := QuotientGroup.mk' (Y.subgroupOf M)
  have hyM : y ∈ M := hYM hy
  have hoM : y⁻¹ * x ∈ M := M.mul_mem (M.inv_mem hyM) hxM
  have hxe : (⟨x, hxM⟩ : ↥M) = ⟨y, hyM⟩ * ⟨y⁻¹ * x, hoM⟩ := Subtype.ext (by simp)
  have hqy : q ⟨y, hyM⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hy)
  have hqx : q ⟨x, hxM⟩ = q ⟨y⁻¹ * x, hoM⟩ := by rw [hxe, map_mul, hqy, one_mul]
  obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 M ⟨y⁻¹ * x, ho⟩
  have hm' : (y⁻¹ * x) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have h2k : (q ⟨x, hxM⟩) ^ 2 ^ m = 1 := by
    rw [hqx, ← map_pow]
    have : (⟨y⁻¹ * x, hoM⟩ : ↥M) ^ 2 ^ m = 1 := Subtype.ext (by simpa using hm')
    rw [this, map_one]
  have h3 : (q ⟨x, hxM⟩) ^ 3 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨x, hxM⟩ : ↥M) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hxk)
    rw [this, map_one]
  have hcop : Nat.Coprime (3 ^ k) (2 ^ m) := Nat.Coprime.pow _ _ (by norm_num)
  have hq1 : q ⟨x, hxM⟩ = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h3)
      (orderOf_dvd_of_pow_eq_one h2k))
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hq1)

variable {T Mc M : Subgroup G}

theorem mem_Y153_of_threePower (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (hker : ∀ w ∈ imageOTwoQuot M (Y153 Mc M),
      starAct M (VZ T M) h.le_normalizer h.hyp14117.pCoreOf_le_centralizer w = 1 → w = 1)
    {x : G} (hxM : x ∈ M) {k : ℕ} (hxk : x ^ 3 ^ k = 1) : x ∈ Y153 Mc M := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · rw [hk0, pow_zero, pow_one] at hxk
    rw [hxk]
    exact Subgroup.one_mem _
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := h.le_normalizer
  have hOC : pCoreOf 2 M ≤ Subgroup.centralizer (VZ T M : Set G) :=
    h.hyp14117.pCoreOf_le_centralizer
  have hYM : Y153 Mc M ≤ M := Y153_le Mc M
  have hMY := le_normalizer_Y153 Mc M
  obtain ⟨⟨-, -, hexp⟩, -⟩ := Hyp153.Ystar_structure h113 h
  set Yq := imageOTwoQuot M (Y153 Mc M) with hYq
  set xs : OTwoQuot M := QuotientGroup.mk ⟨x, hxM⟩ with hxs
  have hxsk : xs ^ 3 ^ k = 1 := by
    rw [hxs, ← QuotientGroup.mk_pow]
    have : (⟨x, hxM⟩ : ↥M) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hxk)
    rw [this, QuotientGroup.mk_one]
  have hρ : starAct M (VZ T M) hMV hOC xs ∈ autOn (Y153 Mc M) (VZ T M) := by
    rw [h.autOn_Y153 h113]
    refine mem_oTwoUpper_of_odd (mem_autOn_iff_exists.mpr ⟨x, hMV hxM, hxM, rfl⟩) ?_
    have hodd3k : Odd (3 ^ k) := Odd.pow (by decide)
    refine Odd.of_dvd_nat hodd3k (orderOf_dvd_of_pow_eq_one ?_)
    rw [← map_pow, hxsk, map_one]
  rw [← map_starAct hMV hOC hYM] at hρ
  obtain ⟨ys, hys, hysρ⟩ := Subgroup.mem_map.mp hρ
  have hcsker : starAct M (VZ T M) hMV hOC (ys⁻¹ * xs) = 1 := by
    rw [map_mul, map_inv, hysρ, inv_mul_cancel]
  have hcs : ys⁻¹ * xs ∈ (starAct M (VZ T M) hMV hOC).ker := hcsker
  rw [ker_starAct] at hcs
  obtain ⟨c, hcM, hcC, hcc⟩ := mem_imageOTwoQuot_iff.mp hcs
  set cs : OTwoQuot M := ys⁻¹ * xs with hcsdef
  have hcomm : ∀ e ∈ Yq, e * cs = cs * e := by
    intro e he
    obtain ⟨y, hyM, hyY, rfl⟩ := mem_imageOTwoQuot_iff.mp he
    rw [← hcc]
    exact (mk_commute_iff ⟨y, hyM⟩ ⟨c, hcM⟩).mpr (h.commutator_Y153_le hyY hcC)
  have hysY : ys * cs = xs := by rw [hcsdef]; group
  have hys3 : ys ^ 3 = 1 := by
    simpa using congrArg Subtype.val (hexp ⟨ys, hys⟩)
  have hysk : ys ^ 3 ^ k = 1 := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ, pow_mul', hys3, one_pow]
  have hcsk : cs ^ 3 ^ k = 1 := by
    have h1 : (ys * cs) ^ 3 ^ k = ys ^ 3 ^ k * cs ^ 3 ^ k := Commute.mul_pow (hcomm ys hys) _
    rw [hysY, hxsk, hysk, one_mul] at h1
    exact h1.symm
  have hcs1 : cs = 1 := by
    by_contra hne
    have hdvd : orderOf cs ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hcsk
    obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hjeq
      exact hne (orderOf_eq_one_iff.mp hjeq)
    have h3dvd : 3 ∣ Nat.card (Subgroup.zpowers cs) := by
      rw [Nat.card_zpowers, hjeq]
      exact dvd_pow_self 3 hj0
    obtain ⟨g, hg3⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers cs)) 3 h3dvd
    have hwcs : (g : OTwoQuot M) ∈ Subgroup.zpowers cs := g.2
    have hw3 : (g : OTwoQuot M) ^ 3 = 1 := by
      have := pow_orderOf_eq_one g
      rw [hg3] at this
      simpa using congrArg Subtype.val this
    have hw1 : (g : OTwoQuot M) ≠ 1 := by
      intro h1
      have : g = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hg3
      omega
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hwcs
    have hwcomm : ∀ e ∈ Yq, e * (g : OTwoQuot M) = (g : OTwoQuot M) * e := by
      intro e he
      rw [← hn]
      exact (Commute.zpow_right (hcomm e he) n).eq
    have hwker : starAct M (VZ T M) hMV hOC (g : OTwoQuot M) = 1 := by
      rw [← hn, map_zpow, hcsker, one_zpow]
    by_cases hwY : (g : OTwoQuot M) ∈ Yq
    · exact hw1 (hker _ hwY hwker)
    · obtain ⟨E, hEY, hE, hE9⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3)
        (k := 2) (two_le_pRank_Ystar h113 h)
      have h3r := three_le_pRank_of_commuting hE (by simpa using hE9) hw3
        (fun e he => hwcomm e (hEY he)) (fun hzE => hwY (hEY hzE))
      exact absurd (pRank_OTwoQuot_le h) (by omega)
  have hxY : xs ∈ Yq := by
    have : xs = ys := by rw [← hysY, hcs1, mul_one]
    rw [this]
    exact hys
  obtain ⟨y', hy'M, hy'Y, hy'x⟩ := mem_imageOTwoQuot_iff.mp hxY
  refine mem_of_mul_mem_pCoreOf_pow hYM hMY hxM hy'Y hxk ?_
  have h1 : (⟨y', hy'M⟩ : ↥M)⁻¹ * ⟨x, hxM⟩ ∈ CFSG.Open.pCore 2 ↥M := QuotientGroup.eq.mp hy'x
  exact (Subgroup.mem_map_iff_mem M.subtype_injective).mpr h1

theorem mem_centralizer_of_starAct_eq_one (h : Hyp153 G T Mc M) {m : G} (hmM : m ∈ M)
    (hm : starAct M (VZ T M) h.le_normalizer h.hyp14117.pCoreOf_le_centralizer
      (QuotientGroup.mk ⟨m, hmM⟩) = 1) : m ∈ Subgroup.centralizer (VZ T M : Set G) := by
  have hker : (QuotientGroup.mk ⟨m, hmM⟩ : OTwoQuot M) ∈
      (starAct M (VZ T M) h.le_normalizer h.hyp14117.pCoreOf_le_centralizer).ker := hm
  rw [ker_starAct] at hker
  obtain ⟨c, hcM, hcC, hcm⟩ := mem_imageOTwoQuot_iff.mp hker
  have h1 : (⟨c, hcM⟩ : ↥M)⁻¹ * ⟨m, hmM⟩ ∈ CFSG.Open.pCore 2 ↥M := QuotientGroup.eq.mp hcm
  have h2 : c⁻¹ * m ∈ pCoreOf 2 M := (Subgroup.mem_map_iff_mem M.subtype_injective).mpr h1
  have h3 := h.hyp14117.pCoreOf_le_centralizer h2
  have e : m = c * (c⁻¹ * m) := by group
  rw [e]
  exact Subgroup.mul_mem _ hcC.2 h3

theorem pCoreOf_Y153_le_pCoreOf_M (Mc M : Subgroup G) : pCoreOf 2 (Y153 Mc M) ≤ pCoreOf 2 M :=
  le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans (Y153_le Mc M))
    (fun _ hm => normalizer_le_normalizer_pCoreOf 2 _ (le_normalizer_Y153 Mc M hm))
    (pCoreOf_isPGroup 2 _)

end ClaimA

end S153D

namespace Hyp15310

open S153D

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp : Subgroup G} {t : G}

theorem Ystar_ker_eq_bot (h113 : StageLemma14113) (h : Hyp15310 G T Mc M V₁ V₂ Yp t)
    (hr : CFSG.Open.pRank 3 Yp = 1) :
    ∀ w ∈ imageOTwoQuot M (Y153 Mc M),
      starAct M (VZ T M) h.hyp.le_normalizer h.hyp.hyp14117.pCoreOf_le_centralizer w = 1 →
        w = 1 := by
  intro w hwY hw1
  have h2 := h.case_two_of_pRank_one h113 hr
  have hYpY : Yp ≤ Y153 Mc M := h.Yp_le_Y153
  have hYpM : Yp ≤ M := hYpY.trans (Y153_le Mc M)
  obtain ⟨z, hzM, hzY, rfl⟩ := mem_imageOTwoQuot_iff.mp hwY
  have hzC : z ∈ Subgroup.centralizer (VZ T M : Set G) :=
    mem_centralizer_of_starAct_eq_one h.hyp hzM hw1
  have hzK : z ∈ Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G) :=
    ⟨hzY, Subgroup.centralizer_le h.decomp.le₁ hzC⟩
  have hz : z ∈ Yp ⊔ pCoreOf 2 (Y153 Mc M) := by
    have := Hyp153.Yplus_base_le h113 h.hyp hzK
    rwa [← h2.2] at this
  have hO₂YM : pCoreOf 2 (Y153 Mc M) ≤ M := (pCoreOf_le 2 _).trans (Y153_le Mc M)
  have hzP : (QuotientGroup.mk ⟨z, hzM⟩ : OTwoQuot M) ∈ imageOTwoQuot M Yp := by
    have hmem : (QuotientGroup.mk ⟨z, hzM⟩ : OTwoQuot M) ∈
        imageOTwoQuot M (Yp ⊔ pCoreOf 2 (Y153 Mc M)) := mem_imageOTwoQuot_iff.mpr ⟨z, hzM, hz, rfl⟩
    rw [imageOTwoQuot_sup hYpM hO₂YM] at hmem
    have hbot : imageOTwoQuot M (pCoreOf 2 (Y153 Mc M)) = ⊥ := by
      refine eq_bot_iff.mpr fun u hu => ?_
      obtain ⟨o, hoM, hoO, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
      exact (mk_eq_one_iff_mem_pCoreOf ⟨o, hoM⟩).mpr (pCoreOf_Y153_le_pCoreOf_M Mc M hoO)
    rw [hbot, sup_bot_eq] at hmem
    exact hmem
  obtain ⟨φ, -⟩ := h.hyp.exists_mulEquiv_imageOTwoQuot_of_le_Y153 h113 hYpY
  have hP₁card : Nat.card ↥(imageOTwoQuot M Yp) = 3 :=
    (Nat.card_congr φ.toEquiv).symm.trans (Hyp153.card_OTwoQuot_of_pRank_one h113 h.hyp hYpY hr)
  by_contra hne
  have hzp : Subgroup.zpowers (QuotientGroup.mk ⟨z, hzM⟩ : OTwoQuot M) ≤ imageOTwoQuot M Yp :=
    Subgroup.zpowers_le.mpr hzP
  have hord : orderOf (QuotientGroup.mk ⟨z, hzM⟩ : OTwoQuot M) = 3 := by
    have hd : orderOf (QuotientGroup.mk ⟨z, hzM⟩ : OTwoQuot M) ∣ 3 :=
      hP₁card ▸ Subgroup.orderOf_dvd_natCard _ hzP
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hne
    · exact h1
  have heq : Subgroup.zpowers (QuotientGroup.mk ⟨z, hzM⟩ : OTwoQuot M) = imageOTwoQuot M Yp :=
    Subgroup.eq_of_le_of_card_ge hzp (by rw [Nat.card_zpowers, hord, hP₁card])
  obtain ⟨hV, L₁, L₂, tb, hS, hV₁, hV₂, y, hy, hyY, hyL, hyord⟩ :=
    h.hyp.exists_mem_Yplus_acts h113 h.decomp
  have hyYp : y ∈ Yp := by rw [h2.2]; exact hyY
  have hyM : y ∈ M := hYpM hyYp
  have hyP : (QuotientGroup.mk ⟨y, hyM⟩ : OTwoQuot M) ∈ imageOTwoQuot M Yp :=
    mem_imageOTwoQuot_iff.mpr ⟨y, hyM, hyYp, rfl⟩
  rw [← heq] at hyP
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hyP
  have hy1 : starAct M (VZ T M) h.hyp.le_normalizer h.hyp.hyp14117.pCoreOf_le_centralizer
      (QuotientGroup.mk ⟨y, hyM⟩) = 1 := by
    rw [← hn, map_zpow, hw1, one_zpow]
  have hyC := mem_centralizer_of_starAct_eq_one h.hyp hyM hy1
  have hconv : convI hV ⟨y, hy⟩ = 1 := by
    ext w
    apply IntMod.val_injective
    rw [convI_apply_val]
    have hc : (w : IntMod (VZ T M) hV).val * y = y * (w : IntMod (VZ T M) hV).val :=
      Subgroup.mem_centralizer_iff.mp hyC _ w.val_mem
    show y * w.val * y⁻¹ = w.val
    rw [← hc]
    group
  rw [hconv, orderOf_one] at hyord
  omega

theorem yp_eq_oPrimeResidual (h113 : StageLemma14113) (h : Hyp15310 G T Mc M V₁ V₂ Yp t)
    (hr : CFSG.Open.pRank 3 Yp = 1) {I : Subgroup G} (hI : IsHPlus Yp (Sgp153 T V₁) M I) :
    Yp = oPrimeResidualOf 3 (M ⊓ I) := by
  have h2 := h.case_two_of_pRank_one h113 hr
  have h3 := h.lemma_15_3_11_three h113 h2 hI
  apply le_antisymm
  · rw [h.theta_eq h113 hI]
    exact Subgroup.closure_mono fun x hx => ⟨hx.1, 1, by rw [pow_one]; exact hx.2⟩
  · refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxMI, k, hk⟩
    have hxk : x ^ 3 ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
    have hxY : x ∈ Y153 Mc M :=
      mem_Y153_of_threePower h113 h.hyp (Ystar_ker_eq_bot h113 h hr) hxMI.1 hxk
    have hodd : Odd (orderOf x) := by rw [hk]; exact Odd.pow (by decide)
    rw [h3.1]
    exact mem_oTwoUpper_of_odd ⟨hxY, hxMI.2⟩ hodd

end Hyp15310

end CFSG.Quasithin

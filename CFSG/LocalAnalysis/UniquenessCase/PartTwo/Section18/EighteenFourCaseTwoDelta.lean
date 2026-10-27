module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirty
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NatRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenBranchA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourWeak

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6 CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.CGT.PushingUp
open scoped Pointwise commutatorElement
open CFSG.GroupTheory (mQuot_top_eq_rkIdx)

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V : Subgroup G} {L K : Subgroup G}

@[expose] def Gap_18_4_ii_G26 (D : Data G) (V : Subgroup G) (hV : IsElemAbelian 2 V)
    (X : Subgroup (MulAut (Vtil ⊥ V hV))) : Prop :=
  Hyp125 D ⊥ V → IsOmegaPlus ↥X 4 2 →
    SumOfNat (fun H U Z => NatOmegaPlus H U Z 4 2) X ⊤ ⊥ 2 →
    mBar D.M ⊥ V hV = 4 →
    ∀ t ∈ Mbar D.M ⊥ V hV, orderOf t = 2 →
      E3.mQuot ⊤ (CFSG.Quasithin.fixV (Subgroup.zpowers t)) = 4 →
        1 < CFSG.Open.pRank 5
          (D.M ⊓ Subgroup.normalizer
            (preTil ⊥ V hV (CFSG.Quasithin.fixV (Subgroup.zpowers t)) : Set G))

theorem normalizer_le_of_pRank (D : Data G) (h61 : UC6.R6_1 D) {U : Subgroup G}
    (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U) (h5sig : 5 ∈ D.sig)
    (hrank : 1 < CFSG.Open.pRank 5 (D.M ⊓ Subgroup.normalizer (U : Set G))) :
    normalizer (U : Set G) ≤ D.M := by
  obtain ⟨E, hE, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 5) (by norm_num)
    (D.M ⊓ Subgroup.normalizer (U : Set G))
  have hE2 : IsPGroup 5 E := by
    obtain ⟨n, hn⟩ := hEel.isPGroup.exists_card_eq
    exact IsPGroup.of_card (n := n) hn
  have hEnc : ¬ IsCyclic E := by
    intro hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥E)
    have hg5 : g ^ 5 = 1 := Subtype.ext (by simpa using hEel.2 (g : G) g.2)
    have hdvd : orderOf g ∣ 5 := orderOf_dvd_of_pow_eq_one hg5
    have hcarddvd : Nat.card E ∣ 5 := by rw [← hg]; exact hdvd
    have h25 : 25 ∣ Nat.card E := by
      rw [hEcard]
      exact pow_dvd_pow 5 (by omega : 2 ≤ CFSG.Open.pRank 5
        (D.M ⊓ Subgroup.normalizer (U : Set G)))
    have : 25 ∣ 5 := h25.trans hcarddvd
    norm_num at this
  exact normalizer_le_of_noncyclic D h61 h5sig (hE.trans inf_le_left) hE2 hEnc hU1 hU2
    (hE.trans inf_le_right)


theorem mQuot_eq_rkIdx_imgTil {V : Subgroup G} (hV : IsElemAbelian 2 V) {U : Subgroup G}
    (hUV : U ≤ V) :
    E3.mQuot V U = rkIdx (imgTil (⊥ : Subgroup G) V hV U) := by
  have hker : (mkTil (⊥ : Subgroup G) V hV).ker = ⊥ := by
    change (QuotientGroup.mk' (modNull (⊥ : Subgroup G) V hV)).ker = ⊥
    rw [QuotientGroup.ker_mk']
    ext x
    rw [Subgroup.mem_bot, mem_modNull, Subgroup.mem_bot]
    constructor
    · intro h
      exact IntMod.val_injective (by simpa using h)
    · intro h
      rw [h]
      rfl
  let e : IntMod V hV ≃* Vtil (⊥ : Subgroup G) V hV :=
    MulEquiv.ofBijective (mkTil (⊥ : Subgroup G) V hV)
      ⟨(MonoidHom.ker_eq_bot_iff (mkTil (⊥ : Subgroup G) V hV)).mp hker,
        mkTil_surjective ⊥ V hV⟩
  have he : (e : IntMod V hV →* Vtil (⊥ : Subgroup G) V hV) = mkTil ⊥ V hV := rfl
  have h1 : rkIdx (imgTil (⊥ : Subgroup G) V hV U) = rkIdx (intSub V hV U) := by
    have himg : imgTil (⊥ : Subgroup G) V hV U =
        (intSub V hV U).map (e : IntMod V hV →* Vtil (⊥ : Subgroup G) V hV) := rfl
    rw [himg]
    exact CFSG.Quasithin.E3.rkIdx_map_equiv e (intSub V hV U)
  rw [h1, E3.mQuot_eq_rkIdx]
  rfl

theorem rk_vtil_eq_sixteen {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {X : Subgroup (MulAut (Vtil (⊥ : Subgroup G) V hV))}
    (hsum : SumOfNat (fun H U Z => NatOmegaPlus H U Z 4 2) X ⊤ ⊥ 2) :
    rk (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV)) = 16 := by
  have hnat : ∀ I : Subgroup (Vtil (⊥ : Subgroup G) V hV),
      NatOmegaPlus X I ⊥ 4 2 → rk ↥I = 8 := by
    intro I hI
    have h := s16c1610_rk_natOmegaPlus hI
    omega
  have h := s16c1610_rk_sumOfNat_two hnat hsum
  rw [h]

theorem A5Config18.mem_deltaEleven_of_case_two (c : A5Config18 D V₀ V L K)
    (h2 : CaseTwo18 D V L K c.elemAbelian)
    (hG26 : Gap_18_4_ii_G26 D V c.elemAbelian
      (barSub (⊥ : Subgroup G) V c.elemAbelian L ⊔ barSub (⊥ : Subgroup G) V c.elemAbelian K))
    (h111 : W3Thm111 G) (h61 : UC6.R6_1 D)
    {U : Subgroup G} (hUV : U ≤ V) (hmU : E3.mQuot V U = 4)
    (hC : ¬ Subgroup.centralizer (U : Set G) ≤ D.M) :
    U ∈ deltaEleven D.M V := by
  have hV0 : V₀ = ⊥ := c.v0
  subst V₀
  have hV := c.elemAbelian
  have hp125 : Hyp125 D ⊥ V := c.pair.data.hyp.hyp125
  have hpF : PairFacts D.M ⊥ V := hp125.pairFacts
  have h5sig : 5 ∈ D.sig := c.pair.data.hyp.hp
  set Xbar : Subgroup (MulAut (Vtil (⊥ : Subgroup G) V hV)) :=
    barSub (⊥ : Subgroup G) V hV L ⊔ barSub (⊥ : Subgroup G) V hV K with hXbardef
  have hX : IsOmegaPlus ↥Xbar 4 2 := h2.2.1
  have hsum : SumOfNat (fun H U Z => NatOmegaPlus H U Z 4 2) Xbar ⊤ ⊥ 2 := h2.2.2
  have hG26' := hG26 hp125 hX hsum c.numerics.1
  have hrk16 : rk (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV)) = 16 :=
    rk_vtil_eq_sixteen hV hsum
  have hVrk : rk ↥V = 16 := by
    have h := s15_Infra_mSub_eq_rk_imgTil_add (⊥ : Subgroup G) V V hV le_rfl
    rw [s15_Infra_imgTil_top, inf_bot_eq, show mSub (⊥ : Subgroup G) = 0 from rk_bot,
      add_zero] at h
    rw [← hrk16]
    change mSub V = rk (⊤ : Subgroup (Vtil (⊥ : Subgroup G) V hV))
    exact h
  have hUt : U ≠ ⊥ := by
    intro hbot
    have h1 : E3.mQuot V U = 16 := by
      rw [hbot, s15_FiveTen_mQuot_bot_eq_rk, hVrk]
    omega
  have hOpp : Opp 2 (D.M ⊓ Subgroup.centralizer (U : Set G)) ≤
      Subgroup.centralizer (V : Set G) := by
    show CFSG.RankThree.PartOne.pElementSubgroup 2
      (D.M ⊓ Subgroup.centralizer (U : Set G)) ≤ Subgroup.centralizer (V : Set G)
    unfold CFSG.RankThree.PartOne.pElementSubgroup
    rw [Subgroup.closure_le]
    rintro x ⟨hxY, k, hxk⟩
    by_contra hxV
    obtain ⟨hxM, hxU⟩ := Subgroup.mem_inf.1 hxY
    have hxS : x ∈ stabTil (⊥ : Subgroup G) V :=
      le_stabTil hpF.le_normalizer hpF.le_normalizer₀ hxM
    set xb : MulAut (Vtil (⊥ : Subgroup G) V hV) := actTil ⊥ V hV ⟨x, hxS⟩ with hxbdef
    have hxbM : xb ∈ Mbar D.M ⊥ V hV := actTil_mem_barSub ⊥ V hV hxM hxS
    have hxb1 : xb ≠ 1 := by
      intro h1
      apply hxV
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro v hv
      have h2 := (actTil_eq_one_iff ⊥ V hV ⟨x, hxS⟩).1 h1 v hv
      rw [Subgroup.mem_bot] at h2
      calc v * x = (x * v * x⁻¹) * x := by
            rw [show x * v * x⁻¹ = (x * v * x⁻¹ * v⁻¹) * v from by group, h2, one_mul]
        _ = x * v := by group
    have hxpow : x ^ 2 ^ k = 1 := hxk ▸ pow_orderOf_eq_one x
    have hxbpow : xb ^ 2 ^ k = 1 := by
      rw [hxbdef]
      rw [← map_pow]
      have h1 : (⟨x, hxS⟩ : ↥(stabTil (⊥ : Subgroup G) V)) ^ 2 ^ k = 1 :=
        Subtype.ext hxpow
      rw [h1, map_one]
    have hxb2 : IsPGroup 2 (Subgroup.zpowers xb) :=
      IsPGroup.of_card_dvd_pow (n := k) (by
        rw [Nat.card_zpowers]
        exact orderOf_dvd_of_pow_eq_one hxbpow)
    have hzb1 : Subgroup.zpowers xb ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hxb1
    have hbound : mBar D.M ⊥ V hV ≤ rkIdx (CFSG.Quasithin.fixV (Subgroup.zpowers xb)) := by
      have h := CFSG.Quasithin.E3.mParam_le_rkIdx_fixV (X := Mbar D.M ⊥ V hV)
        (A := Subgroup.zpowers xb) (Subgroup.zpowers_le.mpr hxbM) hxb2 hzb1
      rwa [show CFSG.Quasithin.E3.mParam (Mbar D.M ⊥ V hV) = mBar D.M ⊥ V hV from rfl] at h
    have hfixU : imgTil (⊥ : Subgroup G) V hV U ≤ CFSG.Quasithin.fixV (Subgroup.zpowers xb) := by
      intro w hw
      rw [mem_imgTil] at hw
      obtain ⟨u, huU, rfl⟩ := hw
      rw [CFSG.Quasithin.mem_fixV_zpowers_iff_apply]
      have hcomm : u.val * x = x * u.val :=
        Subgroup.mem_centralizer_iff.mp hxU u.val huU
      have hux : x * u.val * x⁻¹ = u.val := by
        calc x * u.val * x⁻¹ = (u.val * x) * x⁻¹ := by rw [hcomm]
          _ = u.val := by group
      rw [show xb (mkTil (⊥ : Subgroup G) V hV u) =
          mkTil (⊥ : Subgroup G) V hV (actStab (⊥ : Subgroup G) V hV ⟨x, hxS⟩ u) from
        actTil_mk ⊥ V hV ⟨x, hxS⟩ u]
      congr 1
      exact IntMod.val_injective (by rw [actStab_apply_val]; exact hux)
    have hImgIdx : rkIdx (imgTil (⊥ : Subgroup G) V hV U) = 4 := by
      rw [← mQuot_eq_rkIdx_imgTil hV hUV, hmU]
    have h4xb : rkIdx (CFSG.Quasithin.fixV (Subgroup.zpowers xb)) = 4 := by
      have h1 := hbound
      rw [c.numerics.1] at h1
      have h2 := CFSG.Quasithin.rkIdx_anti hfixU
      rw [hImgIdx] at h2
      omega
    obtain ⟨t, htzp, htord⟩ :=
      CFSG.Quasithin.E3.exists_orderOf_two_of_isPGroup hxb2 hzb1
    have htM : t ∈ Mbar D.M ⊥ V hV := Subgroup.zpowers_le.mpr hxbM htzp
    have htne : t ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at htord
      omega
    have htfix : CFSG.Quasithin.fixV (Subgroup.zpowers xb) ≤
        CFSG.Quasithin.fixV (Subgroup.zpowers t) := by
      intro w hw
      rw [mem_fixV] at hw ⊢
      intro z hz
      exact hw z (Subgroup.zpowers_le.2 htzp hz)
    have htidx : rkIdx (CFSG.Quasithin.fixV (Subgroup.zpowers t)) = 4 := by
      have ht2 : IsPGroup 2 (Subgroup.zpowers t) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htord, pow_one])
      have htz1 : Subgroup.zpowers t ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr htne
      have h1 : mBar D.M ⊥ V hV ≤ rkIdx (CFSG.Quasithin.fixV (Subgroup.zpowers t)) := by
        have h := CFSG.Quasithin.E3.mParam_le_rkIdx_fixV (X := Mbar D.M ⊥ V hV)
          (A := Subgroup.zpowers t) (Subgroup.zpowers_le.mpr htM) ht2 htz1
        rwa [show CFSG.Quasithin.E3.mParam (Mbar D.M ⊥ V hV) = mBar D.M ⊥ V hV from rfl] at h
      rw [c.numerics.1] at h1
      have h2 := CFSG.Quasithin.rkIdx_anti htfix
      rw [h4xb] at h2
      omega
    have hmqt : E3.mQuot ⊤ (CFSG.Quasithin.fixV (Subgroup.zpowers t)) = 4 := by
      rw [mQuot_top_eq_rkIdx, htidx]
    have hpr := hG26' t htM htord hmqt
    have hfiximg : imgTil (⊥ : Subgroup G) V hV U ≤ CFSG.Quasithin.fixV (Subgroup.zpowers t) :=
      hfixU.trans htfix
    have hle : U ≤ preTil (⊥ : Subgroup G) V hV (CFSG.Quasithin.fixV (Subgroup.zpowers t)) := by
      have h1 : U ≤ preTil (⊥ : Subgroup G) V hV (imgTil (⊥ : Subgroup G) V hV U) := by
        have h := le_preTil_imgTil (⊥ : Subgroup G) V hV U
        rwa [inf_eq_left.mpr hUV] at h
      refine h1.trans ?_
      intro g hg
      rw [mem_preTil] at hg ⊢
      obtain ⟨xx, rfl, hxq⟩ := hg
      exact ⟨xx, rfl, hfiximg hxq⟩
    have hpV : preTil (⊥ : Subgroup G) V hV (CFSG.Quasithin.fixV (Subgroup.zpowers t)) ≤ V :=
      preTil_le ⊥ V hV _
    have hm2 : E3.mQuot V
        (preTil (⊥ : Subgroup G) V hV (CFSG.Quasithin.fixV (Subgroup.zpowers t))) = 4 := by
      rw [mQuot_eq_rkIdx_imgTil hV hpV, imgTil_preTil, htidx]
    have hUpre : U = preTil (⊥ : Subgroup G) V hV (CFSG.Quasithin.fixV (Subgroup.zpowers t)) := by
      have hadd := E3.mQuot_add hle hpV
      rw [hmU, hm2] at hadd
      have hzero : E3.mQuot
          (preTil (⊥ : Subgroup G) V hV (CFSG.Quasithin.fixV (Subgroup.zpowers t))) U = 0 := by
        omega
      exact (E3.mQuot_eq_zero_iff (hV := hV.isPGroup.to_le hpV) hle).mp hzero
    rw [← hUpre] at hpr
    have hNle : normalizer (U : Set G) ≤ D.M :=
      normalizer_le_of_pRank D h61 hUt (hV.isPGroup.to_le hUV) h5sig hpr
    exact hC ((Subgroup.centralizer_le_normalizer (U : Set G)).trans hNle)
  refine mem_deltaEleven.2 ⟨?_, ?_⟩
  · exact ⟨hUV, hUt, hC, hOpp⟩
  ·
    have hset : Setting11 D.M V (D.T ⊓ Subgroup.centralizer (V : Set G)) :=
      S17.setting11_of_hyp125 D hp125 rfl
    have hr4 : (4 : ℕ∞) ≤ rMV D.M V := by
      have hm3 : MBarGT D.M ⊥ V 3 :=
        (hpF.mBarGT_iff_lt_mBar 3).2 (by rw [c.numerics.1]; norm_num)
      have hm2 : MBarGT D.M ⊥ V 2 :=
        (hpF.mBarGT_iff_lt_mBar 2).2 (by rw [c.numerics.1]; norm_num)
      have h3 : (3 : ℕ∞) < rMV D.M V :=
        h111 D.M V (D.T ⊓ Subgroup.centralizer (V : Set G)) hset hm2 3 hm3
      exact Order.succ_le_of_lt h3
    have hub : rMV D.M V ≤ (4 : ℕ∞) := by
      have h := rMV_le_mQuot D.M V U hUV hC
      rwa [hmU] at h
    rw [le_antisymm hub hr4]
    exact_mod_cast hmU

theorem A5Config18.four_le_rMV_of_case_two (c : A5Config18 D V₀ V L K)
    (h111 : W3Thm111 G) : (4 : ℕ∞) ≤ rMV D.M V := by
  have hV0 : V₀ = ⊥ := c.v0
  subst V₀
  have hV := c.elemAbelian
  have hp125 : Hyp125 D ⊥ V := c.pair.data.hyp.hyp125
  have hpF : PairFacts D.M ⊥ V := hp125.pairFacts
  have hset : Setting11 D.M V (D.T ⊓ Subgroup.centralizer (V : Set G)) :=
    S17.setting11_of_hyp125 D hp125 rfl
  have hm3 : MBarGT D.M ⊥ V 3 :=
    (hpF.mBarGT_iff_lt_mBar 3).2 (by rw [c.numerics.1]; norm_num)
  have hm2 : MBarGT D.M ⊥ V 2 :=
    (hpF.mBarGT_iff_lt_mBar 2).2 (by rw [c.numerics.1]; norm_num)
  have h3 : (3 : ℕ∞) < rMV D.M V :=
    h111 D.M V (D.T ⊓ Subgroup.centralizer (V : Set G)) hset hm2 3 hm3
  exact Order.succ_le_of_lt h3

theorem A5Config18.four_lt_rMV_of_case_two
    (c : A5Config18 D V₀ V L K) (h2 : CaseTwo18 D V L K c.elemAbelian)
    (hG26 : Gap_18_4_ii_G26 D V c.elemAbelian
      (barSub (⊥ : Subgroup G) V c.elemAbelian L ⊔ barSub (⊥ : Subgroup G) V c.elemAbelian K))
    (h111 : W3Thm111 G) (h61 : UC6.R6_1 D) (hSg : UC6S846.SigmaStd D)
    (hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G) :
    (4 : ℕ∞) < rMV D.M V := by
  by_contra hcon
  push Not at hcon
  have h4 := c.four_le_rMV_of_case_two h111
  have hr : rMV D.M V = 4 := le_antisymm hcon h4
  have hV0 : V₀ = ⊥ := c.v0
  subst V₀
  have hV := c.elemAbelian
  have hp125 : Hyp125 D ⊥ V := c.pair.data.hyp.hyp125
  have hset : Setting11 D.M V (D.T ⊓ Subgroup.centralizer (V : Set G)) :=
    S17.setting11_of_hyp125 D hp125 rfl
  by_cases hne : ∃ U : Subgroup G, U ≤ V ∧ ¬ Subgroup.centralizer (U : Set G) ≤ D.M
  · obtain ⟨U, hUV, hUC, hUrmv⟩ := s16c1614_exists_mQuot_eq_rMV D hne
    have hU4 : E3.mQuot V U = 4 := by
      have h : (E3.mQuot V U : ℕ∞) = (4 : ℕ∞) := by rw [hUrmv, hr]
      exact_mod_cast h
    have hUΔ := c.mem_deltaEleven_of_case_two h2 hG26 h111 h61 hUV hU4 hUC
    obtain ⟨L₀, T₀, Y₀, hY₀, hL₀eq, hL₀M⟩ := exists_mem_elevenBlocks hset hK hUΔ.1
    have hL₀block : IsBlockOfInX (Subgroup.centralizer (U : Set G)) L₀ := by
      refine isBlockOfInX_of_mem_elevenBlocks ⟨T₀, Y₀, hY₀, hL₀eq, hL₀M⟩
    have hm1 : 1 < mBar D.M ⊥ V hset.isElemAbelian := by
      rw [show mBar D.M ⊥ V hset.isElemAbelian = mBar D.M ⊥ V hV from rfl, c.numerics.1]
      norm_num
    have hr1 : 1 < rMV D.M V := by rw [hr]; norm_num
    obtain ⟨n, hn1, hnat, hrveq, hCVL, huniq, hidx, hHall, hHallprops⟩ :=
      eleven_ten_of_one_lt hset hr1 hm1 hUΔ hL₀block hL₀M
    have hn4 : (n : ℕ∞) = 4 := by rw [← hrveq, hr]
    have hn : n = 4 := by exact_mod_cast hn4
    subst hn
    have hidx17 : (L₀ ⊓ D.M).relIndex L₀ = 17 := by rw [hidx]; norm_num
    obtain ⟨X, hXhall⟩ := hHall
    have hXprops := hHallprops X hXhall
    have hXcard : Nat.card X = 15 := by rw [hXprops.2.1]; norm_num
    have h5dvdX : 5 ∣ Nat.card X := by rw [hXcard]; norm_num
    obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 5 h5dvdX
    have hyXL : (y : G) ∈ X := y.2
    have hyLM : (y : G) ∈ L₀ ⊓ D.M := hXhall.1 hyXL
    have hyL : (y : G) ∈ L₀ := hyLM.1
    have hyM : (y : G) ∈ D.M := hyLM.2
    have hyordG : orderOf (y : G) = 5 := by
      simpa using hyord
    let H : Subgroup ↥L₀ := (L₀ ⊓ D.M).subgroupOf L₀
    let yL : ↥L₀ := ⟨(y : G), hyL⟩
    have hyL_mem : yL ∈ H := (Subgroup.mem_subgroupOf).2 hyLM
    have hyLord : orderOf yL = 5 := by
      simpa [yL] using hyordG
    have hYp : IsPGroup 5 (Subgroup.zpowers yL) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyLord, pow_one])
    have hcardL : Nat.card (↥L₀ ⧸ H) = 17 := by
      rw [← Subgroup.index_eq_card]
      exact hidx17
    have hmod := hYp.card_modEq_card_fixedPoints (α := ↥L₀ ⧸ H)
    rw [hcardL] at hmod
    have h2mod : Nat.card (MulAction.fixedPoints (Subgroup.zpowers yL) (↥L₀ ⧸ H)) % 5 = 2 := by
      rw [Nat.ModEq] at hmod
      rw [show (17 : ℕ) % 5 = 2 from by norm_num] at hmod
      omega
    have hfixge : 2 ≤ Nat.card (MulAction.fixedPoints (Subgroup.zpowers yL) (↥L₀ ⧸ H)) := by
      have hx := Nat.div_add_mod (Nat.card (MulAction.fixedPoints (Subgroup.zpowers yL)
        (↥L₀ ⧸ H))) 5
      omega
    have htriv : (QuotientGroup.mk (1 : ↥L₀) : ↥L₀ ⧸ H) ∈
        MulAction.fixedPoints (Subgroup.zpowers yL) (↥L₀ ⧸ H) := by
      rw [MulAction.mem_fixedPoints]
      intro z
      have hzH : (z : ↥L₀) ∈ H := Subgroup.zpowers_le.mpr hyL_mem z.2
      show z • (QuotientGroup.mk (1 : ↥L₀) : ↥L₀ ⧸ H) = QuotientGroup.mk (1 : ↥L₀)
      rw [show z • (QuotientGroup.mk (1 : ↥L₀) : ↥L₀ ⧸ H) =
          QuotientGroup.mk ((z : ↥L₀) * 1) from rfl, mul_one]
      exact QuotientGroup.eq.mpr (by simpa using hzH)
    obtain ⟨q, hqfix, hqne⟩ : ∃ q ∈ MulAction.fixedPoints (Subgroup.zpowers yL) (↥L₀ ⧸ H),
        q ≠ QuotientGroup.mk (1 : ↥L₀) := by
      by_contra h
      push Not at h
      have hsub : MulAction.fixedPoints (Subgroup.zpowers yL) (↥L₀ ⧸ H) ⊆
          {QuotientGroup.mk (1 : ↥L₀)} := fun q hq => by
        have := h q hq
        simpa using this
      have hcardle : Nat.card (MulAction.fixedPoints (Subgroup.zpowers yL) (↥L₀ ⧸ H)) ≤ 1 := by
        calc Nat.card (MulAction.fixedPoints (Subgroup.zpowers yL) (↥L₀ ⧸ H))
            ≤ Nat.card ({QuotientGroup.mk (1 : ↥L₀)} : Set (↥L₀ ⧸ H)) :=
              Nat.card_mono (Set.toFinite _) hsub
          _ = 1 := by simp
      omega
    obtain ⟨x, hxq⟩ := QuotientGroup.mk_surjective q
    have hxL : (x : G) ∈ L₀ := x.2
    have hxnotH : x ∉ H := by
      intro hxH
      apply hqne
      rw [← hxq]
      exact QuotientGroup.eq.mpr (by simpa using hxH)
    have hxnotM : (x : G) ∉ D.M := by
      intro hxM
      exact hxnotH ((Subgroup.mem_subgroupOf).2 (Subgroup.mem_inf.2 ⟨x.2, hxM⟩))
    have hfix := hqfix
    rw [MulAction.mem_fixedPoints] at hfix
    have hyfix := hfix ⟨yL, Subgroup.mem_zpowers yL⟩
    rw [← hxq] at hyfix
    change QuotientGroup.mk (yL * x) = QuotientGroup.mk x at hyfix
    have hmemH : (yL * x)⁻¹ * x ∈ H := QuotientGroup.eq.mp hyfix
    have hmemH' : x⁻¹ * (yL : ↥L₀) * x ∈ H := by
      have h1 : (yL * x)⁻¹ * x = x⁻¹ * (yL : ↥L₀)⁻¹ * x := by group
      rw [h1] at hmemH
      have h2 := H.inv_mem hmemH
      rwa [show (x⁻¹ * (yL : ↥L₀)⁻¹ * x)⁻¹ = x⁻¹ * (yL : ↥L₀) * x from by group] at h2
    have hmemG : (x : G)⁻¹ * (y : G) * (x : G) ∈ D.M :=
      (Subgroup.mem_subgroupOf.mp hmemH').2
    have hyconj : (y : G) ∈ CFSG.Quasithin.conjSubgroup D.M ((x : G)⁻¹) := by
      rw [CFSG.Quasithin.mem_conjSubgroup_iff]
      simpa using hmemG
    have h5dvd : 5 ∣ Nat.card (D.M ⊓ CFSG.Quasithin.conjSubgroup D.M ((x : G)⁻¹) : Subgroup G) := by
      have hle : Subgroup.zpowers (y : G) ≤
          D.M ⊓ CFSG.Quasithin.conjSubgroup D.M ((x : G)⁻¹) :=
        Subgroup.zpowers_le.mpr (Subgroup.mem_inf.2 ⟨hyM, hyconj⟩)
      calc 5 = Nat.card ↥(Subgroup.zpowers (y : G)) := by rw [Nat.card_zpowers, hyordG]
        _ ∣ Nat.card ↥(D.M ⊓ CFSG.Quasithin.conjSubgroup D.M ((x : G)⁻¹)) :=
            Subgroup.card_dvd_of_le hle
    exact c.pair.data.hyp.p_not_dvd_card_inf hSg (g := ((x : G)⁻¹))
      (fun hmem => hxnotM (by simpa using D.M.inv_mem hmem)) h5dvd
  · have htop : rMV D.M V = ⊤ :=
      s16c1614_rMV_eq_top D (fun U hUV => by
        by_contra h
        exact hne ⟨U, hUV, h⟩)
    rw [htop] at hr
    exact absurd hr (by simp)

theorem A5Config18.exists_involution_mQuot_four_of_case_two (c : A5Config18 D V₀ V L K)
    (h2 : CaseTwo18 D V L K c.elemAbelian) :
    ∃ t ∈ Mbar D.M (⊥ : Subgroup G) V c.elemAbelian, orderOf t = 2 ∧
      E3.mQuot ⊤ (CFSG.Quasithin.fixV (Subgroup.zpowers t)) = 4 := by
  have hV0 : V₀ = ⊥ := c.v0
  subst V₀
  have hV := c.elemAbelian
  have hsum : SumOfNat (fun H U Z => NatOmegaPlus H U Z 4 2)
      (barSub (⊥ : Subgroup G) V hV L ⊔ barSub (⊥ : Subgroup G) V hV K) ⊤ ⊥ 2 := h2.2.2
  have hrk : rk (Vtil (⊥ : Subgroup G) V hV) = 16 := by
    rw [← rk_top, rk_vtil_eq_sixteen hV hsum]
  have heven : Even (Nat.card ↥(Mbar D.M (⊥ : Subgroup G) V hV)) := by
    by_contra hodd
    have h := c.numerics.1
    unfold mBar at h
    rw [CFSG.Quasithin.E3.mParam, if_neg hodd, hrk] at h
    norm_num at h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : ({n : ℕ | ∃ t ∈ Mbar D.M (⊥ : Subgroup G) V hV, orderOf t = 2 ∧
      n = rkIdx (CFSG.Quasithin.fixV (Subgroup.zpowers t))}).Nonempty := by
    obtain ⟨t, hto⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(Mbar D.M (⊥ : Subgroup G) V hV)) 2 (even_iff_two_dvd.mp heven)
    exact ⟨_, t, t.2, by simpa using hto, rfl⟩
  have hm : CFSG.Quasithin.E3.mParam (Mbar D.M (⊥ : Subgroup G) V hV) = 4 := c.numerics.1
  rw [CFSG.Quasithin.E3.mParam, if_pos heven] at hm
  have hmem := Nat.sInf_mem hS
  rw [hm] at hmem
  obtain ⟨t, ht, hto, hval⟩ := hmem
  refine ⟨t, ht, hto, ?_⟩
  rw [mQuot_top_eq_rkIdx, ← hval]

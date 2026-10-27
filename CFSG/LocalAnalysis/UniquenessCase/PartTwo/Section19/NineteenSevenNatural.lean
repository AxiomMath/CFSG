module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenSevenCentralizers
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenSevenThirteenTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Aset
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenWitt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R37B
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTwentyThreeHyp125

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12
open CFSG.Quasithin CFSG.LocalAnalysis.WeakClosure81
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem nineteen_seven_mbar_le_normalizer (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (hV : IsElemAbelian 2 V) (hS : Setting19_7 D V₀ V p L K hV)
    (S : OmegaModel (Vtil V₀ V hV)) (hSω : S.omega = barSub V₀ V hV L ⊔ barSub V₀ V hV K) :
    Mbar D.M V₀ V hV ≤ normalizer (S.omega : Set (MulAut (Vtil V₀ V hV))) := by
  rw [hSω, ← hS.opp3]
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (close16_opp_le 3 (Mbar D.M V₀ V hV))).1
    (close16_opp_normal 3 (Mbar D.M V₀ V hV))

theorem nineteen_seven_centralizer_le_of_nonsingular (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (hV : IsElemAbelian 2 V) (hS : Setting19_7 D V₀ V p L K hV)
    (h5 : R19_5At D V₀ V p L K hS.ctx) (h61 : UC6.R6_1 D)
    (S : OmegaModel (Vtil V₀ V hV)) (hSω : S.omega = barSub V₀ V hV L ⊔ barSub V₀ V hV K)
    (hSK : Nat.card S.K = 4) {x : IntMod V hV} (hx : S.Q (mkTil V₀ V hV x) ≠ 0) :
    centralizer ({x.val} : Set G) ≤ D.M := by
  have hw1 : mkTil V₀ V hV x ≠ 1 := fun h => hx (h ▸ S.Q_one)
  have hx0 : x.val ∉ V₀ := fun h0 =>
    hw1 ((QuotientGroup.eq_one_iff (N := modNull V₀ V hV) x).2 h0)
  have hperf := S.isPerfect_ptCent_omega0 hx
  have hcard := S.card_ptCent_omega0 hx
  have h5P₀ : 5 ∣ Nat.card ↥(ptCent S.omega0 (mkTil V₀ V hV x)) := by
    rw [hcard, hSK]
    norm_num
  have hP₀ : ptCent S.omega0 (mkTil V₀ V hV x) ≤
      ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x) := by
    refine inf_le_inf_right _ ?_
    calc S.omega0 ≤ S.omega := S.omega0_le_omega
      _ = barSub V₀ V hV L ⊔ barSub V₀ V hV K := hSω
      _ ≤ Mbar D.M V₀ V hV :=
        sup_le (barSub_mono V₀ V hV (CFSG.Open.IsSubnormal.le hS.ctx.hyp.hL.1.1))
          (barSub_mono V₀ V hV (CFSG.Open.IsSubnormal.le hS.ctx.hK.1))
  obtain ⟨X, hXle, hXp, hXc⟩ :=
    nineteen_seven_noncyclic_cent_of_perfect_bar D hS.ctx hV h5 x hx0 hP₀ hperf h5P₀
      hS.five_dvd
  have hx1 : x.val ≠ 1 := fun h => hx0 (h ▸ V₀.one_mem)
  have hx2 : ∃ n : ℕ, x.val ^ (2 ^ n) = 1 := ⟨1, by simpa using hV.2 x.val x.val_mem⟩
  exact centralizer_le_of_noncyclic D h61 (hS.ctx.p_eq ▸ hS.ctx.hyp.hp)
    (hXle.trans inf_le_left) hXp hXc hx1 hx2 (hXle.trans inf_le_right)

theorem nineteen_seven_natural_Q_eq_zero_of_mem_imgTil (D : Data G) {V₀ V : Subgroup G}
    {hV : IsElemAbelian 2 V} (S : OmegaModel (Vtil V₀ V hV)) {U : Subgroup G}
    (hUC : ¬ centralizer (U : Set G) ≤ D.M)
    (hcQ : ∀ x : IntMod V hV, S.Q (mkTil V₀ V hV x) ≠ 0 →
      centralizer ({x.val} : Set G) ≤ D.M)
    {u : Vtil V₀ V hV} (hu : u ∈ imgTil V₀ V hV U) : S.Q u = 0 := by
  obtain ⟨x, hxU, rfl⟩ := (mem_imgTil V₀ V hV U u).1 hu
  by_contra hne
  exact hUC ((Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxU)).trans (hcQ x hne))

theorem nineteen_seven_natural_rk_imgTil_le_two_mul (D : Data G) {V₀ V : Subgroup G}
    {hV : IsElemAbelian 2 V} (S : OmegaModel (Vtil V₀ V hV)) {m : ℕ}
    (hSK : Nat.card S.K = 2 ^ m)
    (hcQ : ∀ x : IntMod V hV, S.Q (mkTil V₀ V hV x) ≠ 0 →
      centralizer ({x.val} : Set G) ≤ D.M)
    {U : Subgroup G} (hUC : ¬ centralizer (U : Set G) ≤ D.M) :
    rk ↥(imgTil V₀ V hV U) ≤ 2 * m := by
  have hsing : ∀ u ∈ imgTil V₀ V hV U, S.Q u = 0 := fun u hu =>
    nineteen_seven_natural_Q_eq_zero_of_mem_imgTil D S hUC hcQ hu
  have hW2 : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := fun w => by
    rw [pow_two]
    exact S.mul_self_eq_one w
  have hcard := S.card_le_of_totallySingular hsing
  rw [card_eq_two_pow hW2 (imgTil V₀ V hV U), hSK, ← pow_mul] at hcard
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hcard
  omega

theorem nineteen_seven_natural_two_mul_le_mQuot_of_mem_calDn (D : Data G)
    {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) (hV : IsElemAbelian 2 V)
    (S : OmegaModel (Vtil V₀ V hV))
    (hN : Mbar D.M V₀ V hV ≤ normalizer (S.omega : Set (MulAut (Vtil V₀ V hV))))
    {m : ℕ} (hSK : Nat.card S.K = 2 ^ m)
    (hcQ : ∀ x : IntMod V hV, S.Q (mkTil V₀ V hV x) ≠ 0 →
      centralizer ({x.val} : Set G) ≤ D.M)
    {U : Subgroup G} (hU : U ∈ calDn (mSub V) D.M V) : 2 * m ≤ E3.mQuot V U := by
  obtain ⟨hUV, t, ht, ⟨k, hk⟩, W', hW'V, -, -, hW't, hD⟩ := hU
  have hP : PairFacts D.M V₀ V := h.pairFacts
  obtain ⟨htM, htCU⟩ := Subgroup.mem_inf.1 ht
  have hts : t⁻¹ ∈ stabTil V₀ V :=
    le_stabTil hP.le_normalizer hP.le_normalizer₀ (D.M.inv_mem htM)
  obtain ⟨w, hwW, hwt⟩ : ∃ w ∈ W', w ∉ centralizer ({t} : Set G) := by
    by_contra hcon
    exact hW't fun w hw => Classical.byContradiction fun hw' => hcon ⟨w, hw, hw'⟩
  have hwV : w ∈ V := hW'V hwW
  have htN : t⁻¹ * w * t ∈ V :=
    (Subgroup.mem_normalizer_iff''.1 (hP.le_normalizer htM) w).1 hwV
  have hz₀V : w⁻¹ * t⁻¹ * w * t ∈ V := by
    have h1 : w⁻¹ * (t⁻¹ * w * t) ∈ V := V.mul_mem (V.inv_mem hwV) htN
    simpa [mul_assoc] using h1
  have hz₀mem : w⁻¹ * t⁻¹ * w * t ∈ commElt W' t := Subgroup.subset_closure ⟨w, hwW, rfl⟩
  have hDz := hD _ hz₀mem
  have hz₁ : w⁻¹ * t⁻¹ * w * t ≠ 1 := by
    intro h1
    apply hwt
    rw [Subgroup.mem_centralizer_iff]
    intro h' hh'
    rw [Set.mem_singleton_iff] at hh'
    rw [hh']
    have h2 : t⁻¹ * w * t = w := by
      calc t⁻¹ * w * t = w * (w⁻¹ * t⁻¹ * w * t) := by group
        _ = w := by rw [h1, mul_one]
    calc t * w = t * (t⁻¹ * w * t) := by rw [h2]
      _ = w * t := by group
  have hz₀V₀ : w⁻¹ * t⁻¹ * w * t ∉ V₀ := fun hmem =>
    hDz (centralizer_singleton_le_M_of_mem_V₀' D h hmem hz₁)
  let xw : IntMod V hV := IntMod.mk hV ⟨w, hwV⟩
  let x₀ : IntMod V hV := xw⁻¹ * actStab V₀ V hV ⟨t⁻¹, hts⟩ xw
  have hval : x₀.val = w⁻¹ * t⁻¹ * w * t := by
    show (xw⁻¹ * actStab V₀ V hV ⟨t⁻¹, hts⟩ xw).val = _
    have hxw : xw.val = w := rfl
    rw [IntMod.val_mul, IntMod.val_inv, actStab_apply_val, hxw]
    simp [mul_assoc]
  have hsing : S.Q (mkTil V₀ V hV x₀) = 0 := by
    by_contra hne
    have h' := hcQ x₀ hne
    rw [hval] at h'
    exact hDz h'
  have hne1 : mkTil V₀ V hV x₀ ≠ 1 := fun h1 =>
    hz₀V₀ (hval ▸ (mem_modNull V₀ V hV x₀).1
      ((QuotientGroup.eq_one_iff (N := modNull V₀ V hV) x₀).1 h1))
  let g : MulAut (Vtil V₀ V hV) := actTil V₀ V hV ⟨t⁻¹, hts⟩
  have hgM : g ∈ Mbar D.M V₀ V hV := actTil_mem_barSub V₀ V hV (D.M.inv_mem htM) hts
  have hgnorm : g ∈ Subgroup.normalizer (S.omega : Set (MulAut (Vtil V₀ V hV))) := hN hgM
  have hgord : ∃ j : ℕ, g ^ 2 ^ j = 1 := by
    refine ⟨k, ?_⟩
    have h1 : (⟨t⁻¹, hts⟩ : stabTil V₀ V) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [inv_pow, ← hk, pow_orderOf_eq_one, inv_one]
    show actTil V₀ V hV ⟨t⁻¹, hts⟩ ^ 2 ^ k = 1
    rw [← map_pow, h1, map_one]
  have hcomm : g (mkTil V₀ V hV xw) * (mkTil V₀ V hV xw)⁻¹ = mkTil V₀ V hV x₀ := by
    have hg1 : g (mkTil V₀ V hV xw) = mkTil V₀ V hV (actStab V₀ V hV ⟨t⁻¹, hts⟩ xw) :=
      actTil_mk V₀ V hV _ _
    calc g (mkTil V₀ V hV xw) * (mkTil V₀ V hV xw)⁻¹
        = (mkTil V₀ V hV xw)⁻¹ * mkTil V₀ V hV (actStab V₀ V hV ⟨t⁻¹, hts⟩ xw) := by
          rw [hg1, mul_comm]
      _ = mkTil V₀ V hV x₀ := by
          show _ = mkTil V₀ V hV (xw⁻¹ * actStab V₀ V hV ⟨t⁻¹, hts⟩ xw)
          rw [map_mul, map_inv]
  have hcard := S.card_fixed_le_of_singular_commutator hgnorm hgord (w := mkTil V₀ V hV xw)
    (by rw [hcomm]; exact hne1) (by rw [hcomm]; exact hsing)
  have hfix : ∀ q ∈ imgTil V₀ V hV U, g q = q := by
    intro q hq
    obtain ⟨x, hxU, rfl⟩ := (mem_imgTil V₀ V hV U q).1 hq
    have h1 : actStab V₀ V hV ⟨t⁻¹, hts⟩ x = x := by
      apply IntMod.val_injective
      rw [actStab_apply_val]
      have hc := Subgroup.mem_centralizer_iff.1 htCU x.val hxU
      simp only [inv_inv]
      calc t⁻¹ * x.val * t = t⁻¹ * (x.val * t) := by rw [mul_assoc]
        _ = t⁻¹ * (t * x.val) := by rw [hc]
        _ = x.val := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    show actTil V₀ V hV ⟨t⁻¹, hts⟩ (mkTil V₀ V hV x) = mkTil V₀ V hV x
    rw [actTil_mk, h1]
  have hW2 : ∀ v : Vtil V₀ V hV, v ^ 2 = 1 := fun v => by
    rw [pow_two]
    exact S.mul_self_eq_one v
  have hrk : rk ↥(imgTil V₀ V hV U) ≤ 2 * m := by
    have hle : Nat.card ↥(imgTil V₀ V hV U) ≤ Nat.card {v : Vtil V₀ V hV // g v = v} :=
      Nat.card_le_card_of_injective (fun q => (⟨q.1, hfix q.1 q.2⟩ : {v // g v = v}))
        (fun a b hab => Subtype.ext
          (congrArg (Subtype.val (p := fun v : Vtil V₀ V hV => g v = v)) hab))
    have h2 := hle.trans hcard
    rw [card_eq_two_pow hW2 (imgTil V₀ V hV U), hSK, ← pow_mul] at h2
    have h3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2
    omega
  have hq := mSub_eq_mQuot_add V U hV hUV
  have hU' := s15_Infra_mSub_eq_rk_imgTil_add V₀ V U hV hUV
  have hrk' := rk_top_vtil_add_mSub V₀ V hV hP.le
  have h4 := S.rk_top_eq hSK
  have hmono : mSub (U ⊓ V₀) ≤ mSub V₀ := rk_mono inf_le_right
  omega

theorem nineteen_seven_sixteen_thirtyFive_gen (D : Data G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) {hV : IsElemAbelian 2 V} (S : OmegaModel (Vtil V₀ V hV))
    (hN : Mbar D.M V₀ V hV ≤ normalizer (S.omega : Set (MulAut (Vtil V₀ V hV))))
    {m : ℕ} (hSK : Nat.card S.K = 2 ^ m)
    (hcQ : ∀ x : IntMod V hV, S.Q (mkTil V₀ V hV x) ≠ 0 → centralizer ({x.val} : Set G) ≤ D.M) :
    ((2 * m : ℕ) : ℕ∞) ≤ deltaInf D.M V ∧ ((2 * m + mSub V₀ : ℕ) : ℕ∞) ≤ rMV D.M V := by
  refine ⟨?_, ?_⟩
  · unfold deltaInf deltaN
    refine le_iInf₂ fun U hU => ?_
    exact_mod_cast nineteen_seven_natural_two_mul_le_mQuot_of_mem_calDn D h hV S hN hSK hcQ hU
  · have hrk8 : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) + mSub V₀ = mSub V :=
      rk_top_vtil_add_mSub V₀ V hV h.pairFacts.le
    have h4 := S.rk_top_eq hSK
    exact le_rMV_of_forall_rk_imgTil_le D h (b := 2 * m) (c := 2 * m + mSub V₀) (by omega)
      (fun U _ hUC => nineteen_seven_natural_rk_imgTil_le_two_mul D S hSK hcQ hUC)

theorem nineteen_seven_sixteen_thirtyFive (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (hV : IsElemAbelian 2 V) (hS : Setting19_7 D V₀ V p L K hV)
    (h5 : R19_5At D V₀ V p L K hS.ctx) (h61 : UC6.R6_1 D)
    (S : OmegaModel (Vtil V₀ V hV)) (hSω : S.omega = barSub V₀ V hV L ⊔ barSub V₀ V hV K)
    (hSK : Nat.card S.K = 4) :
    (4 : ℕ∞) ≤ deltaInf D.M V ∧ ((4 + mSub V₀ : ℕ) : ℕ∞) ≤ rMV D.M V := by
  have hSK' : Nat.card S.K = 2 ^ 2 := hSK.trans (by norm_num)
  have hN := nineteen_seven_mbar_le_normalizer D hV hS S hSω
  have hcQ : ∀ x : IntMod V hV, S.Q (mkTil V₀ V hV x) ≠ 0 →
      centralizer ({x.val} : Set G) ≤ D.M := fun x hx =>
    nineteen_seven_centralizer_le_of_nonsingular D hV hS h5 h61 S hSω hSK hx
  have h := nineteen_seven_sixteen_thirtyFive_gen D hS.ctx.hyp.hyp125 S hN hSK' hcQ
  simpa using h

theorem nineteen_seven_inf_conj_eq_bot (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (hV : IsElemAbelian 2 V) (hS : Setting19_7 D V₀ V p L K hV)
    (h3 : R19_3At D V₀ V p L K hS.ctx) (h5 : R19_5At D V₀ V p L K hS.ctx)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1) :
    ∀ g : G, g ∉ D.M → V₀ ⊓ conjSubgroup V g = ⊥ := by
  have hcent : ∀ v ∈ V, v ≠ 1 →
      1 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer ({v} : Set G)) := by
    rw [hS.ctx.p_eq]
    exact nineteen_seven_one_le_pRank_centralizer D hS.ctx h3 h5 hS.five_dvd
  have hU : ∀ u ∈ V₀, u ≠ 1 → centralizer ({u} : Set G) ≤ D.M := fun u hu hu1 =>
    centralizer_singleton_le_M_of_mem_V₀' D hS.ctx.hyp.hyp125 hu hu1
  intro g hg
  have hg' : g⁻¹ ∉ D.M := fun h => hg (by simpa using D.M.inv_mem h)
  have h := nineteen_seven_conj_inf_eq_bot D hSg h1219 (U := V₀) hS.ctx.hyp.hp hcent hU g⁻¹ hg'
  rw [← E3.conjSubgroup_inv_conj V₀ g, ← E3.conjSubgroup_inf, h, E3.conjSubgroup_bot]

theorem nineteen_seven_barSub_mem_calABar (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (hV : IsElemAbelian 2 V) (hS : Setting19_7 D V₀ V p L K hV)
    (h3 : R19_3At D V₀ V p L K hS.ctx) (h5 : R19_5At D V₀ V p L K hS.ctx) (h61 : UC6.R6_1 D)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (S : OmegaModel (Vtil V₀ V hV)) (hSω : S.omega = barSub V₀ V hV L ⊔ barSub V₀ V hV K)
    (hSK : Nat.card S.K = 4) {i k : ℕ} (hki : k + i ≤ 4) {A : Subgroup G}
    (hA : A ∈ E3.gammaSet V i D.M) (hA1 : barSub V₀ V hV A ≠ ⊥) :
    barSub V₀ V hV A ∈ calABar k D.M V₀ V hV := by
  obtain ⟨hδ, hr⟩ := nineteen_seven_sixteen_thirtyFive D hV hS h5 h61 S hSω hSK
  have hcent : ∀ v ∈ V, v ≠ 1 →
      1 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer ({v} : Set G)) := by
    rw [hS.ctx.p_eq]
    exact nineteen_seven_one_le_pRank_centralizer D hS.ctx h3 h5 hS.five_dvd
  refine barSub_mem_calABar_of_gammaSet_gen D hSg h1219 hS.ctx.hyp.hyp125 hS.ctx.hyp.hp hcent
    (nineteen_seven_inf_conj_eq_bot D hV hS h3 h5 hSg h1219) ?_ ?_ hA hA1
  · exact le_trans (by exact_mod_cast (by omega : k + i + mSub V₀ ≤ 4 + mSub V₀)) hr
  · exact le_trans (by exact_mod_cast (by omega : k + i ≤ 4)) hδ

theorem nineteen_seven_wClos_le_centralizer (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (hV : IsElemAbelian 2 V) (hS : Setting19_7 D V₀ V p L K hV)
    (h3 : R19_3At D V₀ V p L K hS.ctx) (h5 : R19_5At D V₀ V p L K hS.ctx) (h61 : UC6.R6_1 D)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (S : OmegaModel (Vtil V₀ V hV)) (hSω : S.omega = barSub V₀ V hV L ⊔ barSub V₀ V hV K)
    (hSK : Nat.card S.K = 4) :
    E3.wClos V 0 D.T ≤ centralizer (V : Set G) := by
  classical
  have hP : PairFacts D.M V₀ V := hS.ctx.hyp.hyp125.pairFacts
  have hSK' : Nat.card S.K = 2 ^ 2 := hSK.trans (by norm_num)
  have hN := nineteen_seven_mbar_le_normalizer D hV hS S hSω
  have hempty : E3.aSet 3 (Mbar D.M V₀ V hV) = ∅ := by
    simpa using S.aSet_succ_eq_empty hSK' hN
  obtain ⟨-, hr⟩ := nineteen_seven_sixteen_thirtyFive D hV hS h5 h61 S hSω hSK
  refine E3.wClos_le_of_forall fun A hA => ?_
  have hAM : A ∈ E3.gammaSet V 0 D.M := E3.gammaSet_mono D.sylowM.le hA
  obtain ⟨hAT, g, hAg, -⟩ := hA
  have hAMle : A ≤ D.M := hAT.trans D.sylowM.le
  have hbar : barSub V₀ V hV A = ⊥ := by
    by_contra hne
    have hmem := nineteen_seven_barSub_mem_calABar D hV hS h3 h5 h61 hSg h1219 S hSω hSK
      (i := 0) (k := 3) (by omega) hAM hne
    exact (Set.eq_empty_iff_forall_notMem.1 hempty) _ hmem
  have hi0 : ((0 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_lt_of_le (by exact_mod_cast (by omega : 0 + mSub V₀ < 4 + mSub V₀)) hr
  obtain ⟨-, hc, -⟩ := S18.twentyThree_one_of_inf D hS.ctx.hyp.hyp125 hAM hAg hi0
    (fun hg => nineteen_seven_inf_conj_eq_bot D hV hS h3 h5 hSg h1219 g hg)
  have hCt := (barSub_eq_bot_iff hV hP.le_normalizer hP.le_normalizer₀ hAMle).1 hbar
  have hVc : V ≤ centralizer (A : Set G) := fun v hv => hc v hv fun a ha => by
    have hcm := centralizesMod_of_mem_cTilde hV hP.le_normalizer hP.le_normalizer₀
      (hCt ha) v hv
    have e : ⁅v, a⁆ = (a * v * a⁻¹ * v⁻¹)⁻¹ := by group
    rw [e]
    exact V₀.inv_mem hcm
  exact Subgroup.le_centralizer_iff.1 hVc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

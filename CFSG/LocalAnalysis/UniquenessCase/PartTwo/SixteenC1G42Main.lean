module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GKit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G42Mod
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G42Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Bot47Plane

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c1G_rk_top (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Case167_1 D V₀ V hV L) : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 6 := by
  have h64 : (64 : ℕ) = 2 ^ 6 := by norm_num
  rw [rk_top, rk, s16c1_card_of_natOmegaMinus hc.2.1, h64, padicValNat.prime_pow]

theorem s16c1G_singular_of_not_cent_le {D : Data G} {V₀ V : Subgroup G}
    {hV : IsElemAbelian 2 V} {Q : Vtil V₀ V hV → ZMod 2}
    (hns : ∀ x : IntMod V hV, Q (mkTil V₀ V hV x) ≠ 0 → centralizer ({x.val} : Set G) ≤ D.M)
    {U : Subgroup G} (hUC : ¬ centralizer (U : Set G) ≤ D.M) :
    ∀ u ∈ imgTil V₀ V hV U, Q u = 0 := by
  intro q hq
  obtain ⟨x, hxU, rfl⟩ := (mem_imgTil V₀ V hV U q).1 hq
  by_contra hne
  exact hUC ((Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxU)).trans (hns x hne))

private theorem s16c1G_centralizer_singleton_le_M_of_mem_V₀ (D : Data G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) {z : G} (hzV₀ : z ∈ V₀) (hz : z ≠ 1) :
    centralizer ({z} : Set G) ≤ D.M := by
  have hcent_eq : centralizer ({z} : Set G) = centralizer (Subgroup.zpowers z : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  exact (le_of_eq hcent_eq).trans
    (centralizer_le_M_of_mem_inf_V₀ D h (U := Subgroup.zpowers z)
      (Subgroup.mem_zpowers z) hzV₀ hz)

theorem s16c1G_exists_singular_comm (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) {Q : Vtil V₀ V hV → ZMod 2}
    (hns : ∀ x : IntMod V hV, Q (mkTil V₀ V hV x) ≠ 0 → centralizer ({x.val} : Set G) ≤ D.M)
    {U : Subgroup G} (hU : U ∈ calDn (mSub V) D.M V) :
    ∃ (g : MulAut (Vtil V₀ V hV)) (w : Vtil V₀ V hV), g ∈ Mbar D.M V₀ V hV ∧
      g w * w⁻¹ ≠ 1 ∧ Q (g w * w⁻¹) = 0 ∧ ∀ q ∈ imgTil V₀ V hV U, g q = q := by
  obtain ⟨hUV, t, ht, ⟨_, _⟩, W', hW'V, -, -, hW't, hD⟩ := hU
  have hH125 : Hyp125 D V₀ V := hS.setting.hyp16.hyp125
  have hP : PairFacts D.M V₀ V := hH125.pairFacts
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
    intro h
    apply hwt
    rw [Subgroup.mem_centralizer_iff]
    intro h' hh'
    rw [Set.mem_singleton_iff] at hh'
    rw [hh']
    have h2 : t⁻¹ * w * t = w := by
      calc t⁻¹ * w * t = w * (w⁻¹ * t⁻¹ * w * t) := by group
        _ = w := by rw [h, mul_one]
    calc t * w = t * (t⁻¹ * w * t) := by rw [h2]
      _ = w * t := by group
  have hz₀V₀ : w⁻¹ * t⁻¹ * w * t ∉ V₀ := fun hmem =>
    hDz (s16c1G_centralizer_singleton_le_M_of_mem_V₀ D hH125 hmem hz₁)
  let xw : IntMod V hV := IntMod.mk hV ⟨w, hwV⟩
  let x₀ : IntMod V hV := xw⁻¹ * actStab V₀ V hV ⟨t⁻¹, hts⟩ xw
  have hval : x₀.val = w⁻¹ * t⁻¹ * w * t := by
    show (xw⁻¹ * actStab V₀ V hV ⟨t⁻¹, hts⟩ xw).val = _
    have hxw : xw.val = w := rfl
    rw [IntMod.val_mul, IntMod.val_inv, actStab_apply_val, hxw]
    simp [mul_assoc]
  have hsing : Q (mkTil V₀ V hV x₀) = 0 := by
    by_contra hne
    exact hDz (hval ▸ hns x₀ hne)
  have hne1 : mkTil V₀ V hV x₀ ≠ 1 := fun h =>
    hz₀V₀ (hval ▸ (mem_modNull V₀ V hV x₀).1
      ((QuotientGroup.eq_one_iff (N := modNull V₀ V hV) x₀).1 h))
  let g : MulAut (Vtil V₀ V hV) := actTil V₀ V hV ⟨t⁻¹, hts⟩
  have hgM : g ∈ Mbar D.M V₀ V hV := actTil_mem_barSub V₀ V hV (D.M.inv_mem htM) hts
  have hcomm : g (mkTil V₀ V hV xw) * (mkTil V₀ V hV xw)⁻¹ = mkTil V₀ V hV x₀ := by
    have hg1 : g (mkTil V₀ V hV xw) = mkTil V₀ V hV (actStab V₀ V hV ⟨t⁻¹, hts⟩ xw) :=
      actTil_mk V₀ V hV _ _
    calc g (mkTil V₀ V hV xw) * (mkTil V₀ V hV xw)⁻¹
        = (mkTil V₀ V hV xw)⁻¹ * mkTil V₀ V hV (actStab V₀ V hV ⟨t⁻¹, hts⟩ xw) := by
          rw [hg1, mul_comm]
      _ = mkTil V₀ V hV x₀ := by
          show _ = mkTil V₀ V hV (xw⁻¹ * actStab V₀ V hV ⟨t⁻¹, hts⟩ xw)
          rw [map_mul, map_inv]
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
  exact ⟨g, mkTil V₀ V hV xw, hgM, by rw [hcomm]; exact hne1,
    by rw [hcomm]; exact hsing, hfix⟩

theorem s16c1G_two_le_mQuot (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L) {U : Subgroup G} (hUV : U ≤ V)
    (h4 : rk ↥(imgTil V₀ V hV U) ≤ 4) : 2 ≤ E3.mQuot V U := by
  have hP : PairFacts D.M V₀ V := hS.setting.hyp16.hyp125.pairFacts
  have hq := mSub_eq_mQuot_add V U hV hUV
  have hU' := s15_Infra_mSub_eq_rk_imgTil_add V₀ V U hV hUV
  have hrk' := rk_top_vtil_add_mSub V₀ V hV hP.le
  have h6 := s16c1G_rk_top D hc
  have hmono : mSub (U ⊓ V₀) ≤ mSub V₀ := rk_mono inf_le_right
  omega

theorem s16c1G_rk_imgTil_le_four (D : Data G) (hkit : OmegaKit) (hkitC : OmegaKitC)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hc : Case167_1 D V₀ V hV L) {Q : Vtil V₀ V hV → ZMod 2} (hQ : IsMinusQuadF2 Q)
    (hQi : QuadInvariant Q (lBar V₀ V hV L))
    (hns : ∀ x : IntMod V hV, Q (mkTil V₀ V hV x) ≠ 0 → centralizer ({x.val} : Set G) ≤ D.M)
    {U : Subgroup G} (hU : U ∈ calDn (mSub V) D.M V) :
    rk ↥(imgTil V₀ V hV U) ≤ 4 := by
  obtain ⟨g, w, hgM, hw, hwQ, hfix⟩ := s16c1G_exists_singular_comm D hS hns hU
  have hgN := mBar_le_normalizer_lBar D hS hc hgM
  have hW : Nat.card (Vtil V₀ V hV) = 64 := s16c1_card_of_natOmegaMinus hc.2.1
  have hnt : OmegaNoTrans (lBar V₀ V hV L) :=
    (hkit (Vtil V₀ V hV) (lBar V₀ V hV L) hc.2.1).2.2
  have hout : OmegaOuterNons (lBar V₀ V hV L) :=
    (hkitC (Vtil V₀ V hV) (lBar V₀ V hV L) hc.2.1).2.2.1
  have hcard := s16c1G_card_le_of_singular_commutator hW hnt hout hQ hQi hgN hw hwQ
    (A := imgTil V₀ V hV U) hfix
  have hW2 : ∀ v : Vtil V₀ V hV, v ^ 2 = 1 := fun v => s15_Infra_vtil_sq_eq_one V₀ V hV v
  rw [card_eq_two_pow hW2 (imgTil V₀ V hV U)] at hcard
  have h16 : (2 : ℕ) ^ rk ↥(imgTil V₀ V hV U) ≤ 2 ^ 4 := by simpa using hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h16

theorem s16c1G_cent_le_of_plane (D : Data G) (h61 : UC6.R6_1 D) (hkitC : OmegaKitC)
    (hkitG : OmegaKitG) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L) (hV0 : V₀ = ⊥)
    {Q : Vtil V₀ V hV → ZMod 2} (hQ : IsMinusQuadF2 Q) (hQi : QuadInvariant Q (lBar V₀ V hV L))
    {U : Subgroup G} (hUV : U ≤ V) (hsing : ∀ u ∈ imgTil V₀ V hV U, Q u = 0)
    (h2 : rk ↥(imgTil V₀ V hV U) = 2) : centralizer (U : Set G) ≤ D.M := by
  subst hV0
  have hH125 : Hyp125 D ⊥ V := hS.setting.hyp16.hyp125
  have hP : PairFacts D.M ⊥ V := hH125.pairFacts
  let P : Subgroup (Vtil ⊥ V hV) := imgTil ⊥ V hV U
  have hsq : ∀ v : Vtil ⊥ V hV, v ^ 2 = 1 := fun v => s15_Infra_vtil_sq_eq_one ⊥ V hV v
  have hPcard : Nat.card P = 4 := by
    show Nat.card ↥(imgTil ⊥ V hV U) = 4
    rw [card_eq_two_pow hsq (imgTil ⊥ V hV U), h2]
    norm_num
  have hcent : ∀ w ∈ P, w ≠ 1 → Nat.card (ptCent (lBar ⊥ V hV L) w) = 960 := by
    intro w hw hw1
    exact ((hkitC (Vtil ⊥ V hV) (lBar ⊥ V hV L) hc.2.1).1 Q hQ hQi w hw1).1
      (hsing w hw)
  obtain ⟨E, hE, hE3, hEnc, hstab⟩ :=
    hkitG (Vtil ⊥ V hV) (lBar ⊥ V hV L) hc.2.1 P hPcard hcent
  have hEM : E ≤ Mbar D.M ⊥ V hV := hE.trans (barSub_mono ⊥ V hV hS.setting.hyp151.le)
  obtain ⟨X, hXle, hX3, hXc⟩ :=
    s16c1G_exists_noncyclic_three_of_stable D hV hP hUV hEM hE3 hEnc hstab
  have hU1 : U ≠ ⊥ := by
    rintro rfl
    have hbot : imgTil ⊥ V hV (⊥ : Subgroup G) = ⊥ := by
      ext q
      rw [mem_imgTil, Subgroup.mem_bot]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [Subgroup.mem_bot] at hx
        have hx1 : x = 1 := IntMod.val_injective hx
        rw [hx1, map_one]
      · rintro rfl
        exact ⟨1, Subgroup.one_mem _, map_one _⟩
    rw [hbot, rk_bot] at h2
    omega
  have hU2 : IsPGroup 2 U := hV.isPGroup.to_le hUV
  have h3 : 3 ∈ D.sig := by
    rw [hc.2.2.1]
    exact Set.mem_singleton 3
  have hN : normalizer (U : Set G) ≤ D.M :=
    normalizer_le_of_noncyclic D h61 h3 (hXle.trans inf_le_left) hX3 hXc hU1 hU2
      (hXle.trans inf_le_right)
  exact (Subgroup.centralizer_le_normalizer (U : Set G)).trans hN

theorem s16c1G_rMV_ge (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L) {Q : Vtil V₀ V hV → ZMod 2}
    (hQ : IsMinusQuadF2 Q)
    (hns : ∀ x : IntMod V hV, Q (mkTil V₀ V hV x) ≠ 0 → centralizer ({x.val} : Set G) ≤ D.M) :
    ((mSub V₀ + 4 : ℕ) : ℕ∞) ≤ rMV D.M V := by
  have hH : Hyp125 D V₀ V := hS.setting.hyp16.hyp125
  have h6 := s16c1G_rk_top D hc
  have hrk := rk_top_vtil_add_mSub V₀ V hV hH.pairFacts.le
  have hsq : ∀ x : Vtil V₀ V hV, x * x = 1 := fun w => by
    simpa [sq] using s15_Infra_vtil_sq_eq_one V₀ V hV w
  refine le_rMV_of_forall_rk_imgTil_le D hH (b := 2) (c := mSub V₀ + 4) (by omega) ?_
  intro U _ hUC
  exact s16c1G_rk_le_two h6 hsq hQ (s16c1G_singular_of_not_cent_le hns hUC)

theorem s16c1G_deltaInf_ge (D : Data G) (hkit : OmegaKit) (hkitC : OmegaKitC)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hc : Case167_1 D V₀ V hV L) {Q : Vtil V₀ V hV → ZMod 2} (hQ : IsMinusQuadF2 Q)
    (hQi : QuadInvariant Q (lBar V₀ V hV L))
    (hns : ∀ x : IntMod V hV, Q (mkTil V₀ V hV x) ≠ 0 → centralizer ({x.val} : Set G) ≤ D.M) :
    (2 : ℕ∞) ≤ deltaInf D.M V := by
  unfold deltaInf deltaN
  refine le_iInf₂ fun U hU => ?_
  exact_mod_cast s16c1G_two_le_mQuot D hS hc hU.1
    (s16c1G_rk_imgTil_le_four D hkit hkitC hS hc hQ hQi hns hU)

theorem s16c1G_rMV_gt_four (D : Data G) (h61 : UC6.R6_1 D) (hkitC : OmegaKitC)
    (hkitG : OmegaKitG) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L) {Q : Vtil V₀ V hV → ZMod 2}
    (hQ : IsMinusQuadF2 Q) (hQi : QuadInvariant Q (lBar V₀ V hV L))
    (hns : ∀ x : IntMod V hV, Q (mkTil V₀ V hV x) ≠ 0 → centralizer ({x.val} : Set G) ≤ D.M)
    (hV0 : V₀ = ⊥) : (4 : ℕ∞) < rMV D.M V := by
  have hH : Hyp125 D V₀ V := hS.setting.hyp16.hyp125
  have h6 := s16c1G_rk_top D hc
  have hrk := rk_top_vtil_add_mSub V₀ V hV hH.pairFacts.le
  have hm0 : mSub V₀ = 0 := by
    rw [hV0]
    exact rk_bot
  have hsq : ∀ x : Vtil V₀ V hV, x * x = 1 := fun w => by
    simpa [sq] using s15_Infra_vtil_sq_eq_one V₀ V hV w
  have hb : ∀ U : Subgroup G, U ≤ V → ¬ centralizer (U : Set G) ≤ D.M →
      rk ↥(imgTil V₀ V hV U) ≤ 1 := by
    intro U hUV hUC
    have hsing := s16c1G_singular_of_not_cent_le hns hUC
    have h2 := s16c1G_rk_le_two h6 hsq hQ hsing
    by_contra hlt
    exact hUC (s16c1G_cent_le_of_plane D h61 hkitC hkitG hS hc hV0 hQ hQi hUV hsing (by omega))
  have h5 : ((5 : ℕ) : ℕ∞) ≤ rMV D.M V :=
    le_rMV_of_forall_rk_imgTil_le D hH (b := 1) (c := 5) (by omega) hb
  exact lt_of_lt_of_le (by norm_num) h5

theorem r16_42_of (D : Data G) (h61 : UC6.R6_1 D) (h41 : R16_41 D) (hkit : OmegaKit)
    (hkitC : OmegaKitC) (hkitG : OmegaKitG) : R16_42 D := by
  intro V₀ V L hV hS hc
  obtain ⟨⟨Q, hQ, hQi⟩, hall⟩ := h41 V₀ V L hV hS hc
  have hns : ∀ x : IntMod V hV, Q (mkTil V₀ V hV x) ≠ 0 →
      centralizer ({x.val} : Set G) ≤ D.M :=
    fun x hx => ((hall Q hQ hQi).2 _ hx).2 x rfl
  exact ⟨s16c1G_rMV_ge D hS hc hQ hns, s16c1G_deltaInf_ge D hkit hkitC hS hc hQ hQi hns,
    fun h0 => s16c1G_rMV_gt_four D h61 hkitC hkitG hS hc hQ hQi hns h0⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

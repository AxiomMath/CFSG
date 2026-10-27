module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Norm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R34
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenWitt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Nat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem Q_eq_zero_of_mem_imgTil (D : Data G) (h61 : UC6.R6_1 D) (hext : DataExt D)
    (h5 : R16_5 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    {m : ℕ} (hm : Case1633 D V₀ V hV L m) (S : OmegaModel (Vtil V₀ V hV))
    (hSω : S.omega = lBar V₀ V hV L) (hSK : Nat.card S.K = 2 ^ m) {p : ℕ} (hp : D.sig = {p})
    {U : Subgroup G} (hUC : ¬ centralizer (U : Set G) ≤ D.M) {u : Vtil V₀ V hV}
    (hu : u ∈ imgTil V₀ V hV U) : S.Q u = 0 := by
  obtain ⟨x, hxU, rfl⟩ := (mem_imgTil V₀ V hV U u).1 hu
  by_contra hne
  exact hUC ((Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxU)).trans
    (r16_34_coord D h61 hext h5 hS hm S hSω hSK hp hne).2)

theorem rk_imgTil_le_two_mul (D : Data G) (h61 : UC6.R6_1 D) (hext : DataExt D) (h5 : R16_5 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) {m : ℕ}
    (hm : Case1633 D V₀ V hV L m) (S : OmegaModel (Vtil V₀ V hV))
    (hSω : S.omega = lBar V₀ V hV L) (hSK : Nat.card S.K = 2 ^ m) {p : ℕ} (hp : D.sig = {p})
    {U : Subgroup G} (hUC : ¬ centralizer (U : Set G) ≤ D.M) :
    rk ↥(imgTil V₀ V hV U) ≤ 2 * m := by
  have hsing : ∀ u ∈ imgTil V₀ V hV U, S.Q u = 0 := fun u hu =>
    Q_eq_zero_of_mem_imgTil D h61 hext h5 hS hm S hSω hSK hp hUC hu
  have hW2 : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := fun w => by
    rw [pow_two]
    exact S.mul_self_eq_one w
  have hcard := S.card_le_of_totallySingular hsing
  rw [card_eq_two_pow hW2 (imgTil V₀ V hV U), hSK, ← pow_mul] at hcard
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hcard
  omega

private theorem centralizer_singleton_le_M_of_mem_V₀ (D : Data G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) {z : G} (hzV₀ : z ∈ V₀) (hz : z ≠ 1) :
    centralizer ({z} : Set G) ≤ D.M := by
  have hXV : Subgroup.zpowers z ≤ V₀ := Subgroup.zpowers_le.2 hzV₀
  have hX1 : Subgroup.zpowers z ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hz
  have hN := h.hyp62.normalizer_le _ hXV hX1
  have hcent_eq : centralizer ({z} : Set G) = centralizer (Subgroup.zpowers z : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  exact ((le_of_eq hcent_eq).trans (Subgroup.centralizer_le_normalizer _)).trans hN

theorem two_mul_le_mQuot_of_mem_calDn (D : Data G) (h61 : UC6.R6_1 D) (hext : DataExt D)
    (h5 : R16_5 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    {m : ℕ} (hm : Case1633 D V₀ V hV L m) (S : OmegaModel (Vtil V₀ V hV))
    (hSω : S.omega = lBar V₀ V hV L) (hSK : Nat.card S.K = 2 ^ m) {p : ℕ} (hp : D.sig = {p})
    {U : Subgroup G} (hU : U ∈ calDn (mSub V) D.M V) : 2 * m ≤ E3.mQuot V U := by
  obtain ⟨hUV, t, ht, ⟨k, hk⟩, W', hW'V, -, -, hW't, hD⟩ := hU
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
    hDz (centralizer_singleton_le_M_of_mem_V₀ D hH125 hmem hz₁)
  let xw : IntMod V hV := IntMod.mk hV ⟨w, hwV⟩
  let x₀ : IntMod V hV := xw⁻¹ * actStab V₀ V hV ⟨t⁻¹, hts⟩ xw
  have hval : x₀.val = w⁻¹ * t⁻¹ * w * t := by
    show (xw⁻¹ * actStab V₀ V hV ⟨t⁻¹, hts⟩ xw).val = _
    have hxw : xw.val = w := rfl
    rw [IntMod.val_mul, IntMod.val_inv, actStab_apply_val, hxw]
    simp [mul_assoc]
  have hsing : S.Q (mkTil V₀ V hV x₀) = 0 := by
    by_contra hne
    have h' := (r16_34_coord D h61 hext h5 hS hm S hSω hSK hp (x := x₀) hne).2
    rw [hval] at h'
    exact hDz h'
  have hne1 : mkTil V₀ V hV x₀ ≠ 1 := fun h =>
    hz₀V₀ (hval ▸ (mem_modNull V₀ V hV x₀).1
      ((QuotientGroup.eq_one_iff (N := modNull V₀ V hV) x₀).1 h))
  let g : MulAut (Vtil V₀ V hV) := actTil V₀ V hV ⟨t⁻¹, hts⟩
  have hgM : g ∈ Mbar D.M V₀ V hV := actTil_mem_barSub V₀ V hV (D.M.inv_mem htM) hts
  have hgnorm : g ∈ Subgroup.normalizer (S.omega : Set (MulAut (Vtil V₀ V hV))) :=
    Mbar_le_normalizer_lBar hS S hSω hgM
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

theorem r16_35_holds (D : Data G) (h61 : UC6.R6_1 D) (hext : DataExt D) (h5 : R16_5 D) :
    ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV → ∀ m : ℕ,
      Case1633 D V₀ V hV L m →
        ((2 * m : ℕ) : ℕ∞) ≤ deltaInf D.M V ∧ ((2 * m + mSub V₀ : ℕ) : ℕ∞) ≤ rMV D.M V := by
  intro V₀ V L hV hS m hm
  obtain ⟨S, hSω, hSK⟩ := exists_omegaModel_of_case1633 hm
  obtain ⟨p, hp⟩ : ∃ p, D.sig = {p} := by
    rcases hm with ⟨hc, -⟩ | ⟨hc, -⟩
    · exact ⟨5, hc.2.2⟩
    · exact ⟨3, hc.2.2⟩
  have hH125 : Hyp125 D V₀ V := hS.setting.hyp16.hyp125
  refine ⟨?_, ?_⟩
  · unfold deltaInf deltaN
    refine le_iInf₂ fun U hU => ?_
    exact_mod_cast two_mul_le_mQuot_of_mem_calDn D h61 hext h5 hS hm S hSω hSK hp hU
  · have hrk8 : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) + mSub V₀ = mSub V :=
      rk_top_vtil_add_mSub V₀ V hV hH125.pairFacts.le
    have h4 := S.rk_top_eq hSK
    exact le_rMV_of_forall_rk_imgTil_le D hH125 (b := 2 * m) (c := 2 * m + mSub V₀) (by omega)
      (fun U _ hUC => rk_imgTil_le_two_mul D h61 hext h5 hS hm S hSω hSK hp hUC)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AModOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AModRankLe
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.FFC CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem c23ne_commElt_le_V {V Y : Subgroup G} (hV : IsElemAbelian 2 V) {t : G}
    (hts : t ∈ stabTil Y V) : commElt V t ≤ V := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨w, hw, rfl⟩
  have htN : t ∈ Subgroup.normalizer (V : Set G) := stabTil_le_normalizer Y V hts
  have h1 : t⁻¹ * w * t ∈ V := (Subgroup.mem_normalizer_iff''.1 htN w).1 hw
  have he : w⁻¹ * t⁻¹ * w * t = w⁻¹ * (t⁻¹ * w * t) := by group
  rw [he]
  exact V.mul_mem (V.inv_mem hw) h1

private theorem c23ne_gen_mem {V Y : Subgroup G} (hV : IsElemAbelian 2 V) {t : G}
    (hts : t ∈ stabTil Y V) {w : G} (hw : w ∈ V) : w⁻¹ * t⁻¹ * w * t ∈ V :=
  c23ne_commElt_le_V hV hts (Subgroup.subset_closure ⟨w, hw, rfl⟩)

private theorem c23ne_preTil_mono {V Y : Subgroup G} (hV : IsElemAbelian 2 V)
    {S T : Subgroup (Vtil Y V hV)} (h : S ≤ T) :
    preTil Y V hV S ≤ preTil Y V hV T := by
  intro g hg
  obtain ⟨x, rfl, hx⟩ := (mem_preTil Y V hV S).1 hg
  exact (mem_preTil Y V hV T).2 ⟨x, rfl, h hx⟩

private theorem c23ne_imgTil_mono {V Y : Subgroup G} (hV : IsElemAbelian 2 V)
    {U W : Subgroup G} (h : U ≤ W) : imgTil Y V hV U ≤ imgTil Y V hV W := by
  unfold imgTil intSub
  exact Subgroup.map_mono (Subgroup.comap_mono h)

private theorem c23ne_le_preTil {V Y : Subgroup G} (hV : IsElemAbelian 2 V) (hYV : Y ≤ V)
    (E : Subgroup (Vtil Y V hV)) : Y ≤ preTil Y V hV E := by
  intro y hy
  refine (mem_preTil Y V hV E).2 ⟨IntMod.mk hV ⟨y, hYV hy⟩, rfl, ?_⟩
  have h1 : mkTil Y V hV (IntMod.mk hV ⟨y, hYV hy⟩) = 1 :=
    (QuotientGroup.eq_one_iff (N := modNull Y V hV) _).2 hy
  rw [h1]
  exact E.one_mem

private theorem c23ne_zpow_succ_apply {W : Type*} [Group W] (τ : MulAut W) (k : ℤ) (u : W) :
    (τ ^ (k + 1)) u = τ ((τ ^ k) u) := by
  rw [Int.add_comm k 1, zpow_one_add, MulAut.mul_apply]

private theorem c23ne_zpow_pred_apply {W : Type*} [Group W] (τ : MulAut W) (k : ℤ) (u : W) :
    (τ ^ (k - 1)) u = τ⁻¹ ((τ ^ k) u) := by
  have h : k - 1 = (-1 : ℤ) + k := by ring
  rw [h, zpow_add, zpow_neg_one, MulAut.mul_apply]

private theorem c23ne_zpow_mul_inv_mem {W : Type*} [CommGroup W] (τ : MulAut W)
    (C' : Subgroup W) (hB1 : ∀ u : W, τ u * u⁻¹ ∈ C')
    (hB2 : ∀ u : W, τ⁻¹ u * u⁻¹ ∈ C') (k : ℤ) (u : W) :
    (τ ^ k) u * u⁻¹ ∈ C' := by
  induction k using Int.induction_on with
  | zero =>
      have h : (τ ^ (0 : ℤ)) u * u⁻¹ = 1 := by simp
      rw [h]
      exact C'.one_mem
  | succ i ih =>
      rw [c23ne_zpow_succ_apply]
      rw [show τ ((τ ^ (i : ℤ)) u) * u⁻¹ =
          (τ ((τ ^ (i : ℤ)) u) * ((τ ^ (i : ℤ)) u)⁻¹) *
            (((τ ^ (i : ℤ)) u) * u⁻¹) from by group]
      exact C'.mul_mem (hB1 _) ih
  | pred i ih =>
      rw [c23ne_zpow_pred_apply]
      rw [show τ⁻¹ ((τ ^ (-(i : ℤ))) u) * u⁻¹ =
          (τ⁻¹ ((τ ^ (-(i : ℤ))) u) * ((τ ^ (-(i : ℤ))) u)⁻¹) *
            (((τ ^ (-(i : ℤ))) u) * u⁻¹) from by group]
      exact C'.mul_mem (hB2 _) ih

private theorem c23ne_commSub_zpowers_le {W : Type*} [CommGroup W] (τ : MulAut W)
    (C' : Subgroup W) (hB1 : ∀ u : W, τ u * u⁻¹ ∈ C') (hB2 : ∀ u : W, τ⁻¹ u * u⁻¹ ∈ C') :
    commSub ⊤ (Subgroup.zpowers τ) ≤ C' := by
  refine (Subgroup.closure_le _).2 ?_
  rintro c ⟨x, hx, u, -, rfl⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  exact c23ne_zpow_mul_inv_mem τ C' hB1 hB2 k u

private theorem c23ne_imgTil_commElt {V Y : Subgroup G} (hV : IsElemAbelian 2 V) {t : G}
    (hts : t ∈ stabTil Y V) :
    imgTil Y V hV (commElt V t) =
      commSub ⊤ (Subgroup.zpowers (actTil Y V hV ⟨t, hts⟩)) := by
  set τ : MulAut (Vtil Y V hV) := actTil Y V hV ⟨t, hts⟩ with hτ
  have hσ : (actStab Y V hV ⟨t, hts⟩)⁻¹ = actStab Y V hV ⟨t, hts⟩⁻¹ :=
    (map_inv (actStab Y V hV) ⟨t, hts⟩).symm
  have hσmk : ∀ x : IntMod V hV,
      mkTil Y V hV ((actStab Y V hV ⟨t, hts⟩)⁻¹ x) = τ⁻¹ (mkTil Y V hV x) := by
    intro x
    rw [hσ, ← actTil_mk, map_inv]
  have hσw : ∀ w : IntMod V hV,
      (actStab Y V hV ⟨t, hts⟩)⁻¹ w =
        IntMod.mk hV ⟨t⁻¹ * w.val * t, (Subgroup.mem_normalizer_iff''.1
          (stabTil_le_normalizer Y V hts) w.val).1 w.val_mem⟩ := by
    intro w
    refine Subtype.ext ?_
    change ((actStab Y V hV ⟨t, hts⟩)⁻¹ w).val = t⁻¹ * w.val * t
    rw [hσ, actStab_apply_val]
    simp only [Subgroup.coe_inv, inv_inv, IntMod.mk, IntMod.val]
  apply le_antisymm
  · have hle : commElt V t ≤ preTil Y V hV (commSub ⊤ (Subgroup.zpowers τ)) := by
      refine (Subgroup.closure_le _).2 ?_
      rintro x ⟨w, hw, rfl⟩
      have hwV : w⁻¹ * t⁻¹ * w * t ∈ V := c23ne_gen_mem hV hts hw
      refine (mem_preTil Y V hV _).2 ⟨IntMod.mk hV ⟨w⁻¹ * t⁻¹ * w * t, hwV⟩, rfl, ?_⟩
      have hval : (IntMod.mk hV ⟨w⁻¹ * t⁻¹ * w * t, hwV⟩ : IntMod V hV) =
          (IntMod.mk hV ⟨w, hw⟩)⁻¹ * (actStab Y V hV ⟨t, hts⟩)⁻¹ (IntMod.mk hV ⟨w, hw⟩) := by
        rw [hσw (IntMod.mk hV ⟨w, hw⟩)]
        refine Subtype.ext ?_
        change w⁻¹ * t⁻¹ * w * t = w⁻¹ * (t⁻¹ * w * t)
        group
      rw [hval, map_mul, map_inv, hσmk]
      exact Subgroup.subset_closure ⟨τ⁻¹, Subgroup.inv_mem _ (Subgroup.mem_zpowers τ),
        mkTil Y V hV (IntMod.mk hV ⟨w, hw⟩), Subgroup.mem_top _, mul_comm _ _⟩
    calc imgTil Y V hV (commElt V t)
        ≤ imgTil Y V hV (preTil Y V hV (commSub ⊤ (Subgroup.zpowers τ))) :=
          c23ne_imgTil_mono hV hle
      _ = commSub ⊤ (Subgroup.zpowers τ) := imgTil_preTil Y V hV _
  · have hB2 : ∀ u : Vtil Y V hV, τ⁻¹ u * u⁻¹ ∈ imgTil Y V hV (commElt V t) := by
      intro u
      obtain ⟨w, rfl⟩ := mkTil_surjective Y V hV u
      have hgen : w.val⁻¹ * t⁻¹ * w.val * t ∈ commElt V t :=
        Subgroup.subset_closure ⟨w.val, w.val_mem, rfl⟩
      have hgenV : w.val⁻¹ * t⁻¹ * w.val * t ∈ V := c23ne_commElt_le_V hV hts hgen
      refine (mem_imgTil Y V hV (commElt V t) _).2
        ⟨IntMod.mk hV ⟨w.val⁻¹ * t⁻¹ * w.val * t, hgenV⟩, hgen, ?_⟩
      have hval : (IntMod.mk hV ⟨w.val⁻¹ * t⁻¹ * w.val * t, hgenV⟩ : IntMod V hV) =
          w⁻¹ * (actStab Y V hV ⟨t, hts⟩)⁻¹ w := by
        rw [hσw w]
        refine Subtype.ext ?_
        change w.val⁻¹ * t⁻¹ * w.val * t = w.val⁻¹ * (t⁻¹ * w.val * t)
        group
      rw [hval, map_mul, map_inv, hσmk]
      exact mul_comm _ _
    have hB1 : ∀ u : Vtil Y V hV, τ u * u⁻¹ ∈ imgTil Y V hV (commElt V t) := by
      intro u
      have h := (imgTil Y V hV (commElt V t)).inv_mem (hB2 (τ u))
      rwa [MulAut.inv_apply_self, mul_inv_rev, inv_inv] at h
    exact c23ne_commSub_zpowers_le τ _ hB1 hB2

private theorem c23ne_mSub_commElt {V Y : Subgroup G} (hV : IsElemAbelian 2 V) {t : G}
    (hts : t ∈ stabTil Y V) :
    mSub (commElt V t) =
      rk ↥(commSub ⊤ (Subgroup.zpowers (actTil Y V hV ⟨t, hts⟩))) +
        mSub (commElt V t ⊓ Y) := by
  have hU := c23ne_commElt_le_V hV hts
  rw [s15_Infra_mSub_eq_rk_imgTil_add Y V (commElt V t) hV hU,
    c23ne_imgTil_commElt hV hts]

private theorem c23ne_commElt_le_preTil_of_le {V Y : Subgroup G} (hV : IsElemAbelian 2 V) {t : G}
    (hts : t ∈ stabTil Y V) {E : Subgroup (Vtil Y V hV)}
    (hE : commSub ⊤ (Subgroup.zpowers (actTil Y V hV ⟨t, hts⟩)) ≤ E) :
    commElt V t ≤ preTil Y V hV E := by
  have hU := c23ne_commElt_le_V hV hts
  have h1 : commElt V t ≤ preTil Y V hV (imgTil Y V hV (commElt V t)) :=
    (le_inf le_rfl hU).trans (le_preTil_imgTil Y V hV (commElt V t))
  rw [c23ne_imgTil_commElt hV hts] at h1
  exact h1.trans (c23ne_preTil_mono hV hE)

private theorem c23ne_fix_of_commute {V Y : Subgroup G} (hV : IsElemAbelian 2 V) {t : G}
    (hts : t ∈ stabTil Y V) (htY : t ∈ normalizer (Y : Set G))
    (hbot : commElt V t ⊓ Y = ⊥) {E : Subgroup (Vtil Y V hV)}
    (hfix : ∀ u ∈ E, actTil Y V hV ⟨t, hts⟩ u = u) :
    ∀ y ∈ preTil Y V hV E, t * y = y * t := by
  intro y hy
  have hyV : y ∈ V := preTil_le Y V hV E hy
  have hyE : mkTil Y V hV (IntMod.mk hV ⟨y, hyV⟩) ∈ E :=
    (mem_preTil_iff_of_mem Y V hV E hyV).1 hy
  have hfy := hfix _ hyE
  have hfy' : mkTil Y V hV (actStab Y V hV ⟨t, hts⟩ (IntMod.mk hV ⟨y, hyV⟩)) =
      mkTil Y V hV (IntMod.mk hV ⟨y, hyV⟩) := by
    rw [← actTil_mk]
    exact hfy
  have hmemY : t * y * t⁻¹ * y⁻¹ ∈ Y := by
    have h := (mkTil_eq_iff Y V hV _ _).1 hfy'
    rw [actStab_apply_val] at h
    exact h
  have hzV : t⁻¹ * y * t ∈ V :=
    (Subgroup.mem_normalizer_iff''.1 (stabTil_le_normalizer Y V hts) y).1 hyV
  have hconjY : y * (t⁻¹ * y * t)⁻¹ ∈ Y := by
    have htinv : t⁻¹ ∈ normalizer (Y : Set G) :=
      (Subgroup.normalizer (Y : Set G)).inv_mem htY
    have h4 : t⁻¹ * (t * y * t⁻¹ * y⁻¹) * t ∈ Y := by
      have h := (Subgroup.mem_normalizer_iff.1 htinv _).1 hmemY
      simpa using h
    rwa [show t⁻¹ * (t * y * t⁻¹ * y⁻¹) * t = y * (t⁻¹ * y * t)⁻¹ by group] at h4
  have hfinal : y⁻¹ * t⁻¹ * y * t ∈ Y := by
    have h5 : ((y * (t⁻¹ * y * t)⁻¹))⁻¹ ∈ Y := Y.inv_mem hconjY
    have h5' : (t⁻¹ * y * t) * y⁻¹ ∈ Y := by
      rwa [show (y * (t⁻¹ * y * t)⁻¹)⁻¹ = (t⁻¹ * y * t) * y⁻¹ by group] at h5
    have hcommV : y⁻¹ * t⁻¹ * y * t = (t⁻¹ * y * t) * y⁻¹ := by
      rw [show y⁻¹ * t⁻¹ * y * t = y⁻¹ * (t⁻¹ * y * t) by group]
      exact IntMod.val_comm (hV := hV) (⟨y⁻¹, V.inv_mem hyV⟩ : IntMod V hV)
        ⟨t⁻¹ * y * t, hzV⟩
    rw [hcommV]
    exact h5'
  have hmemComm : y⁻¹ * t⁻¹ * y * t ∈ commElt V t :=
    Subgroup.subset_closure ⟨y, hyV, rfl⟩
  have hzero : y⁻¹ * t⁻¹ * y * t = 1 := by
    have h : y⁻¹ * t⁻¹ * y * t ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact ⟨hmemComm, hfinal⟩
    exact Subgroup.mem_bot.1 h
  have h3 : t⁻¹ * y * t = y := by
    have h := congrArg (fun z => y * z) hzero
    rw [mul_one] at h
    calc t⁻¹ * y * t = y * (y⁻¹ * t⁻¹ * y * t) := by group
      _ = y := h
  have h4 : y * t = t * y := by
    calc y * t = t * (t⁻¹ * y * t) := by group
      _ = t * y := by rw [h3]
  exact h4.symm

private theorem c23ne_mQuot_CTilde_eq_rk_barSub {M V Y : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (hMY : M ≤ normalizer (Y : Set G)) {E : Subgroup G}
    (hEM : E ≤ M) : E3.mQuot E (F11.CTilde M Y V) = rk ↥(barSub Y V hV E) := by
  classical
  have hEs : E ≤ stabTil Y V := le_stabTil (hEM.trans hM) (hEM.trans hMY)
  let f : ↥E →* MulAut (Vtil Y V hV) :=
    (actTil Y V hV).comp (Subgroup.inclusion hEs)
  have hrange : f.range = barSub Y V hV E := by
    ext φ
    rw [MonoidHom.mem_range, mem_barSub]
    constructor
    · rintro ⟨e, rfl⟩
      exact ⟨⟨(e : G), hEs e.2⟩, e.2, rfl⟩
    · rintro ⟨g, hgE, rfl⟩
      exact ⟨⟨(g : G), hgE⟩, rfl⟩
  have hker : f.ker = (F11.CTilde M Y V).subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_cTilde_iff hV hM]
    constructor
    · intro h
      exact ⟨hEM e.2, hEs e.2, h⟩
    · rintro ⟨-, h1⟩
      obtain ⟨h, hh⟩ := h1
      exact hh
  have hcard : Nat.card ↥(barSub Y V hV E) = f.ker.index := by
    rw [Subgroup.index_ker f, hrange]
  unfold E3.mQuot rk
  rw [hcard, hker, Subgroup.relIndex]

theorem c23ne_bridge_oneSided {M V Y : Subgroup G} (hV : IsElemAbelian 2 V) (hYV : Y ≤ V)
    (hM : M ≤ normalizer (V : Set G)) (hMY : M ≤ normalizer (Y : Set G)) (hY1 : mSub Y = 1)
    {L₁ L₂ : Subgroup (MulAut (Vtil Y V hV))} {E₁ E₂ Z₁ Z₂ : Subgroup (Vtil Y V hV)}
    (hP : C23AModPair (barSub Y V hV M) L₁ L₂ E₁ E₂ Z₁ Z₂) :
    ∀ t ∈ M, t ^ 2 = 1 → ¬ V ≤ centralizer ({t} : Set G) → mSub (commElt V t) ≤ 2 →
      (mSub (commElt V t) = 1 ∧ commElt V t = Y) ∨
      (mSub (commElt V t) = 2 ∧ commElt V t ⊓ Y = ⊥ ∧
        (((∀ y ∈ preTil Y V hV E₂, t * y = y * t) ∧ commElt V t ≤ preTil Y V hV E₁) ∨
          ((∀ y ∈ preTil Y V hV E₁, t * y = y * t) ∧ commElt V t ≤ preTil Y V hV E₂))) := by
  intro t htM ht2 hnc hm
  have hts : t ∈ stabTil Y V := le_stabTil hM hMY htM
  set τ : MulAut (Vtil Y V hV) := actTil Y V hV ⟨t, hts⟩ with hτ
  have hτ2 : ∃ j : ℕ, orderOf τ = 2 ^ j := by
    have h0 : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one ht2
    have h1 : orderOf (actTil Y V hV ⟨t, hts⟩) ∣ orderOf (⟨t, hts⟩ : ↥(stabTil Y V)) :=
      orderOf_map_dvd _ _
    rw [Subgroup.orderOf_mk] at h1
    have h2 : orderOf τ ∣ 2 := by
      rw [hτ]
      exact h1.trans h0
    have h2' : orderOf τ ∣ 2 ^ 1 := by simpa using h2
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2'
    exact ⟨a, ha⟩
  have hmSub := c23ne_mSub_commElt hV hts
  rw [← hτ] at hmSub
  have hne : commElt V t ≠ ⊥ := by
    intro hbot
    apply hnc
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    by_contra hc
    have hgen : v⁻¹ * t⁻¹ * v * t ∈ commElt V t :=
      Subgroup.subset_closure ⟨v, hv, rfl⟩
    rw [hbot] at hgen
    have h1 : v⁻¹ * t⁻¹ * v * t = 1 := Subgroup.mem_bot.1 hgen
    apply hc
    have h2 : t⁻¹ * v * t = v := by
      have h := congrArg (fun z => v * z) h1
      rw [mul_one] at h
      calc t⁻¹ * v * t = v * (v⁻¹ * t⁻¹ * v * t) := by group
        _ = v := h
    calc v * t = t * (t⁻¹ * v * t) := by group
      _ = t * v := by rw [h2]
  have hYcard : Nat.card Y = 2 := by
    rw [card_eq_two_pow_mSub (hV.mono hYV).isPGroup, hY1, pow_one]
  by_cases hτ1 : τ = 1
  · left
    have hbot : commSub ⊤ (Subgroup.zpowers τ) = ⊥ := by
      rw [hτ1, Subgroup.zpowers_one_eq_bot]
      rw [commSub_eq_bot_iff]
      intro v _
      exact mem_fixV.2 (fun x hx => by rw [Subgroup.mem_bot.1 hx, MulAut.one_apply])
    have hleY : commElt V t ≤ Y := by
      have h1 := c23ne_commElt_le_preTil_of_le hV hts (E := ⊥) (le_of_eq hbot)
      rwa [preTil_bot, inf_eq_right.mpr hYV] at h1
    have hcommEqY : commElt V t = Y := by
      have hdvd : Nat.card ↥(commElt V t) ∣ Nat.card ↥Y := Subgroup.card_dvd_of_le hleY
      rw [hYcard] at hdvd
      have hne1 : Nat.card ↥(commElt V t) ≠ 1 := fun h1 =>
        hne ((Subgroup.card_eq_one).1 h1)
      have hc2 : Nat.card ↥(commElt V t) = 2 := by
        rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
        · exact absurd h hne1
        · exact h
      exact Subgroup.eq_of_le_of_card_ge hleY (by omega)
    exact ⟨by rw [hcommEqY, hY1], hcommEqY⟩
  · right
    have hr : rk ↥(commSub ⊤ (Subgroup.zpowers τ)) ≤ 2 := by omega
    have hmain := c23a_modPair_oneSided (t := τ) hP
      (actTil_mem_barSub Y V hV htM hts) hτ2 hτ1 hr
    have h2rk : rk ↥(commSub ⊤ (Subgroup.zpowers τ)) = 2 := by omega
    have h0 : mSub (commElt V t ⊓ Y) = 0 := by omega
    have hm2 : mSub (commElt V t) = 2 := by omega
    have hbot : commElt V t ⊓ Y = ⊥ := by
      refine (rk_eq_zero_iff_of_isPGroup (hV.mono (inf_le_right.trans hYV)).isPGroup).1 ?_
      change rk ↥(commElt V t ⊓ Y) = 0
      exact h0
    refine ⟨hm2, hbot, ?_⟩
    rcases hmain.1 with ⟨hfix₂, hle₂⟩ | ⟨hfix₁, hle₁⟩
    · exact Or.inl ⟨c23ne_fix_of_commute hV hts (hMY htM) hbot hfix₂,
        c23ne_commElt_le_preTil_of_le hV hts hle₂⟩
    · exact Or.inr ⟨c23ne_fix_of_commute hV hts (hMY htM) hbot hfix₁,
        c23ne_commElt_le_preTil_of_le hV hts hle₁⟩

theorem c23ne_bridge_twoElt {M V Y : Subgroup G} (hV : IsElemAbelian 2 V) (hYV : Y ≤ V)
    (hM : M ≤ normalizer (V : Set G)) (hMY : M ≤ normalizer (Y : Set G))
    {L₁ L₂ : Subgroup (MulAut (Vtil Y V hV))} {E₁ E₂ Z₁ Z₂ : Subgroup (Vtil Y V hV)}
    (hP : C23AModPair (barSub Y V hV M) L₁ L₂ E₁ E₂ Z₁ Z₂) :
    ∀ t ∈ M, (∃ j : ℕ, orderOf t = 2 ^ j) → ¬ V ≤ centralizer ({t} : Set G) →
      mSub (commElt V t) ≤ 2 →
        commElt V t ≤ preTil Y V hV E₁ ∨ commElt V t ≤ preTil Y V hV E₂ := by
  intro t htM ht2 hnc hm
  have hts : t ∈ stabTil Y V := le_stabTil hM hMY htM
  set τ : MulAut (Vtil Y V hV) := actTil Y V hV ⟨t, hts⟩ with hτ
  have hτ2 : ∃ j : ℕ, orderOf τ = 2 ^ j := by
    obtain ⟨j, hj⟩ := ht2
    have h1 : orderOf (actTil Y V hV ⟨t, hts⟩) ∣ orderOf (⟨t, hts⟩ : ↥(stabTil Y V)) :=
      orderOf_map_dvd _ _
    rw [Subgroup.orderOf_mk] at h1
    have h2 : orderOf τ ∣ 2 ^ j := by
      rw [hτ]
      rw [hj] at h1
      exact h1
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    exact ⟨a, ha⟩
  have hmSub := c23ne_mSub_commElt hV hts
  rw [← hτ] at hmSub
  have hr : rk ↥(commSub ⊤ (Subgroup.zpowers τ)) ≤ 2 := by omega
  by_cases hτ1 : τ = 1
  · have hbot : commSub ⊤ (Subgroup.zpowers τ) = ⊥ := by
      rw [hτ1, Subgroup.zpowers_one_eq_bot]
      rw [commSub_eq_bot_iff]
      intro v _
      exact mem_fixV.2 (fun x hx => by rw [Subgroup.mem_bot.1 hx, MulAut.one_apply])
    have hU := c23ne_commElt_le_V hV hts
    have h1 : commElt V t ≤ preTil Y V hV (imgTil Y V hV (commElt V t)) :=
      (le_inf le_rfl hU).trans (le_preTil_imgTil Y V hV (commElt V t))
    rw [c23ne_imgTil_commElt hV hts, hbot, preTil_bot, inf_eq_right.mpr hYV] at h1
    exact Or.inl (h1.trans (c23ne_le_preTil hV hYV E₁))
  · rcases (c23a_modPair_oneSided (t := τ) hP
      (actTil_mem_barSub Y V hV htM hts) hτ2 hτ1 hr).1 with
      ⟨-, hle₁⟩ | ⟨-, hle₂⟩
    · exact Or.inl (c23ne_commElt_le_preTil_of_le hV hts hle₁)
    · exact Or.inr (c23ne_commElt_le_preTil_of_le hV hts hle₂)

theorem c23ne_bridge_rankLe {M V Y : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (hMY : M ≤ normalizer (Y : Set G))
    {L₁ L₂ : Subgroup (MulAut (Vtil Y V hV))} {E₁ E₂ Z₁ Z₂ : Subgroup (Vtil Y V hV)}
    (hP : C23AModPair (barSub Y V hV M) L₁ L₂ E₁ E₂ Z₁ Z₂) :
    ∀ E : Subgroup G, E ≤ M → IsElemAbelian 2 E →
      (∀ e ∈ E, e ∈ normalizer (preTil Y V hV E₁ : Set G)) →
      (∀ e ∈ E, ∀ y ∈ preTil Y V hV E₂, e * y = y * e) →
        E3.mQuot E (F11.CTilde M Y V) ≤ 2 := by
  intro E hEM hel hnorm hcent
  let A : Subgroup (MulAut (Vtil Y V hV)) := barSub Y V hV E
  have hA : A ≤ barSub Y V hV M := barSub_mono Y V hV hEM
  have hAel : IsElemAbelian 2 A := by
    change IsElemAbelian 2 ((E.subgroupOf (stabTil Y V)).map (actTil Y V hV))
    exact (hel.subgroupOf (stabTil Y V)).map (actTil Y V hV)
  have hnorm' : ∀ a ∈ A, ∀ u ∈ E₁, a u ∈ E₁ := by
    intro a ha u hu
    obtain ⟨g, hgE, hga⟩ := (mem_barSub Y V hV E a).1 ha
    rw [← hga]
    obtain ⟨z, rfl⟩ := mkTil_surjective Y V hV u
    have hzpre : z.val ∈ preTil Y V hV E₁ :=
      (mem_preTil Y V hV E₁).2 ⟨z, rfl, hu⟩
    have hgz : (g : G) * z.val * (g : G)⁻¹ ∈ preTil Y V hV E₁ :=
      (Subgroup.mem_normalizer_iff.1 (hnorm (g : G) hgE) z.val).1 hzpre
    have h2 : mkTil Y V hV (actStab Y V hV g z) ∈ E₁ := by
      obtain ⟨x, hxval, hxmem⟩ := (mem_preTil Y V hV E₁).1 hgz
      have hxz : x = actStab Y V hV g z := by
        apply IntMod.val_injective
        rw [actStab_apply_val, hxval]
      rwa [← hxz]
    rw [actTil_mk]
    exact h2
  have hcent' : ∀ a ∈ A, ∀ y ∈ E₂, a y = y := by
    intro a ha y hy
    obtain ⟨g, hgE, hga⟩ := (mem_barSub Y V hV E a).1 ha
    rw [← hga]
    obtain ⟨z, rfl⟩ := mkTil_surjective Y V hV y
    have hzpre : z.val ∈ preTil Y V hV E₂ :=
      (mem_preTil Y V hV E₂).2 ⟨z, rfl, hy⟩
    have hcomm : (g : G) * z.val = z.val * (g : G) := hcent (g : G) hgE z.val hzpre
    have heq : actStab Y V hV g z = z := by
      apply IntMod.val_injective
      rw [actStab_apply_val, hcomm]
      group
    rw [actTil_mk, heq]
  have hle : rk ↥A ≤ 2 := c23a_modPair_rankLe hP hA hAel hnorm' hcent'
  rw [c23ne_mQuot_CTilde_eq_rk_barSub hV hM hMY hEM]
  exact hle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

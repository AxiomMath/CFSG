module

public import CFSG.Monster.B.GSide.HInnerFusion
public import CFSG.Monster.B.GSide.HSylowCenter
public import CFSG.Monster.B.Cbar.Simple
public import CFSG.Monster.B.CTIB.OddCoreFree
public import CFSG.Monster.B.CTIB.Rep4371Rho
public import Certificates.Certificate3011
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3057
public import Certificates.Certificate3058
public import Certificates.Certificate3060
public import Certificates.Certificate3061
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3118
public import Certificates.Certificate16022
public import Certificates.Certificate3027
public import Certificates.Certificate16951

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open MulOpposite CFSG.Blueprint CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short
  CFSG.Monster.B.CTIB CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster.B.CTIB.Native (qmul gArr autApply genImgs repRanks)

local notation "vR" => SpinLattice.phi0 (Griess.coordOf rStar)

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

@[expose] def QhatS : Subgroup Shat := Ehat.subgroupOf Shat

theorem mem_QhatS {s : Shat} : s ∈ QhatS ↔ (s : Dfull) ∈ Ehat := Subgroup.mem_subgroupOf

theorem mem_centralizer_xhatS {s : Shat} :
    s ∈ Subgroup.centralizer {xhatS} ↔ (s : Dfull) ∈ Jhat := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← centralizer_xhat,
    Subgroup.mem_centralizer_singleton_iff]
  exact Subtype.ext_iff

theorem QhatS_le_centralizer :
    QhatS ≤ Subgroup.centralizer {xhatS} := fun _ hs =>
  mem_centralizer_xhatS.2 (Ehat_le_Jhat (mem_QhatS.1 hs))

theorem xhatS_mem_QhatS : xhatS ∈ QhatS := mem_QhatS.2 xhat_mem_Ehat

theorem conj_mem_QhatS
    {g : Shat} (hg : g ∈ Subgroup.centralizer {xhatS}) {q : Shat}
    (hq : q ∈ QhatS) : g * q * g⁻¹ ∈ QhatS := by
  rw [mem_QhatS]
  have h := conj_mem_Ehat (Jhat.inv_mem (mem_centralizer_xhatS.1 hg)) (mem_QhatS.1 hq)
  rwa [inv_inv] at h

theorem mul_self_of_mem_QhatS {q : Shat} (hq : q ∈ QhatS) : q * q = 1 ∨ q * q = xhatS := by
  rcases Ehat_sq_mem (mem_QhatS.1 hq) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem comm_of_mem_QhatS {q r : Shat} (hq : q ∈ QhatS) (hr : r ∈ QhatS) :
    q * r = r * q ∨ q * r = r * q * xhatS := by
  have h := Ehat_comm ⟨q, mem_QhatS.1 hq⟩ ⟨r, mem_QhatS.1 hr⟩
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases h01 (bV (psiW ⟨q, mem_QhatS.1 hq⟩) (psiW ⟨r, mem_QhatS.1 hr⟩)) with h0 | h0 <;>
    rw [h0] at h
  · left
    apply Subtype.ext
    rw [ZMod.val_zero, pow_zero, mul_one] at h
    exact h
  · right
    apply Subtype.ext
    rw [show (1 : ZMod 2).val = 1 from rfl, pow_one] at h
    exact h

theorem xhatS_comm {g : Shat} (hg : g ∈ Subgroup.centralizer {xhatS}) :
    g * xhatS = xhatS * g :=
  Subgroup.mem_centralizer_singleton_iff.1 hg

theorem xhatS_mul_self : xhatS * xhatS = 1 := Subtype.ext xhat_mul_self

theorem cbarEquiv_xbar : cbarEquiv xbar = xhatS := Subtype.ext iotaD_xbar

theorem cbarEquiv_mem_QhatS {c : Cbar} : cbarEquiv c ∈ QhatS ↔ c ∈ Ebar := by
  rw [mem_QhatS, coe_cbarEquiv, Ehat]
  exact Subgroup.mem_map_iff_mem iotaD_injective

theorem cbarEquiv_mem_centralizer {c : Cbar} :
    cbarEquiv c ∈ Subgroup.centralizer {xhatS} ↔ c ∈ Jbar := by
  rw [mem_centralizer_xhatS, coe_cbarEquiv, Jhat_eq_map]
  exact Subgroup.mem_map_iff_mem iotaD_injective

theorem map_Ebar_cbarEquiv : Ebar.map cbarEquiv.toMonoidHom = QhatS := by
  ext s
  rw [Subgroup.mem_map_equiv, ← cbarEquiv_mem_QhatS, MulEquiv.apply_symm_apply]

theorem map_Jbar_cbarEquiv :
    Jbar.map cbarEquiv.toMonoidHom = Subgroup.centralizer {xhatS} := by
  ext s
  rw [Subgroup.mem_map_equiv, ← cbarEquiv_mem_centralizer, MulEquiv.apply_symm_apply]

theorem natCard_centralizer_xhatS :
    Nat.card (Subgroup.centralizer {xhatS}) = 2 ^ 41 * 3 ^ 6 * 5 ^ 3 * 7 * 11 * 23 := by
  rw [← map_Jbar_cbarEquiv,
    Subgroup.card_map_of_injective (f := cbarEquiv.toMonoidHom) cbarEquiv.injective,
    natCard_Jbar_eq]
  norm_num

theorem xbar_comm_of_mem_Jbar
    {h : Cbar} (hh : h ∈ Jbar) : h * xbar = xbar * h := by
  rw [← centralizer_xbar] at hh
  exact Subgroup.mem_centralizer_singleton_iff.1 hh

theorem mem_QhatS_of_conj
    {g : Shat} (hg : g ∈ Subgroup.centralizer {xhatS})
    (h : ∀ q ∈ QhatS, g * q * g⁻¹ = q ∨ g * q * g⁻¹ = q * xhatS) : g ∈ QhatS := by
  have hgs := cbarEquiv.surjective g
  obtain ⟨c, rfl⟩ := hgs
  rw [cbarEquiv_mem_centralizer] at hg
  rw [cbarEquiv_mem_QhatS]
  refine mem_Ebar_of_comm hg fun x hx => ?_
  have hxc := xbar_comm_of_mem_Jbar (Ebar_le_Jbar hx)
  rcases h (cbarEquiv x) (cbarEquiv_mem_QhatS.2 hx) with h1 | h1
  · have e : c * x * c⁻¹ = x := cbarEquiv.injective (by
      rw [map_mul, map_mul, map_inv]
      exact h1)
    rw [e, mul_inv_cancel]
    exact Subgroup.one_mem _
  · have e : c * x * c⁻¹ = x * xbar := cbarEquiv.injective (by
      rw [map_mul, map_mul, map_inv, map_mul, cbarEquiv_xbar]
      exact h1)
    rw [e, hxc, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers _

theorem commutator_mul_central {G : Type*} [Group G] {a b z w : G} (hzb : z * b = b * z)
    (hwa : w * a = a * w) (hzw : z * w = w * z) :
    a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have hwa' : w * a⁻¹ = a⁻¹ * w := (Commute.inv_right (show Commute w a from hwa)).eq
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹ = a * (z * b) * w * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by
        group
    _ = a * b * (z * w) * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by rw [hzb]; group
    _ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by rw [hzw]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [hwa']; group

theorem comm_of_mem_zpowers_xbar
    {z h : Cbar} (hz : z ∈ Subgroup.zpowers xbar) (hh : h ∈ Jbar) :
    z * h = h * z := by
  rcases (mem_zpowers_xbar_iff z).1 hz with rfl | rfl
  · rw [one_mul, mul_one]
  · exact (xbar_comm_of_mem_Jbar hh).symm

theorem xbar_mem_of_invariant
    {R : Subgroup Cbar} (hR : ∀ h ∈ Jbar, ∀ r ∈ R, h * r * h⁻¹ ∈ R)
    (hRE : R ≤ Ebar) (hsub : ¬ R ≤ Subgroup.zpowers xbar) : xbar ∈ R := by
  obtain ⟨-, h22, hirr⟩ := Kv_rStar_facts
  set U := AddSubgroup.toZModSubmodule 2 (psiSub R hRE) with hU
  have hmemU : ∀ w, w ∈ U ↔ w ∈ psiSub R hRE := fun w => AddSubgroup.mem_toZModSubmodule 2
  have hinv : ∀ (k : Kstab vR) (w : Wv vR), w ∈ U →
      wAct vR k w ∈ U := by
    intro k w hw
    rw [hmemU] at hw ⊢
    obtain ⟨r, hr, rfl⟩ := hw
    obtain ⟨g, rfl⟩ := jbarToKv_surjective k
    have hgr : (g : Cbar)⁻¹ * r * g ∈ R := by
      have := hR _ (Jbar.inv_mem g.2) r hr
      rwa [inv_inv] at this
    refine ⟨_, hgr, ?_⟩
    rw [psiBar_conj g.2 (hRE hr), toAdd_ofAdd]
  have hU0 : U ≠ ⊥ := by
    obtain ⟨r, hr, hrz⟩ := IsConcreteLE.not_le_iff_exists.1 hsub
    intro h
    have hw : Multiplicative.toAdd (psiBar ⟨r, hRE hr⟩) ∈ U := (hmemU _).2 ⟨r, hr, rfl⟩
    rw [h, Submodule.mem_bot] at hw
    exact hrz ((psiBar_eq_one_iff' (hRE hr)).1 (toAdd_eq_zero.1 hw))
  have hUtop : U = ⊤ := (hirr U hinv).resolve_left hU0
  have hlift : ∀ e ∈ Ebar, ∃ r ∈ R, r⁻¹ * e ∈ Subgroup.zpowers xbar := fun e he => by
    have hw : Multiplicative.toAdd (psiBar ⟨e, he⟩) ∈ U := by
      rw [hUtop]
      exact Submodule.mem_top
    obtain ⟨r, hr, hre⟩ := (hmemU _).1 hw
    have hmem : r⁻¹ * e ∈ Ebar := Ebar.mul_mem (Ebar.inv_mem (hRE hr)) he
    refine ⟨r, hr, (psiBar_eq_one_iff' hmem).1 ?_⟩
    have h2 : (⟨r⁻¹ * e, hmem⟩ : Ebar) = (⟨r, hRE hr⟩ : Ebar)⁻¹ * ⟨e, he⟩ := rfl
    rw [h2, map_mul, map_inv, inv_mul_eq_one]
    exact Multiplicative.toAdd.injective hre
  have hW : Nontrivial (Wv vR) :=
    Module.nontrivial_of_finrank_pos (by rw [h22]; norm_num)
  obtain ⟨q₀, hq₀, hq₀z⟩ := exists_Ebar_not_mem_zpowers hW
  have hnc : ¬ ∀ x ∈ Ebar, x * q₀ = q₀ * x := fun h =>
    hq₀z ((center_Ebar_iff map_center_Ebar hq₀).1 h)
  push Not at hnc
  obtain ⟨q₁, hq₁, hne⟩ := hnc
  have hx : q₁ * q₀ * q₁⁻¹ * q₀⁻¹ = xbar := by
    rcases (mem_zpowers_xbar_iff _).1 (comm_mem_zpowers_xbar hq₁ hq₀) with h | h
    · exact absurd (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h)) hne
    · exact h
  obtain ⟨r₀, hr₀, hz₀⟩ := hlift q₀ hq₀
  obtain ⟨r₁, hr₁, hz₁⟩ := hlift q₁ hq₁
  have hJ : ∀ {y : Cbar}, y ∈ Ebar → y ∈ Jbar := fun hy => Ebar_le_Jbar hy
  have e₀ : r₀ * (r₀⁻¹ * q₀) = q₀ := mul_inv_cancel_left r₀ q₀
  have e₁ : r₁ * (r₁⁻¹ * q₁) = q₁ := mul_inv_cancel_left r₁ q₁
  have hcomm := commutator_mul_central (a := r₁) (b := r₀)
    (comm_of_mem_zpowers_xbar hz₁ (hJ (hRE hr₀)))
    (comm_of_mem_zpowers_xbar hz₀ (hJ (hRE hr₁)))
    (comm_of_mem_zpowers_xbar hz₁ (hJ (Ebar.mul_mem (Ebar.inv_mem (hRE hr₀)) hq₀)))
  rw [e₀, e₁, hx] at hcomm
  rw [hcomm]
  exact R.mul_mem (R.mul_mem (R.mul_mem hr₁ hr₀) (R.inv_mem hr₁)) (R.inv_mem hr₀)

theorem eq_of_invariant_Ebar
    (R : Subgroup Cbar) (hR : ∀ h ∈ Jbar, ∀ r ∈ R, h * r * h⁻¹ ∈ R)
    (hRE : R ≤ Ebar) : R = ⊥ ∨ R = Subgroup.zpowers xbar ∨ R = Ebar := by
  by_cases hsub : R ≤ Subgroup.zpowers xbar
  · by_cases hx : xbar ∈ R
    · exact Or.inr (Or.inl (le_antisymm hsub ((Subgroup.zpowers_le).2 hx)))
    · left
      rw [eq_bot_iff]
      intro r hr
      rcases (mem_zpowers_xbar_iff r).1 (hsub hr) with h | h
      · exact (Subgroup.mem_bot).2 h
      · exact absurd (h ▸ hr) hx
  · have hx := xbar_mem_of_invariant hR hRE hsub
    obtain ⟨-, -, hirr⟩ := Kv_rStar_facts
    rcases eq_of_invariant jbarToKv_surjective hirr R hR ((Subgroup.zpowers_le).2 hx) hRE with
      h | h
    · exact absurd h.le hsub
    · exact Or.inr (Or.inr h)

theorem eq_of_invariant_QhatS
    (R : Subgroup Shat) (hRQ : R ≤ QhatS)
    (hR : ∀ g ∈ Subgroup.centralizer {xhatS}, ∀ r ∈ R, g * r * g⁻¹ ∈ R) :
    R = ⊥ ∨ R = Subgroup.zpowers xhatS ∨ R = QhatS := by
  have hRE : R.comap cbarEquiv.toMonoidHom ≤ Ebar := fun c hc =>
    cbarEquiv_mem_QhatS.1 (hRQ hc)
  have hR' : ∀ h ∈ Jbar, ∀ r ∈ R.comap cbarEquiv.toMonoidHom,
      h * r * h⁻¹ ∈ R.comap cbarEquiv.toMonoidHom := fun h hh r hr => by
    show cbarEquiv (h * r * h⁻¹) ∈ R
    rw [map_mul, map_mul, map_inv]
    exact hR _ (cbarEquiv_mem_centralizer.2 hh) _ hr
  have hRmap : (R.comap cbarEquiv.toMonoidHom).map cbarEquiv.toMonoidHom = R :=
    Subgroup.map_comap_eq_self_of_surjective (f := cbarEquiv.toMonoidHom) cbarEquiv.surjective R
  rcases eq_of_invariant_Ebar _ hR' hRE with h | h | h <;> rw [h] at hRmap <;> rw [← hRmap]
  · exact Or.inl (Subgroup.map_bot _)
  · refine Or.inr (Or.inl ?_)
    rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, cbarEquiv_xbar]
  · exact Or.inr (Or.inr map_Ebar_cbarEquiv)

theorem eq_of_normal_Ebar
    (R : Subgroup Cbar) (hER : Ebar ≤ R) (hRJ : R ≤ Jbar)
    (hR : ∀ h ∈ Jbar, ∀ r ∈ R, h * r * h⁻¹ ∈ R) : R = Ebar ∨ R = Jbar := by
  obtain ⟨hsimple, -, -⟩ := Kv_rStar_facts
  have : IsSimpleGroup (Jbar ⧸ Ebar.subgroupOf Jbar) :=
    isSimpleGroup_Jbar_quot jbarToKv_surjective
  have hRn : (R.subgroupOf Jbar).Normal :=
    ⟨fun n hn g => Subgroup.mem_subgroupOf.2 (hR _ g.2 _ (Subgroup.mem_subgroupOf.1 hn))⟩
  have hNn : ((R.subgroupOf Jbar).map (QuotientGroup.mk' (Ebar.subgroupOf Jbar))).Normal :=
    hRn.map (QuotientGroup.mk' (Ebar.subgroupOf Jbar)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((R.subgroupOf Jbar).map (QuotientGroup.mk' (Ebar.subgroupOf Jbar))) with h | h
  · left
    refine le_antisymm (fun r hr => ?_) hER
    have hmem : QuotientGroup.mk' (Ebar.subgroupOf Jbar) ⟨r, hRJ hr⟩ ∈
        (R.subgroupOf Jbar).map (QuotientGroup.mk' (Ebar.subgroupOf Jbar)) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hr)
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact Subgroup.mem_subgroupOf.1 hmem
  · right
    refine le_antisymm hRJ (fun g hg => ?_)
    have hmem : QuotientGroup.mk' (Ebar.subgroupOf Jbar) ⟨g, hg⟩ ∈
        (R.subgroupOf Jbar).map (QuotientGroup.mk' (Ebar.subgroupOf Jbar)) := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨r, hr, hrg⟩ := hmem
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hrg
    have h1 : ((r⁻¹ * ⟨g, hg⟩ : Jbar) : Cbar) ∈ R := hER (Subgroup.mem_subgroupOf.1 hrg)
    have h2 := R.mul_mem (Subgroup.mem_subgroupOf.1 hr) h1
    rwa [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] at h2

theorem eq_of_normal_QhatS
    (R : Subgroup Shat) (hQR : QhatS ≤ R)
    (hRC : R ≤ Subgroup.centralizer {xhatS})
    (hR : ∀ g ∈ Subgroup.centralizer {xhatS}, ∀ r ∈ R, g * r * g⁻¹ ∈ R) :
    R = QhatS ∨ R = Subgroup.centralizer {xhatS} := by
  have hER : Ebar ≤ R.comap cbarEquiv.toMonoidHom := fun c hc =>
    hQR (cbarEquiv_mem_QhatS.2 hc)
  have hRJ : R.comap cbarEquiv.toMonoidHom ≤ Jbar := fun c hc =>
    cbarEquiv_mem_centralizer.1 (hRC hc)
  have hR' : ∀ h ∈ Jbar, ∀ r ∈ R.comap cbarEquiv.toMonoidHom,
      h * r * h⁻¹ ∈ R.comap cbarEquiv.toMonoidHom := fun h hh r hr => by
    show cbarEquiv (h * r * h⁻¹) ∈ R
    rw [map_mul, map_mul, map_inv]
    exact hR _ (cbarEquiv_mem_centralizer.2 hh) _ hr
  have hRmap : (R.comap cbarEquiv.toMonoidHom).map cbarEquiv.toMonoidHom = R :=
    Subgroup.map_comap_eq_self_of_surjective (f := cbarEquiv.toMonoidHom) cbarEquiv.surjective R
  rcases eq_of_normal_Ebar _ hER hRJ hR' with h | h <;> rw [h] at hRmap <;> rw [← hRmap]
  · exact Or.inl map_Ebar_cbarEquiv
  · exact Or.inr map_Jbar_cbarEquiv

theorem coe_sEquiv (u : Sbp) : ((sEquiv u : Shat) : Dfull) = (iotaD u.unop)⁻¹ := rfl

theorem sEquiv_mem_QhatS {u : Sbp} : sEquiv u ∈ QhatS ↔ u ∈ Qs := by
  rw [mem_QhatS, coe_sEquiv, inv_mem_iff, Ehat, Subgroup.mem_map_iff_mem iotaD_injective]
  rfl

theorem sEquiv_mem_centralizer {u : Sbp} :
    sEquiv u ∈ Subgroup.centralizer {xhatS} ↔ u.unop ∈ Jbar := by
  rw [mem_centralizer_xhatS, coe_sEquiv, inv_mem_iff, Jhat_eq_map,
    Subgroup.mem_map_iff_mem iotaD_injective]

theorem coe_cV0_dfull :
    (((cV0 : vStab cv0) : Shat) : Dfull) = cQ := by
  rw [coe_cV0, coe_clabelS, clabel_cv0]

theorem isConj_sEquiv_iff {a b : Sbp} : IsConj (sEquiv a) (sEquiv b) ↔ IsConj a b := by
  refine ⟨fun h => ?_, fun h => sEquiv.toMonoidHom.map_isConj h⟩
  have h' := sEquiv.symm.toMonoidHom.map_isConj h
  simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using h'

theorem mem_jClass_of_isConj_labelS
    {t : Sbp} (ht : t ∈ Qs) (hc : IsConj labelS t) :
    t ∈ jClass (qS 1) := by
  have hrk : ((βr t) - 1).rank = 1860 := (rank_beta_conj hc).symm.trans rank_labelS
  obtain ⟨g, rfl⟩ := isConj_iff.1 hc
  have hsq : g * labelS * g⁻¹ * (g * labelS * g⁻¹) = 1 := by
    calc g * labelS * g⁻¹ * (g * labelS * g⁻¹) = g * (labelS * labelS) * g⁻¹ := by group
      _ = 1 := by rw [mul_self_of_mem_jClass labelS_mem_jClass, mul_one, mul_inv_cancel]
  have hne : g * labelS * g⁻¹ ≠ 1 := fun h => one_not_mem_jClass (by
    have e : labelS = 1 := by
      calc labelS = g⁻¹ * (g * labelS * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    rw [← e]
    exact labelS_mem_jClass)
  have hmem : g * labelS * g⁻¹ ∈ {t | t ∈ Qs ∧ t * t = 1 ∧ t ≠ 1} := ⟨ht, hsq, hne⟩
  rw [invs_eq] at hmem
  have hr : ∀ i < 14, g * labelS * g⁻¹ ∈ jClass (rs i) → 1860 = repRanks.getD i 0 := by
    intro i hi h
    rw [← hrk, rank_beta_conj (isConj_of_mem_jClass h), rank_rs hi]
  rcases hmem with ((h | h) | h) | h
  · exact absurd (hr 0 (by norm_num) h) (by decide)
  · rwa [rs1_eq] at h
  · exact absurd (hr 2 (by norm_num) h) (by decide)
  · exact absurd (hr 3 (by norm_num) h) (by decide)

theorem isConj_labelS_of_mem_jClass
    {t : Sbp} (ht : t ∈ jClass (qS 1)) : IsConj labelS t :=
  (isConj_of_mem_jClass labelS_mem_jClass).trans (isConj_of_mem_jClass ht).symm

theorem twoA_QhatS_eq :
    {a : Shat | a ∈ QhatS ∧ IsConj (cV0 : Shat) a} = sEquiv '' jClass (qS 1) := by
  ext a
  constructor
  · rintro ⟨ha, hc⟩
    refine ⟨sEquiv.symm a, ?_, sEquiv.apply_symm_apply a⟩
    have ha' : sEquiv (sEquiv.symm a) ∈ QhatS := by rwa [MulEquiv.apply_symm_apply]
    have hc' : IsConj (sEquiv labelS) (sEquiv (sEquiv.symm a)) := by
      rwa [MulEquiv.apply_symm_apply, sEquiv_labelS_eq_cV0]
    exact mem_jClass_of_isConj_labelS (sEquiv_mem_QhatS.1 ha') (isConj_sEquiv_iff.1 hc')
  · rintro ⟨t, ht, rfl⟩
    refine ⟨sEquiv_mem_QhatS.2 (qS_mem_Qs_of_mem_jClass ht), ?_⟩
    rw [← sEquiv_labelS_eq_cV0]
    exact isConj_sEquiv_iff.2 (isConj_labelS_of_mem_jClass ht)

theorem ncard_twoA_QhatS :
    {a : Shat | a ∈ QhatS ∧ IsConj (cV0 : Shat) a}.ncard = 4600 := by
  rw [twoA_QhatS_eq, Set.ncard_image_of_injective _ sEquiv.injective, ← rs1_eq,
    ncard_jClass_rs1]

theorem mul_xs_mem_jClass
    {t : Sbp} (ht : t ∈ jClass (qS 1)) : t * xs ∈ jClass (qS 1) := by
  rw [jClass_eq_fiber (qS_mem 1) (psiS_qS_ne_zero (by decide))] at ht ⊢
  refine ⟨Qs.mul_mem ht.1 xs_mem, ?_⟩
  rw [psiS_mul ht.1 xs_mem, psiS_xs, add_zero]
  exact ht.2

theorem isConj_mul_xhatS_of_twoA
    {a : Shat} (ha : a ∈ QhatS) (hc : IsConj (cV0 : Shat) a) :
    IsConj (cV0 : Shat) (a * xhatS) := by
  have hmem : a ∈ sEquiv '' jClass (qS 1) := by
    rw [← twoA_QhatS_eq]
    exact ⟨ha, hc⟩
  obtain ⟨t, ht, rfl⟩ := hmem
  have h := (twoA_QhatS_eq.symm ▸ (⟨t * xs, mul_xs_mem_jClass ht, rfl⟩ :
    sEquiv (t * xs) ∈ sEquiv '' jClass (qS 1)) : sEquiv (t * xs) ∈
      {a : Shat | a ∈ QhatS ∧ IsConj (cV0 : Shat) a})
  rw [map_mul, sEquiv_xs] at h
  exact h.2

theorem cV0_mem_QhatS :
    (cV0 : Shat) ∈ QhatS := by
  rw [← sEquiv_labelS_eq_cV0, sEquiv_mem_QhatS]
  exact labelS_mem

@[expose] def FixesPt (s a : Shat) : Prop := s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * xhatS

theorem FixesPt.inv {s a : Shat} (hsC : s ∈ Subgroup.centralizer {xhatS}) (h : FixesPt s a) :
    FixesPt s⁻¹ a := by
  have hx := xhatS_comm hsC
  rcases h with h | h
  · left
    calc s⁻¹ * a * s⁻¹⁻¹ = s⁻¹ * (s * a * s⁻¹) * s := by rw [h, inv_inv]
      _ = a := by group
  · right
    calc s⁻¹ * a * s⁻¹⁻¹ = s⁻¹ * a * s * (xhatS * xhatS) := by
          rw [inv_inv, xhatS_mul_self, mul_one]
      _ = s⁻¹ * a * (s * xhatS) * xhatS := by group
      _ = s⁻¹ * a * (xhatS * s) * xhatS := by rw [hx]
      _ = s⁻¹ * (a * xhatS) * s * xhatS := by group
      _ = s⁻¹ * (s * a * s⁻¹) * s * xhatS := by rw [h]
      _ = a * xhatS := by group

theorem conj_mul_xhatS {g a : Shat} (hg : g ∈ Subgroup.centralizer {xhatS}) :
    g * (a * xhatS) * g⁻¹ = g * a * g⁻¹ * xhatS := by
  have hx' : xhatS * g⁻¹ = g⁻¹ * xhatS :=
    ((Commute.inv_left (show Commute g xhatS from xhatS_comm hg)).eq).symm
  calc g * (a * xhatS) * g⁻¹ = g * a * (xhatS * g⁻¹) := by group
    _ = g * a * (g⁻¹ * xhatS) := by rw [hx']
    _ = g * a * g⁻¹ * xhatS := by group

theorem FixesPt.mul {s t a : Shat} (hsC : s ∈ Subgroup.centralizer {xhatS})
    (h₁ : FixesPt s a) (h₂ : FixesPt t a) : FixesPt (s * t) a := by
  have e : s * t * a * (s * t)⁻¹ = s * (t * a * t⁻¹) * s⁻¹ := by group
  have hsx := conj_mul_xhatS (a := a) hsC
  rcases h₂ with h₂ | h₂ <;> rcases h₁ with h₁ | h₁
  · exact Or.inl (by rw [e, h₂, h₁])
  · exact Or.inr (by rw [e, h₂, h₁])
  · exact Or.inr (by rw [e, h₂, hsx, h₁])
  · exact Or.inl (by rw [e, h₂, hsx, h₁, mul_assoc, xhatS_mul_self, mul_one])

theorem FixesPt.conj {s a g : Shat} (hg : g ∈ Subgroup.centralizer {xhatS}) (h : FixesPt s a) :
    FixesPt (g * s * g⁻¹) (g * a * g⁻¹) := by
  have e : g * s * g⁻¹ * (g * a * g⁻¹) * (g * s * g⁻¹)⁻¹ = g * (s * a * s⁻¹) * g⁻¹ := by group
  rcases h with h | h
  · exact Or.inl (by rw [e, h])
  · exact Or.inr (by rw [e, h, conj_mul_xhatS hg])

theorem FixesPt.of_mem_QhatS
    {q a : Shat} (hq : q ∈ QhatS) (ha : a ∈ QhatS) : FixesPt q a := by
  have hx := xhatS_comm (QhatS_le_centralizer hq)
  rcases comm_of_mem_QhatS hq ha with h | h
  · exact Or.inl (by rw [h, mul_inv_cancel_right])
  · right
    rw [h]
    calc a * q * xhatS * q⁻¹ = a * (q * xhatS) * q⁻¹ := by group
      _ = a * (xhatS * q) * q⁻¹ := by rw [hx]
      _ = a * xhatS := by group

@[expose] def wordImg (w : List ℕ) (n : ℕ) : ℕ := w.foldl (fun m l => autApply gArr (genImgs l) m) n

theorem liftWordS_cons
    (l : ℕ) (w : List ℕ) : liftWordS (l :: w) = gs l * liftWordS w := by
  simp only [liftWordS, List.map_cons, List.prod_cons]

theorem liftWordS_unop_mem :
    ∀ w : List ℕ, (∀ l ∈ w, l < 2) → (liftWordS w).unop ∈ Jbar
  | [], _ => by simp only [liftWordS, List.map_nil, List.prod_nil, unop_one]; exact Jbar.one_mem
  | l :: w, hw => by
    rw [liftWordS_cons, unop_mul]
    exact Jbar.mul_mem (liftWordS_unop_mem w fun l' h => hw l' (List.mem_cons_of_mem _ h))
      (gs_mem_Jbar (hw l (List.mem_cons_self ..)))

theorem conj_liftWordS_qS :
    ∀ w : List ℕ, (∀ l ∈ w, l < 2) → ∀ n : ℕ,
    (liftWordS w)⁻¹ * qS n * liftWordS w = qS (wordImg w n)
  | [], _, n => by simp only [liftWordS, List.map_nil, List.prod_nil, inv_one, one_mul, mul_one,
      wordImg, List.foldl_nil]
  | l :: w, hw, n => by
    have hl := hw l (List.mem_cons_self ..)
    have ih := conj_liftWordS_qS w (fun l' h => hw l' (List.mem_cons_of_mem _ h))
      (autApply gArr (genImgs l) n)
    have e : wordImg (l :: w) n = wordImg w (autApply gArr (genImgs l) n) := rfl
    rw [liftWordS_cons, e, ← ih, ← conj_qS (gs_mem_Jbar hl) (fun i hi => conj_gs hl hi) n]
    group

@[expose] def fpCode (k : ℕ) : ℕ := if k = 6 then 7615769 else if k = 8 then 4146799 else 2345549

@[expose] def fpWord (k : ℕ) : List ℕ :=
  if k = 6 then [1, 0, 1, 1, 0] else if k = 8 then [1, 1, 0, 1] else [1, 1, 1, 1, 1, 1, 1, 1]

theorem fpWord_lt {k : ℕ} (hk : IsRank k) : ∀ l ∈ fpWord k, l < 2 := by
  rcases hk with rfl | rfl | rfl <;> decide

theorem wordImg_fpWord {k : ℕ} (hk : IsRank k) : wordImg (fpWord k) 1 = fpCode k := by
  rcases hk with rfl | rfl | rfl <;> decide +kernel

theorem fpCode_fixed {k : ℕ} (hk : IsRank k) :
    autApply gArr (liftImgsK k).toArray (fpCode k) = fpCode k ∨
      autApply gArr (liftImgsK k).toArray (fpCode k) = qmul gArr (fpCode k) (2 ^ 22) := by
  rcases hk with rfl | rfl | rfl
  · exact Or.inl (by decide +kernel)
  · exact Or.inl (by decide +kernel)
  · exact Or.inr (by decide +kernel)

theorem fpCode_mem_jClass
    {k : ℕ} (hk : IsRank k) : qS (fpCode k) ∈ jClass (qS 1) :=
  ⟨liftWordS (fpWord k), liftWordS_unop_mem _ (fpWord_lt hk),
    ((conj_liftWordS_qS _ (fpWord_lt hk) 1).trans (congrArg qS (wordImg_fpWord hk))).symm⟩

theorem conj_hs_qS
    {k : ℕ} (hk : IsRank k) (n : ℕ) :
    (hs k)⁻¹ * qS n * hs k = qS (autApply gArr (liftImgsK k).toArray n) :=
  conj_qS (hs_mem_Jbar hk) (fun i hi => by
    rw [conj_hs hk hi, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getD_eq_getElem?_getD]) n

theorem fpCode_hs
    {k : ℕ} (hk : IsRank k) :
    (hs k)⁻¹ * qS (fpCode k) * hs k = qS (fpCode k) ∨
      (hs k)⁻¹ * qS (fpCode k) * hs k = qS (fpCode k) * xs := by
  rw [conj_hs_qS hk]
  rcases fpCode_fixed hk with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr (by rw [h, ← qS_mul, qS_two_pow_22])

theorem exists_twoA_fixed_QhatS
    {s : Shat} (hsC : s ∈ Subgroup.centralizer {xhatS})
    (hsQ : s ∉ QhatS) (hs2 : s * s = 1 ∨ s * s = xhatS) :
    ∃ a ∈ QhatS, IsConj (cV0 : Shat) a ∧ (s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * xhatS) := by
  have hsu : sEquiv (sEquiv.symm s) = s := sEquiv.apply_symm_apply s
  have huJ : (sEquiv.symm s).unop ∈ Jbar := sEquiv_mem_centralizer.1 (by rwa [hsu])
  have huQ : sEquiv.symm s ∉ Qs := fun h => hsQ (by rw [← hsu]; exact sEquiv_mem_QhatS.2 h)
  have huu : sEquiv.symm s * sEquiv.symm s ∈ Qs := by
    rw [← sEquiv_mem_QhatS, map_mul, hsu]
    rcases hs2 with h | h <;> rw [h]
    · exact QhatS.one_mem
    · exact xhatS_mem_QhatS
  have hc := exists_conj_cosetElt huJ huQ huu
  obtain ⟨k, hk, g, hg, n, -, hgu⟩ := hc
  have hG : sEquiv g ∈ Subgroup.centralizer {xhatS} := sEquiv_mem_centralizer.2 hg
  have hH : sEquiv (hs k) ∈ Subgroup.centralizer {xhatS} :=
    sEquiv_mem_centralizer.2 (hs_mem_Jbar hk)
  have hq : sEquiv (qS n) ∈ QhatS := sEquiv_mem_QhatS.2 (qS_mem n)
  have hA : sEquiv (qS (fpCode k)) ∈ QhatS := sEquiv_mem_QhatS.2 (qS_mem _)
  have hGs : sEquiv g * s * (sEquiv g)⁻¹ = sEquiv (hs k) * sEquiv (qS n) := by
    have h := congrArg sEquiv hgu
    rwa [cosetElt, map_mul, map_mul, map_mul, map_inv, hsu] at h
  have hHA : FixesPt (sEquiv (hs k))⁻¹ (sEquiv (qS (fpCode k))) := by
    unfold FixesPt
    rw [inv_inv]
    rcases fpCode_hs hk with h | h
    · left
      have h' := congrArg sEquiv h
      rwa [map_mul, map_mul, map_inv] at h'
    · right
      have h' := congrArg sEquiv h
      rwa [map_mul, map_mul, map_mul, map_inv, sEquiv_xs] at h'
  have hHA' : FixesPt (sEquiv (hs k)) (sEquiv (qS (fpCode k))) := by
    have h := hHA.inv (Subgroup.inv_mem _ hH)
    rwa [inv_inv] at h
  have hfix : FixesPt (sEquiv g * s * (sEquiv g)⁻¹) (sEquiv (qS (fpCode k))) := by
    rw [hGs]
    exact hHA'.mul hH (FixesPt.of_mem_QhatS hq hA)
  have hfix' := hfix.conj (Subgroup.inv_mem _ hG)
  have e : (sEquiv g)⁻¹ * (sEquiv g * s * (sEquiv g)⁻¹) * (sEquiv g)⁻¹⁻¹ = s := by group
  rw [e] at hfix'
  refine ⟨_, ?_, ?_, hfix'⟩
  · exact conj_mem_QhatS (Subgroup.inv_mem _ hG) hA
  · refine IsConj.trans ?_ (isConj_iff.2 ⟨(sEquiv g)⁻¹, rfl⟩)
    rw [← sEquiv_labelS_eq_cV0]
    exact isConj_sEquiv_iff.2 (isConj_labelS_of_mem_jClass (fpCode_mem_jClass hk))

theorem oddCore_P1 :
    CFSG.oddCore P1 = ⊥ := by
  refine oddCore_eq_bot_iff.2 fun N hNn hN =>
    eq_bot_of_selfCent N1_subgroupOf_normal ?_ ?_ hNn hN
  · exact IsPGroup.of_card (n := 22)
      (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe N1_le_P1).toEquiv, natCard_N1])
  · intro y hy
    rw [Subgroup.mem_subgroupOf]
    refine centralizer_N1_le y.2 fun n hn => ?_
    have h := (Subgroup.mem_centralizer_iff.1 hy) ⟨n, N1_le_P1 hn⟩ (Subgroup.mem_subgroupOf.2 hn)
    exact (congrArg Subtype.val h).symm

theorem map_centralizer_cV0_inf :
    (Subgroup.centralizer {(cV0 : Shat)} ⊓ Subgroup.centralizer {xhatS}).map Shat.subtype =
      P1 := by
  ext d
  constructor
  · rintro ⟨s, ⟨hc, hx⟩, rfl⟩
    refine ⟨mem_centralizer_xhatS.1 hx, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hc)
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, coe_cV0_dfull] at h
  · intro hd
    refine ⟨⟨d, Jhat_le_Shat hd.1⟩, ⟨Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_),
      mem_centralizer_xhatS.2 hd.1⟩, rfl⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_cV0_dfull]
    exact Subgroup.mem_centralizer_singleton_iff.1 hd.2

theorem oddCore_centralizer_cV0_xhatS :
    CFSG.oddCore ↥(Subgroup.centralizer {(cV0 : Shat)} ⊓ Subgroup.centralizer {xhatS}) = ⊥ :=
  oddCore_eq_bot_of_equiv ((Subgroup.equivMapOfInjective _ Shat.subtype
    Shat.subtype_injective).trans (MulEquiv.subgroupCongr map_centralizer_cV0_inf)).symm oddCore_P1

theorem conj_mem_centralizer_singleton {X : Type*} [Group X] {g x y : X}
    (h : x ∈ Subgroup.centralizer {y}) : g * x * g⁻¹ ∈ Subgroup.centralizer {g * y * g⁻¹} := by
  rw [Subgroup.mem_centralizer_singleton_iff] at h ⊢
  calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
    _ = g * (y * x) * g⁻¹ := by rw [h]
    _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group

theorem map_conj_centralizer_inf {X : Type*} [Group X] (g y z : X) :
    (Subgroup.centralizer {y} ⊓ Subgroup.centralizer {z}).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer {g * y * g⁻¹} ⊓ Subgroup.centralizer {g * z * g⁻¹} := by
  ext x
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  constructor
  · rintro ⟨h1, h2⟩
    have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [e]
    exact ⟨conj_mem_centralizer_singleton h1, conj_mem_centralizer_singleton h2⟩
  · rintro ⟨h1, h2⟩
    have h1' := conj_mem_centralizer_singleton (g := g⁻¹) h1
    have h2' := conj_mem_centralizer_singleton (g := g⁻¹) h2
    rw [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group, inv_inv] at h1'
    rw [show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group, inv_inv] at h2'
    exact ⟨h1', h2'⟩

theorem oddCore_centralizer_twoA_QhatS
    {a : Shat} (ha : a ∈ QhatS)
    (hc : IsConj (cV0 : Shat) a) :
    CFSG.oddCore ↥(Subgroup.centralizer {a} ⊓ Subgroup.centralizer {xhatS}) = ⊥ := by
  have hmem : sEquiv.symm a ∈ jClass labelS := by
    rw [jClass_eq_of_mem labelS_mem_jClass]
    have hmem' : a ∈ sEquiv '' jClass (qS 1) := by
      rw [← twoA_QhatS_eq]
      exact ⟨ha, hc⟩
    obtain ⟨t, ht, rfl⟩ := hmem'
    rwa [MulEquiv.symm_apply_apply]
  obtain ⟨g, hg, hga⟩ := hmem
  have hG : (sEquiv g)⁻¹ ∈ Subgroup.centralizer {xhatS} :=
    Subgroup.inv_mem _ (sEquiv_mem_centralizer.2 hg)
  have haG : (sEquiv g)⁻¹ * (cV0 : Shat) * (sEquiv g)⁻¹⁻¹ = a := by
    have h := congrArg sEquiv hga
    rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, sEquiv_labelS_eq_cV0] at h
    rw [inv_inv, h]
  have hxG : (sEquiv g)⁻¹ * xhatS * (sEquiv g)⁻¹⁻¹ = xhatS := by
    rw [xhatS_comm hG, mul_inv_cancel_right]
  have hmap := map_conj_centralizer_inf ((sEquiv g)⁻¹) (cV0 : Shat) xhatS
  rw [haG, hxG] at hmap
  exact oddCore_eq_bot_of_equiv (((MulAut.conj (sEquiv g)⁻¹).subgroupMap _).trans
    (MulEquiv.subgroupCongr hmap)) oddCore_centralizer_cV0_xhatS

theorem exists_twoA_pair_QhatS :
    ∃ a ∈ QhatS, ∃ b ∈ QhatS, IsConj (cV0 : Shat) a ∧
    IsConj (cV0 : Shat) b ∧ a * b = b * a ∧ a * b ≠ 1 ∧ a * b ≠ xhatS ∧
    CFSG.oddCore ↥(Subgroup.centralizer {a} ⊓ Subgroup.centralizer {xhatS}) = ⊥ ∧
    CFSG.oddCore ↥(Subgroup.centralizer {b} ⊓ Subgroup.centralizer {xhatS}) = ⊥ := by
  have c1 : autApply gArr (genImgs 1) 1 = 1190513 := by decide +kernel
  have c2 : qmul gArr 1 1190513 = 1190512 := by decide +kernel
  have c3 : qmul gArr 1190513 1 = 1190512 := by decide +kernel
  have hb : (gs 1)⁻¹ * qS 1 * gs 1 = qS 1190513 := by
    rw [conj_qS (gs_mem_Jbar (by norm_num)) (fun i hi => conj_gs (by norm_num) hi) 1, c1]
  have hab : qS 1 * qS 1190513 = qS 1190512 := by rw [qS_mul, c2]
  have hba : qS 1190513 * qS 1 = qS 1190512 := by rw [qS_mul, c3]
  have hmemB : qS 1190513 ∈ jClass (qS 1) := ⟨gs 1, gs_mem_Jbar (by norm_num), hb.symm⟩
  have hA : sEquiv (qS 1) ∈ QhatS := sEquiv_mem_QhatS.2 (qS_mem 1)
  have hB : sEquiv (qS 1190513) ∈ QhatS := sEquiv_mem_QhatS.2 (qS_mem _)
  have hcA : IsConj (cV0 : Shat) (sEquiv (qS 1)) := by
    rw [← sEquiv_labelS_eq_cV0]
    exact isConj_sEquiv_iff.2 (isConj_labelS_of_mem_jClass (mem_jClass_self _))
  have hcB : IsConj (cV0 : Shat) (sEquiv (qS 1190513)) := by
    rw [← sEquiv_labelS_eq_cV0]
    exact isConj_sEquiv_iff.2 (isConj_labelS_of_mem_jClass hmemB)
  refine ⟨_, hA, _, hB, hcA, hcB, ?_, ?_, ?_, oddCore_centralizer_twoA_QhatS hA hcA,
    oddCore_centralizer_twoA_QhatS hB hcB⟩
  · rw [← map_mul, ← map_mul, hab, hba]
  · rw [← map_mul, hab]
    intro h
    have h1 := sEquiv.injective (h.trans (map_one sEquiv).symm)
    rw [← qS_zero] at h1
    exact absurd (qS_injOn (Set.mem_Iio.2 (by norm_num)) (Set.mem_Iio.2 (by norm_num)) h1)
      (by norm_num)
  · rw [← map_mul, hab, ← sEquiv_xs]
    intro h
    have h1 := sEquiv.injective h
    rw [← qS_two_pow_22] at h1
    exact absurd (qS_injOn (Set.mem_Iio.2 (by norm_num)) (Set.mem_Iio.2 (by norm_num)) h1)
      (by norm_num)

end CFSG.Monster.B.GSide

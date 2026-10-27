module

public import CFSG.RankThree.GF2n.Stroth80.Sec7EndMain
public import CFSG.RankThree.GF2n.Stroth80.Sec78Z1
public import CFSG.RankThree.GF2n.Stroth80.Sec78Z0Data
public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerDefs

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GF2n.Stroth80.S714
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

variable (hc) in
@[expose] def tbar {t : G} (ht : t ∈ LB M Q B) : Mbar M Q :=
  QuotientGroup.mk (⟨t, hc.LB_le_M ht⟩ : ↥M)

omit [Finite G] [Finite K] in
theorem dmap_act_comm {g h : Mbar M Q} (hgh : g * h = h * g) (e : M₀.E) :
    dmap ρ g ((ρ h).toAdd e) = (ρ h).toAdd (dmap ρ g e) := by
  have e1 : ∀ (a c : Mbar M Q) (v : M₀.E), (ρ a).toAdd ((ρ c).toAdd v) = (ρ (a * c)).toAdd v :=
    fun a c v => by rw [map_mul]; rfl
  simp only [dmap, map_sub]
  rw [e1 g h, e1 h g, hgh]

theorem tbar_mem (hc : Ctx M Q Z B) {n' : ℕ} {t : G} (hs : Sec7Hyp hc n' t) :
    tbar hc hs.toSec5.mem ∈ bar M Q (Rt M (LB M Q B) t) ∧
      tbar hc hs.toSec5.mem ∈ bar M Q (hc.CN t) ∧ tbar hc hs.toSec5.mem ∈ bar M Q (H0 M Z) := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htR : t ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht ht
  have htN : t ∈ hc.CN t := Ctx.mem_CN.mpr ⟨htR, fun v hv =>
    ((hc.mem_Q1_iff (hc.LB_le_M ht)).mp (hc.Vt_le_Q1 ht hv)).2⟩
  exact ⟨mk_mem_bar _ htR, mk_mem_bar _ htN, mk_mem_bar _ (hc.Rt_le_H0 t htR)⟩

theorem wsub_eq_orthogonal (hS : IsTensorSetup hc n M₀ ρ b) (t : G) :
    wsub hS t = M₀.B.orthogonal (hc.VtSub hS.model t) := by
  ext e
  rw [LinearMap.BilinForm.mem_orthogonal_iff, mem_wsub,
    mem_img_Wt_iff M₀ hS.model.reg (hc.Vt_le_Q t)]
  constructor
  · intro h v hv
    show M₀.B v e = 0
    rw [Tim79.QuadModel.B_comm, h v ((hc.mem_VtSub hS.model t).mp hv), neg_zero]
  · intro h v hv
    have h1 : M₀.B v e = 0 := h v ((hc.mem_VtSub hS.model t).mpr hv)
    rw [Tim79.QuadModel.B_comm, h1, neg_zero]

theorem bilin_nondegenerate_isRefl : M₀.B.Nondegenerate ∧ M₀.B.IsRefl :=
  ⟨⟨fun x hx => M₀.nondeg x hx, fun y hy => M₀.nondeg y fun f => by
      rw [Tim79.QuadModel.B_comm, hy f, neg_zero]⟩,
    fun x y h => by rw [Tim79.QuadModel.B_comm, h, neg_zero]⟩

theorem psi_facts_tbar (h310chi : Stroth310ChiStatement) (hS : IsTensorSetup hc n M₀ ρ b)
    {n' : ℕ} {t : G} (hs : Sec7Hyp hc n' t) :
    (∀ e, dmap ρ (tbar hc hs.toSec5.mem) e ∈ hc.VtSub hS.model t) ∧
      (∀ v ∈ hc.VtSub hS.model t, ∃ e, dmap ρ (tbar hc hs.toSec5.mem) e = v) ∧
      ∀ e, dmap ρ (tbar hc hs.toSec5.mem) e = 0 ↔ e ∈ wsub hS t :=
  psi_facts h310chi hS hs.toSec5 (Or.inr hs.omegaNat) ⟨t, hc.LB_le_M hs.toSec5.mem⟩ rfl

theorem exists_dmap_tbar_ne_zero (h310chi : Stroth310ChiStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t : G} (hs : Sec7Hyp hc n' t) :
    ∃ e, dmap ρ (tbar hc hs.toSec5.mem) e ≠ 0 := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨-, hψsurj, -⟩ := psi_facts h310chi hS hs.toSec5 (Or.inr hs.omegaNat)
    ⟨t, hc.LB_le_M ht⟩ rfl
  obtain ⟨x, hxB, hxQ, hx⟩ := M₀.mem_img.mp hS.b_img
  have hbV : b ∈ hc.VtSub hS.model t := by
    have h := (hc.mem_VtSub hS.model t).mpr (M₀.pi_mem_img (hc.B_le_Vt ht hxB) hxQ)
    rwa [hx] at h
  obtain ⟨e, he⟩ := hψsurj b hbV
  exact ⟨e, fun h0 => hS.b_ne (he.symm.trans h0)⟩

theorem exists_act_eq_add_smul (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hMp : Sec7CentreMpStatement) (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G}
    (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {a : Mbar M Q} (ha : a ∈ bar M Q Z0) :
    ∃ c : K, ∀ e, (ρ a).toAdd e = e + c • dmap ρ (tbar hc hs.toSec5.mem) e := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  obtain ⟨-, -, htH⟩ := tbar_mem hc hs
  obtain ⟨a', ha', rfl⟩ := exists_of_mem_bar ha
  have haN : (QuotientGroup.mk a' : Mbar M Q) ∈ bar M Q (hc.CN t) :=
    mk_mem_bar a' (sec7ctr_Z0_le_CN hc hs hZ0 ha')
  have haH : (QuotientGroup.mk a' : Mbar M Q) ∈ bar M Q (H0 M Z) := mem_bar_H0_of_CN haN
  obtain ⟨hψV, hψsurj, hψW⟩ := psi_facts h310chi hS hs.toSec5 (Or.inr hs.omegaNat) ⟨t, htM⟩ rfl
  obtain ⟨-, -, haE⟩ := dmap_CN_facts h310chi h52a hS hs hr haN
  have haW : ∀ w ∈ wsub hS t, dmap ρ (QuotientGroup.mk a') w = 0 := by
    intro w hw
    obtain ⟨x, hxW, hxQ, rfl⟩ := M₀.mem_img.mp ((mem_wsub hS t).mp hw)
    rw [dmap_pi hS a' hxQ]
    have hcQ : ⁅(a' : G), x⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 a'.2) x).mp hxQ)
        (Q.inv_mem hxQ)
    exact (M₀.π_ker _ hcQ).mpr ((hMp G M Q Z B hc n' t hs Z0 hZ0 a' ha').2 x hxW)
  have hrefl : M₀.B.IsRefl := fun x y h => by rw [Tim79.QuadModel.B_comm, h, neg_zero]
  have hnd : M₀.B.Nondegenerate :=
    ⟨fun x hx => M₀.nondeg x hx, fun y hy => M₀.nondeg y fun f => by
      rw [Tim79.QuadModel.B_comm, hy f, neg_zero]⟩
  have hWorth : ∀ e, e ∈ wsub hS t → e ∈ M₀.B.orthogonal (hc.VtSub hS.model t) := by
    intro e he
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro v hv
    show M₀.B v e = 0
    exact bilin_vsub_wsub hS t hv he
  have hWorth' : ∀ e, e ∈ M₀.B.orthogonal (hc.VtSub hS.model t) → e ∈ wsub hS t := by
    intro e he
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at he
    refine (mem_wsub hS t).mpr ((mem_img_Wt_iff M₀ hS.model.reg (hc.Vt_le_Q t)).mpr ?_)
    intro v hv
    have h1 : M₀.B v e = 0 := he v ((hc.mem_VtSub hS.model t).mpr hv)
    rw [Tim79.QuadModel.B_comm, h1, neg_zero]
  have hφV : ∀ e, dmap ρ (QuotientGroup.mk a') e ∈ hc.VtSub hS.model t := by
    intro e
    rw [← LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl (hc.VtSub hS.model t),
      LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    have huW : u ∈ wsub hS t := hWorth' u hu
    show M₀.B u (dmap ρ (QuotientGroup.mk a') e) = 0
    have h1 := bilin_D_right (B := M₀.B) (V := hc.VtSub hS.model t) (W := wsub hS t)
      (D := dlin hS _ haH) (dmap_iso hS haH) (fun x => haE x)
      (fun w hw => by rw [dlin_apply, haW w hw]; exact Submodule.zero_mem _)
      (fun w hw v hv => bilin_wsub_vsub hS t hw hv) e huW
    rw [dlin_apply, dlin_apply, haW u huW, map_zero, neg_zero] at h1
    rw [Tim79.QuadModel.B_comm, h1, neg_zero]
  have hrange : LinearMap.range (dlin hS (tbar hc ht) htH) = hc.VtSub hS.model t := by
    ext v
    constructor
    · rintro ⟨e, rfl⟩
      exact hψV e
    · intro hv
      obtain ⟨e, he⟩ := hψsurj v hv
      exact ⟨e, he⟩
  have hker : LinearMap.ker (dlin hS (tbar hc ht) htH) ≤ LinearMap.ker (dlin hS _ haH) := by
    intro e he
    rw [LinearMap.mem_ker] at he ⊢
    exact haW e ((hψW e).mp he)
  have hφP : LinearMap.range (dlin hS _ haH) ≤ hc.VtSub hS.model t := by
    rintro _ ⟨e, rfl⟩
    exact hφV e
  have hψS : ∀ (x : ↥(bar M Q (Rt M (LB M Q B) t))) (e : M₀.E),
      dlin hS (tbar hc ht) htH ((ρ (x : Mbar M Q)).toAdd e) =
        (ρ (x : Mbar M Q)).toAdd (dlin hS (tbar hc ht) htH e) := fun x e =>
    dmap_act_comm (endg_comm_centre hZ0 hRM (z := ⟨t, htM⟩) htZ0 x.2) e
  have hφS : ∀ (x : ↥(bar M Q (Rt M (LB M Q B) t))) (e : M₀.E),
      dlin hS _ haH ((ρ (x : Mbar M Q)).toAdd e) = (ρ (x : Mbar M Q)).toAdd (dlin hS _ haH e) :=
    fun x e => dmap_act_comm (endg_comm_centre hZ0 hRM ha' x.2) e
  obtain ⟨K', hF', hFin', ι, hFι, hDι, hNι, Xcl, hK', hcomm, hnat⟩ := sec7_natural_data hc hs
  obtain ⟨θ, Ψ, π, hπr, -, hΨc, hΨx⟩ := hc.natural_transport hS ht hK' hcomm hnat
  obtain ⟨c, hcφ⟩ := endg_schur hcomm (hc.VtSub hS.model t) θ Ψ hΨc π hπr
    (fun (x : ↥(bar M Q (Rt M (LB M Q B) t))) (w : M₀.E) => (ρ (x : Mbar M Q)).toAdd w)
    (fun x w hw => hc.act_mem_VtSub hS ht x x.2 w hw) hΨx _ _ hrange hker hφP hψS hφS
  refine ⟨c, fun e => ?_⟩
  rw [act_eq_add_dmap]
  have h1 := hcφ e
  rw [dlin_apply, dlin_apply] at h1
  rw [h1]

variable (ρ hc) in
noncomputable def cscal {t : G} (ht : t ∈ LB M Q B) (a : Mbar M Q) : K := by
  classical
  exact if h : ∃ c : K, ∀ e, (ρ a).toAdd e = e + c • dmap ρ (tbar hc ht) e then
    Classical.choose h else 0

theorem act_eq_cscal (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hMp : Sec7CentreMpStatement) (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G}
    (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {a : Mbar M Q} (ha : a ∈ bar M Q Z0)
    (e : M₀.E) :
    (ρ a).toAdd e = e + cscal hc ρ hs.toSec5.mem a • dmap ρ (tbar hc hs.toSec5.mem) e := by
  have h := exists_act_eq_add_smul h310chi h52a hMp hS hs hr hZ0 ha
  rw [cscal, dif_pos h]
  exact Classical.choose_spec h e

theorem cscal_eq (h310chi : Stroth310ChiStatement) (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ}
    {t : G} (hs : Sec7Hyp hc n' t) {a : Mbar M Q} {c : K}
    (h : ∀ e, (ρ a).toAdd e = e + c • dmap ρ (tbar hc hs.toSec5.mem) e) :
    cscal hc ρ hs.toSec5.mem a = c := by
  obtain ⟨e₀, he₀⟩ := exists_dmap_tbar_ne_zero h310chi hS hs
  have hex : ∃ c : K, ∀ e, (ρ a).toAdd e = e + c • dmap ρ (tbar hc hs.toSec5.mem) e := ⟨c, h⟩
  have h1 := Classical.choose_spec hex e₀
  rw [h e₀] at h1
  have h2 : (c - Classical.choose hex) • dmap ρ (tbar hc hs.toSec5.mem) e₀ = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr (add_left_cancel h1)
  rw [cscal, dif_pos hex]
  exact (sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right he₀)).symm

theorem dmap_tbar_dmap_tbar (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t)
    (hr : Sec7A hc t r) (e : M₀.E) :
    dmap ρ (tbar hc hs.toSec5.mem) (dmap ρ (tbar hc hs.toSec5.mem) e) = 0 := by
  obtain ⟨-, htN, -⟩ := tbar_mem hc hs
  obtain ⟨hψV, -, -⟩ := psi_facts h310chi hS hs.toSec5 (Or.inr hs.omegaNat)
    ⟨t, hc.LB_le_M hs.toSec5.mem⟩ rfl
  exact (dmap_CN_facts h310chi h52a hS hs hr htN).1 _ (hψV e)

theorem cscal_mul (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hMp : Sec7CentreMpStatement) (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G}
    (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {a a' : Mbar M Q} (ha : a ∈ bar M Q Z0)
    (ha' : a' ∈ bar M Q Z0) :
    cscal hc ρ hs.toSec5.mem (a * a') =
      cscal hc ρ hs.toSec5.mem a + cscal hc ρ hs.toSec5.mem a' := by
  obtain ⟨-, -, htH⟩ := tbar_mem hc hs
  refine cscal_eq h310chi hS hs fun e => ?_
  have e1 : (ρ (a * a')).toAdd e = (ρ a).toAdd ((ρ a').toAdd e) := by rw [map_mul]; rfl
  rw [e1, act_eq_cscal h310chi h52a hMp hS hs hr hZ0 ha' e,
    act_eq_cscal h310chi h52a hMp hS hs hr hZ0 ha, dmap_add, dmap_smul hS htH,
    dmap_tbar_dmap_tbar h310chi h52a hS hs hr, smul_zero, add_zero, add_smul]
  abel

theorem cscal_one (h310chi : Stroth310ChiStatement) (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ}
    {t : G} (hs : Sec7Hyp hc n' t) : cscal hc ρ hs.toSec5.mem 1 = 0 :=
  cscal_eq h310chi hS hs fun e => by
    rw [zero_smul, add_zero, map_one]
    rfl

theorem cscal_eq_zero_iff (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hMp : Sec7CentreMpStatement) (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G}
    (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {a : Mbar M Q} (ha : a ∈ bar M Q Z0) :
    cscal hc ρ hs.toSec5.mem a = 0 ↔ a = 1 := by
  constructor
  · intro h0
    obtain ⟨act, hactρ, hinj, -⟩ := endg_act_data hc hS.model ρ hS.conj
    refine hinj (Equiv.ext fun e => ?_)
    rw [hactρ, hactρ, act_eq_cscal h310chi h52a hMp hS hs hr hZ0 ha e, h0, zero_smul, add_zero,
      map_one]
    rfl
  · rintro rfl
    exact cscal_one h310chi hS hs

theorem cscal_inv (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hMp : Sec7CentreMpStatement) (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G}
    (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {a : Mbar M Q} (ha : a ∈ bar M Q Z0) :
    cscal hc ρ hs.toSec5.mem a⁻¹ = -cscal hc ρ hs.toSec5.mem a := by
  have h := cscal_mul h310chi h52a hMp hS hs hr hZ0 ha (Subgroup.inv_mem _ ha)
  rw [mul_inv_cancel, cscal_one h310chi hS hs] at h
  linear_combination -h

theorem cscal_surj (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hMp : Sec7CentreMpStatement) (hZcard : Sec7ZCardStatement) (hS : IsTensorSetup hc n M₀ ρ b)
    {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (k : K) :
    ∃ a ∈ bar M Q Z0, cscal hc ρ hs.toSec5.mem a = k := by
  have hinj : Function.Injective fun a : ↥(bar M Q Z0) => cscal hc ρ hs.toSec5.mem a := by
    intro a a' h
    have h1 := cscal_mul h310chi h52a hMp hS hs hr hZ0 a.2 (Subgroup.inv_mem _ a'.2)
    rw [cscal_inv h310chi h52a hMp hS hs hr hZ0 a'.2] at h1
    have h2 := (cscal_eq_zero_iff h310chi h52a hMp hS hs hr hZ0
      (Subgroup.mul_mem _ a.2 (Subgroup.inv_mem _ a'.2))).mp (by
        rw [h1]
        exact add_neg_eq_zero.mpr h)
    exact Subtype.ext (mul_inv_eq_one.mp h2)
  have hcard := bar_card_mul_card_of_le (hc.Q_le_centre hs.toSec5.mem hZ0)
    (hZ0.le.trans (hc.Rt_le_M t))
  rw [hZcard G M Q Z B hc n' t hs Z0 hZ0, mul_comm (Nat.card Q)] at hcard
  have hbar : Nat.card ↥(bar M Q Z0) = Nat.card Z := Nat.eq_of_mul_eq_mul_right Nat.card_pos hcard
  obtain ⟨a, ha⟩ := (hinj.bijective_of_nat_card_le (hS.card.trans hbar.symm).le).2 k
  exact ⟨a, a.2, ha⟩

theorem conj_eq_of_mem_bar_centre (hc : Ctx M Q Z B) {t : G} {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {a x : Mbar M Q} (ha : a ∈ bar M Q Z0)
    (hx : x ∈ bar M Q (Rt M (LB M Q B) t)) : x * a * x⁻¹ = a := by
  obtain ⟨a', ha', rfl⟩ := exists_of_mem_bar ha
  rw [← endg_comm_centre hZ0 (hc.Rt_le_M t) ha' hx, mul_inv_cancel_right]

theorem comm_mem_bar_Z0 (hCommN : Sec7CommNStatement) {n' : ℕ} {t : G} (hs : Sec7Hyp hc n' t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {g h : Mbar M Q}
    (hg : g ∈ bar M Q (hc.CN t)) (hh : h ∈ bar M Q (hc.CN t)) : ⁅g, h⁆ ∈ bar M Q Z0 := by
  obtain ⟨x, hx, rfl⟩ := exists_of_mem_bar hg
  obtain ⟨y, hy, rfl⟩ := exists_of_mem_bar hh
  rw [show ⁅(QuotientGroup.mk x : Mbar M Q), QuotientGroup.mk y⁆ = QuotientGroup.mk ⁅x, y⁆ from
    (map_commutatorElement (QuotientGroup.mk' (Q.subgroupOf M)) x y).symm]
  exact mk_mem_bar ⁅x, y⁆
    (hCommN G M Q Z B hc n' t hs Z0 hZ0 (Subgroup.commutator_mem_commutator hx hy))

theorem sq_mem_bar_Z0 (h51 : Stroth51Statement) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t)
    (hr : Sec7A hc t r) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {g : Mbar M Q} (hg : g ∈ bar M Q (hc.CN t)) : g ^ 2 ∈ bar M Q Z0 := by
  obtain ⟨x, hx, rfl⟩ := exists_of_mem_bar hg
  obtain ⟨-, hopp, -⟩ := sec7ctr_Z0_data h51 hc hs.toSec5 (Or.inr hs.omegaNat) hr hZ0
    (sec7ctr_Z0_le_CN hc hs hZ0)
  rw [show (QuotientGroup.mk x : Mbar M Q) ^ 2 = QuotientGroup.mk (x ^ 2) from
    (map_pow (QuotientGroup.mk' (Q.subgroupOf M)) x 2).symm]
  exact mk_mem_bar (x ^ 2) (by simpa using hopp.2.2.2.2.2.2.2.1 (x : G) hx)

theorem cscal_comm_mul_bilin (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hMp : Sec7CentreMpStatement) (hCommN : Sec7CommNStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t)
    (hr : Sec7A hc t r) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {g h : Mbar M Q} (hg : g ∈ bar M Q (hc.CN t)) (hh : h ∈ bar M Q (hc.CN t)) (e e' : M₀.E) :
    cscal hc ρ hs.toSec5.mem ⁅g, h⁆ * M₀.B (dmap ρ (tbar hc hs.toSec5.mem) e) e' =
      M₀.B (dmap ρ g e) (dmap ρ h e') - M₀.B (dmap ρ h e) (dmap ρ g e') := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hgH := mem_bar_H0_of_CN hg
  have hhH := mem_bar_H0_of_CN hh
  have hcZ := comm_mem_bar_Z0 hCommN hs hZ0 hg hh
  have hcH : ⁅g, h⁆ ∈ bar M Q (H0 M Z) := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hgH hhH)
      (Subgroup.inv_mem _ hgH)) (Subgroup.inv_mem _ hhH)
  obtain ⟨-, -, hψW⟩ := psi_facts_tbar h310chi hS hs
  obtain ⟨-, hgW, hgE⟩ := dmap_CN_facts h310chi h52a hS hs hr hg
  obtain ⟨-, hhW, hhE⟩ := dmap_CN_facts h310chi h52a hS hs hr hh
  have hP : ∀ x, dmap ρ ⁅g, h⁆ x = cscal hc ρ ht ⁅g, h⁆ • dmap ρ (tbar hc ht) x := by
    intro x
    have h1 := act_eq_cscal h310chi h52a hMp hS hs hr hZ0 hcZ x
    rw [act_eq_add_dmap] at h1
    exact add_left_cancel h1
  have hrel : ∀ x, (x + dlin hS g hgH x + dlin hS h hhH (x + dlin hS g hgH x)) +
      dlin hS ⁅g, h⁆ hcH (x + dlin hS g hgH x + dlin hS h hhH (x + dlin hS g hgH x)) =
      (x + dlin hS h hhH x) + dlin hS g hgH (x + dlin hS h hhH x) := by
    intro x
    have e3 : ∀ (a c : Mbar M Q) (v : M₀.E), (ρ (a * c)).toAdd v = (ρ a).toAdd ((ρ c).toAdd v) :=
      fun a c v => by rw [map_mul]; rfl
    have key : (ρ ⁅g, h⁆).toAdd ((ρ h).toAdd ((ρ g).toAdd x)) = (ρ g).toAdd ((ρ h).toAdd x) := by
      rw [← e3, ← e3, ← e3, show ⁅g, h⁆ * h * g = g * h by rw [commutatorElement_def]; group]
    simp only [dlin_apply]
    simpa only [act_eq_add_dmap] using key
  have hcf := comm_formula (fun x => by
      simp only [dlin_apply]
      rw [hP, (hψW _).mpr (hgE x), smul_zero])
    (fun x => by
      simp only [dlin_apply]
      rw [hP, (hψW _).mpr (hhE x), smul_zero]) hrel
  have hpc := pair_comm (B := M₀.B) (V := hc.VtSub hS.model t) (W := wsub hS t) hcf
    (dmap_iso hS hgH) (dmap_iso hS hhH) (fun x => hgE x) (fun x => hhE x)
    (fun w hw => hgW w hw) (fun w hw => hhW w hw) (fun v hv w hw => bilin_vsub_wsub hS t hv hw)
    e e'
  rw [dlin_apply, hP, map_smul, LinearMap.smul_apply, smul_eq_mul] at hpc
  rw [hpc]
  rfl

theorem cscal_sq_mul_bilin (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement)
    (h52a : Stroth52aStatement) (hMp : Sec7CentreMpStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t)
    (hr : Sec7A hc t r) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {g : Mbar M Q} (hg : g ∈ bar M Q (hc.CN t)) (e e' : M₀.E) :
    cscal hc ρ hs.toSec5.mem (g ^ 2) * M₀.B (dmap ρ (tbar hc hs.toSec5.mem) e) e' =
      -M₀.B (dmap ρ g e) (dmap ρ g e') := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hS.card.trans hZ2)
  have hgH := mem_bar_H0_of_CN hg
  have hsqZ := sq_mem_bar_Z0 h51 hs hr hZ0 hg
  have hsqH : g ^ 2 ∈ bar M Q (H0 M Z) := Subgroup.pow_mem _ hgH 2
  obtain ⟨-, hgW, hgE⟩ := dmap_CN_facts h310chi h52a hS hs hr hg
  have hP : ∀ x, dmap ρ (g ^ 2) x = cscal hc ρ ht (g ^ 2) • dmap ρ (tbar hc ht) x := by
    intro x
    have h1 := act_eq_cscal h310chi h52a hMp hS hs hr hZ0 hsqZ x
    rw [act_eq_add_dmap] at h1
    exact add_left_cancel h1
  have hrel : ∀ x, (x + dlin hS g hgH x) + dlin hS g hgH (x + dlin hS g hgH x) =
      x + dlin hS (g ^ 2) hsqH x := by
    intro x
    have key : (ρ (g ^ 2)).toAdd x = (ρ g).toAdd ((ρ g).toAdd x) := by rw [pow_two, map_mul]; rfl
    simp only [dlin_apply]
    rw [← act_eq_add_dmap, ← act_eq_add_dmap, ← act_eq_add_dmap, key]
  have hps := pair_sq (B := M₀.B) (V := hc.VtSub hS.model t) (W := wsub hS t) hrel
    (dmap_iso hS hgH) (fun x => hgE x) (fun w hw => hgW w hw)
    (fun v hv w hw => bilin_vsub_wsub hS t hv hw) e e'
  rw [dlin_apply, hP, map_smul, LinearMap.smul_apply, smul_eq_mul] at hps
  rw [hps]
  rfl

theorem exists_bilin_dmap_tbar_ne_zero (h310chi : Stroth310ChiStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t : G} (hs : Sec7Hyp hc n' t) :
    ∃ e₀ e₁, M₀.B (dmap ρ (tbar hc hs.toSec5.mem) e₀) e₁ ≠ 0 := by
  obtain ⟨e₀, he₀⟩ := exists_dmap_tbar_ne_zero h310chi hS hs
  by_contra hcon
  push Not at hcon
  exact he₀ (M₀.nondeg _ (hcon e₀))

theorem bilin_dmap_comb (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t)
    (hr : Sec7A hc t r) {g₁ g₂ g₃ : Mbar M Q} (hg₁ : g₁ ∈ bar M Q (hc.CN t))
    (hg₂ : g₂ ∈ bar M Q (hc.CN t)) (hg₃ : g₃ ∈ bar M Q (hc.CN t)) {k₁ k₂ : K}
    (hk : ∀ w ∈ wsub hS t, dmap ρ g₃ w = k₁ • dmap ρ g₁ w + k₂ • dmap ρ g₂ w) (x : M₀.E)
    {w : M₀.E} (hw : w ∈ wsub hS t) :
    M₀.B (dmap ρ g₃ x) w = k₁ * M₀.B (dmap ρ g₁ x) w + k₂ * M₀.B (dmap ρ g₂ x) w := by
  have hg₁H := mem_bar_H0_of_CN hg₁
  have hg₂H := mem_bar_H0_of_CN hg₂
  have hg₃H := mem_bar_H0_of_CN hg₃
  obtain ⟨-, hg₁W, hg₁E⟩ := dmap_CN_facts h310chi h52a hS hs hr hg₁
  obtain ⟨-, hg₂W, hg₂E⟩ := dmap_CN_facts h310chi h52a hS hs hr hg₂
  obtain ⟨-, hg₃W, hg₃E⟩ := dmap_CN_facts h310chi h52a hS hs hr hg₃
  have h1 := bilin_comb (B := M₀.B) (V := hc.VtSub hS.model t) (W := wsub hS t)
    (D₁ := dlin hS g₁ hg₁H) (D₂ := dlin hS g₂ hg₂H) (D₃ := dlin hS g₃ hg₃H)
    (dmap_iso hS hg₁H) (dmap_iso hS hg₂H) (dmap_iso hS hg₃H) (fun x => hg₁E x) (fun x => hg₂E x)
    (fun x => hg₃E x) (fun w hw => hg₁W w hw) (fun w hw => hg₂W w hw) (fun w hw => hg₃W w hw)
    (fun w hw v hv => bilin_wsub_vsub hS t hw hv) (k₁ := k₁) (k₂ := k₂)
    (fun w hw => by simp only [dlin_apply]; exact hk w hw) x hw
  simpa [dlin_apply] using h1

theorem cscal_comm_comb (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hMp : Sec7CentreMpStatement) (hCommN : Sec7CommNStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t)
    (hr : Sec7A hc t r) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {g₁ g₂ g₃ h : Mbar M Q} (hg₁ : g₁ ∈ bar M Q (hc.CN t)) (hg₂ : g₂ ∈ bar M Q (hc.CN t))
    (hg₃ : g₃ ∈ bar M Q (hc.CN t)) (hh : h ∈ bar M Q (hc.CN t)) {k₁ k₂ : K}
    (hk : ∀ w ∈ wsub hS t, dmap ρ g₃ w = k₁ • dmap ρ g₁ w + k₂ • dmap ρ g₂ w) :
    cscal hc ρ hs.toSec5.mem ⁅g₃, h⁆ =
      k₁ * cscal hc ρ hs.toSec5.mem ⁅g₁, h⁆ + k₂ * cscal hc ρ hs.toSec5.mem ⁅g₂, h⁆ := by
  obtain ⟨-, -, hhE⟩ := dmap_CN_facts h310chi h52a hS hs hr hh
  obtain ⟨e₀, e₁, he⟩ := exists_bilin_dmap_tbar_ne_zero h310chi hS hs
  have hcomb := bilin_dmap_comb h310chi h52a hS hs hr hg₁ hg₂ hg₃ hk
  have h1 := cscal_comm_mul_bilin h310chi h52a hMp hCommN hS hs hr hZ0 hg₁ hh e₀ e₁
  have h2 := cscal_comm_mul_bilin h310chi h52a hMp hCommN hS hs hr hZ0 hg₂ hh e₀ e₁
  have h3 := cscal_comm_mul_bilin h310chi h52a hMp hCommN hS hs hr hZ0 hg₃ hh e₀ e₁
  rw [Tim79.QuadModel.B_comm (dmap ρ h e₀)] at h1
  rw [Tim79.QuadModel.B_comm (dmap ρ h e₀)] at h2
  rw [Tim79.QuadModel.B_comm (dmap ρ h e₀), hcomb e₀ (hhE e₁), hcomb e₁ (hhE e₀)] at h3
  refine mul_right_cancel₀ he ?_
  linear_combination h3 - k₁ * h1 - k₂ * h2

theorem cscal_comm_swap (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hMp : Sec7CentreMpStatement) (hCommN : Sec7CommNStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t)
    (hr : Sec7A hc t r) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {g h : Mbar M Q} (hg : g ∈ bar M Q (hc.CN t)) (hh : h ∈ bar M Q (hc.CN t)) :
    cscal hc ρ hs.toSec5.mem ⁅h, g⁆ = -cscal hc ρ hs.toSec5.mem ⁅g, h⁆ := by
  rw [← commutatorElement_inv g h]
  exact cscal_inv h310chi h52a hMp hS hs hr hZ0 (comm_mem_bar_Z0 hCommN hs hZ0 hg hh)

theorem cscal_comm_comb_right (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hMp : Sec7CentreMpStatement) (hCommN : Sec7CommNStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t)
    (hr : Sec7A hc t r) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {g h₁ h₂ h₃ : Mbar M Q} (hg : g ∈ bar M Q (hc.CN t)) (hh₁ : h₁ ∈ bar M Q (hc.CN t))
    (hh₂ : h₂ ∈ bar M Q (hc.CN t)) (hh₃ : h₃ ∈ bar M Q (hc.CN t)) {k₁ k₂ : K}
    (hk : ∀ w ∈ wsub hS t, dmap ρ h₃ w = k₁ • dmap ρ h₁ w + k₂ • dmap ρ h₂ w) :
    cscal hc ρ hs.toSec5.mem ⁅g, h₃⁆ =
      k₁ * cscal hc ρ hs.toSec5.mem ⁅g, h₁⁆ + k₂ * cscal hc ρ hs.toSec5.mem ⁅g, h₂⁆ := by
  rw [cscal_comm_swap h310chi h52a hMp hCommN hS hs hr hZ0 hh₃ hg,
    cscal_comm_swap h310chi h52a hMp hCommN hS hs hr hZ0 hh₁ hg,
    cscal_comm_swap h310chi h52a hMp hCommN hS hs hr hZ0 hh₂ hg,
    cscal_comm_comb h310chi h52a hMp hCommN hS hs hr hZ0 hh₁ hh₂ hh₃ hg hk]
  ring

theorem cscal_sq_comb (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement)
    (h52a : Stroth52aStatement) (hMp : Sec7CentreMpStatement) (hCommN : Sec7CommNStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t)
    (hr : Sec7A hc t r) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {g₁ g₂ g₃ : Mbar M Q} (hg₁ : g₁ ∈ bar M Q (hc.CN t)) (hg₂ : g₂ ∈ bar M Q (hc.CN t))
    (hg₃ : g₃ ∈ bar M Q (hc.CN t)) {k₁ k₂ : K}
    (hk : ∀ w ∈ wsub hS t, dmap ρ g₃ w = k₁ • dmap ρ g₁ w + k₂ • dmap ρ g₂ w) :
    cscal hc ρ hs.toSec5.mem (g₃ ^ 2) = k₁ ^ 2 * cscal hc ρ hs.toSec5.mem (g₁ ^ 2) +
      k₂ ^ 2 * cscal hc ρ hs.toSec5.mem (g₂ ^ 2) + k₁ * k₂ * cscal hc ρ hs.toSec5.mem ⁅g₁, g₂⁆ := by
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hS.card.trans hZ2)
  obtain ⟨-, -, hg₁E⟩ := dmap_CN_facts h310chi h52a hS hs hr hg₁
  obtain ⟨-, -, hg₂E⟩ := dmap_CN_facts h310chi h52a hS hs hr hg₂
  obtain ⟨-, -, hg₃E⟩ := dmap_CN_facts h310chi h52a hS hs hr hg₃
  obtain ⟨e₀, e₁, he⟩ := exists_bilin_dmap_tbar_ne_zero h310chi hS hs
  have hcomb := bilin_dmap_comb h310chi h52a hS hs hr hg₁ hg₂ hg₃ hk
  have h1 := cscal_sq_mul_bilin h310chi h51 h52a hMp hS hs hr hZ0 hg₁ e₀ e₁
  have h2 := cscal_sq_mul_bilin h310chi h51 h52a hMp hS hs hr hZ0 hg₂ e₀ e₁
  have h3 := cscal_sq_mul_bilin h310chi h51 h52a hMp hS hs hr hZ0 hg₃ e₀ e₁
  have h12 := cscal_comm_mul_bilin h310chi h52a hMp hCommN hS hs hr hZ0 hg₁ hg₂ e₀ e₁
  have a1 : M₀.B (dmap ρ g₁ e₀) (dmap ρ g₃ e₁) =
      k₁ * M₀.B (dmap ρ g₁ e₀) (dmap ρ g₁ e₁) + k₂ * M₀.B (dmap ρ g₁ e₀) (dmap ρ g₂ e₁) := by
    rw [Tim79.QuadModel.B_comm (dmap ρ g₁ e₀), hcomb e₁ (hg₁E e₀),
      Tim79.QuadModel.B_comm (dmap ρ g₁ e₁), Tim79.QuadModel.B_comm (dmap ρ g₂ e₁)]
    ring
  have a2 : M₀.B (dmap ρ g₂ e₀) (dmap ρ g₃ e₁) =
      k₁ * M₀.B (dmap ρ g₂ e₀) (dmap ρ g₁ e₁) + k₂ * M₀.B (dmap ρ g₂ e₀) (dmap ρ g₂ e₁) := by
    rw [Tim79.QuadModel.B_comm (dmap ρ g₂ e₀), hcomb e₁ (hg₂E e₀),
      Tim79.QuadModel.B_comm (dmap ρ g₁ e₁), Tim79.QuadModel.B_comm (dmap ρ g₂ e₁)]
    ring
  rw [hcomb e₀ (hg₃E e₁), a1, a2] at h3
  refine mul_right_cancel₀ he ?_
  linear_combination h3 - k₁ ^ 2 * h1 - k₂ ^ 2 * h2 - k₁ * k₂ * h12 -
    k₁ * k₂ * M₀.B (dmap ρ g₁ e₀) (dmap ρ g₂ e₁) * CharTwo.two_eq_zero (R := K)

noncomputable def deltaLift (hS : IsTensorSetup hc n M₀ ρ b) (t : G)
    (f : ↥(wsub hS t) →ₗ[K] M₀.E) : Mbar M Q := by
  classical
  exact if h : ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      f = delta hS t g (mem_bar_H0_of_CN hg) then Classical.choose h else 1

theorem deltaLift_mem (hS : IsTensorSetup hc n M₀ ρ b) (t : G) (f : ↥(wsub hS t) →ₗ[K] M₀.E) :
    deltaLift hS t f ∈ bar M Q (hc.CN t) := by
  by_cases h : ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      f = delta hS t g (mem_bar_H0_of_CN hg)
  · rw [deltaLift, dif_pos h]
    exact (Classical.choose_spec h).fst
  · rw [deltaLift, dif_neg h]
    exact Subgroup.one_mem _

theorem dmap_deltaLift (hS : IsTensorSetup hc n M₀ ρ b) (t : G) {f : ↥(wsub hS t) →ₗ[K] M₀.E}
    (hf : ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)), f = delta hS t g (mem_bar_H0_of_CN hg))
    {w : M₀.E} (hw : w ∈ wsub hS t) : dmap ρ (deltaLift hS t f) w = f ⟨w, hw⟩ := by
  obtain ⟨hg, h⟩ := Classical.choose_spec hf
  rw [deltaLift, dif_pos hf]
  conv_rhs => rw [h]
  rfl

theorem delta_deltaLift (hS : IsTensorSetup hc n M₀ ρ b) (t : G) {f : ↥(wsub hS t) →ₗ[K] M₀.E}
    (hf : ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)), f = delta hS t g (mem_bar_H0_of_CN hg)) :
    delta hS t (deltaLift hS t f) (mem_bar_H0_of_CN (deltaLift_mem hS t f)) = f :=
  LinearMap.ext fun w => by
    rw [delta_apply]
    exact dmap_deltaLift hS t hf w.2

noncomputable def bN (hS : IsTensorSetup hc n M₀ ρ b) {t : G} (ht : t ∈ LB M Q B)
    (f f' : ↥(wsub hS t) →ₗ[K] M₀.E) : K :=
  cscal hc ρ ht ⁅deltaLift hS t f, deltaLift hS t f'⁆

noncomputable def qN (hS : IsTensorSetup hc n M₀ ρ b) {t : G} (ht : t ∈ LB M Q B)
    (f : ↥(wsub hS t) →ₗ[K] M₀.E) : K :=
  cscal hc ρ ht (deltaLift hS t f ^ 2)

theorem bN_delta (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hMp : Sec7CentreMpStatement) (hCommN : Sec7CommNStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t)
    (hr : Sec7A hc t r) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {g h : Mbar M Q} (hg : g ∈ bar M Q (hc.CN t)) (hh : h ∈ bar M Q (hc.CN t)) :
    bN hS hs.toSec5.mem (delta hS t g (mem_bar_H0_of_CN hg)) (delta hS t h (mem_bar_H0_of_CN hh)) =
      cscal hc ρ hs.toSec5.mem ⁅g, h⁆ := by
  have hL : ∀ w ∈ wsub hS t, dmap ρ (deltaLift hS t (delta hS t g (mem_bar_H0_of_CN hg))) w =
      (1 : K) • dmap ρ g w + (0 : K) • dmap ρ g w := fun w hw => by
    rw [dmap_deltaLift hS t ⟨g, hg, rfl⟩ hw, one_smul, zero_smul, add_zero]
    rfl
  have hR : ∀ w ∈ wsub hS t, dmap ρ (deltaLift hS t (delta hS t h (mem_bar_H0_of_CN hh))) w =
      (1 : K) • dmap ρ h w + (0 : K) • dmap ρ h w := fun w hw => by
    rw [dmap_deltaLift hS t ⟨h, hh, rfl⟩ hw, one_smul, zero_smul, add_zero]
    rfl
  unfold bN
  rw [cscal_comm_comb h310chi h52a hMp hCommN hS hs hr hZ0 hg hg (deltaLift_mem hS t _)
      (deltaLift_mem hS t _) hL,
    cscal_comm_comb_right h310chi h52a hMp hCommN hS hs hr hZ0 hg hh hh (deltaLift_mem hS t _) hR]
  ring

theorem qN_delta (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement)
    (h52a : Stroth52aStatement) (hMp : Sec7CentreMpStatement) (hCommN : Sec7CommNStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t)
    (hr : Sec7A hc t r) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {g : Mbar M Q} (hg : g ∈ bar M Q (hc.CN t)) :
    qN hS hs.toSec5.mem (delta hS t g (mem_bar_H0_of_CN hg)) =
      cscal hc ρ hs.toSec5.mem (g ^ 2) := by
  have h := cscal_sq_comb h310chi h51 h52a hMp hCommN hS hs hr hZ0 hg hg (deltaLift_mem hS t _)
    (k₁ := 1) (k₂ := 0) fun w hw => by
      rw [dmap_deltaLift hS t ⟨g, hg, rfl⟩ hw, one_smul, zero_smul, add_zero]
      rfl
  unfold qN
  rw [h]
  ring

theorem bN_comb_left (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hMp : Sec7CentreMpStatement) (hCommN : Sec7CommNStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t)
    (hr : Sec7A hc t r) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {f₁ f₂ f₃ : ↥(wsub hS t) →ₗ[K] M₀.E}
    (h₁ : ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)), f₁ = delta hS t g (mem_bar_H0_of_CN hg))
    (h₂ : ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)), f₂ = delta hS t g (mem_bar_H0_of_CN hg))
    (h₃ : ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)), f₃ = delta hS t g (mem_bar_H0_of_CN hg))
    {k₁ k₂ : K} (h : f₃ = k₁ • f₁ + k₂ • f₂) (f : ↥(wsub hS t) →ₗ[K] M₀.E) :
    bN hS hs.toSec5.mem f₃ f = k₁ * bN hS hs.toSec5.mem f₁ f + k₂ * bN hS hs.toSec5.mem f₂ f :=
  cscal_comm_comb h310chi h52a hMp hCommN hS hs hr hZ0 (deltaLift_mem hS t f₁)
    (deltaLift_mem hS t f₂) (deltaLift_mem hS t f₃) (deltaLift_mem hS t f) fun w hw => by
      rw [dmap_deltaLift hS t h₃ hw, dmap_deltaLift hS t h₁ hw, dmap_deltaLift hS t h₂ hw, h]
      rfl

theorem bN_comb_right (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hMp : Sec7CentreMpStatement) (hCommN : Sec7CommNStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t)
    (hr : Sec7A hc t r) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {f₁ f₂ f₃ : ↥(wsub hS t) →ₗ[K] M₀.E}
    (h₁ : ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)), f₁ = delta hS t g (mem_bar_H0_of_CN hg))
    (h₂ : ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)), f₂ = delta hS t g (mem_bar_H0_of_CN hg))
    (h₃ : ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)), f₃ = delta hS t g (mem_bar_H0_of_CN hg))
    {k₁ k₂ : K} (h : f₃ = k₁ • f₁ + k₂ • f₂) (f : ↥(wsub hS t) →ₗ[K] M₀.E) :
    bN hS hs.toSec5.mem f f₃ = k₁ * bN hS hs.toSec5.mem f f₁ + k₂ * bN hS hs.toSec5.mem f f₂ :=
  cscal_comm_comb_right h310chi h52a hMp hCommN hS hs hr hZ0 (deltaLift_mem hS t f)
    (deltaLift_mem hS t f₁) (deltaLift_mem hS t f₂) (deltaLift_mem hS t f₃) fun w hw => by
      rw [dmap_deltaLift hS t h₃ hw, dmap_deltaLift hS t h₁ hw, dmap_deltaLift hS t h₂ hw, h]
      rfl

noncomputable def bForm (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hMp : Sec7CentreMpStatement) (hCommN : Sec7CommNStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t)
    (hr : Sec7A hc t r) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (S : Submodule K (↥(wsub hS t) →ₗ[K] M₀.E))
    (hSΔ : ∀ f ∈ S, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      f = delta hS t g (mem_bar_H0_of_CN hg)) :
    LinearMap.BilinForm K ↥S :=
  LinearMap.mk₂ K (fun f f' => bN hS hs.toSec5.mem f f')
    (fun f₁ f₂ f => by
      rw [bN_comb_left h310chi h52a hMp hCommN hS hs hr hZ0 (hSΔ _ f₁.2) (hSΔ _ f₂.2)
        (hSΔ _ (f₁ + f₂).2) (k₁ := 1) (k₂ := 1) (by simp), one_mul, one_mul])
    (fun c f₁ f => by
      rw [bN_comb_left h310chi h52a hMp hCommN hS hs hr hZ0 (hSΔ _ f₁.2) (hSΔ _ f₁.2)
        (hSΔ _ (c • f₁).2) (k₁ := c) (k₂ := 0) (by simp), zero_mul, add_zero, smul_eq_mul])
    (fun f f₁ f₂ => by
      rw [bN_comb_right h310chi h52a hMp hCommN hS hs hr hZ0 (hSΔ _ f₁.2) (hSΔ _ f₂.2)
        (hSΔ _ (f₁ + f₂).2) (k₁ := 1) (k₂ := 1) (by simp), one_mul, one_mul])
    (fun c f f₁ => by
      rw [bN_comb_right h310chi h52a hMp hCommN hS hs hr hZ0 (hSΔ _ f₁.2) (hSΔ _ f₁.2)
        (hSΔ _ (c • f₁).2) (k₁ := c) (k₂ := 0) (by simp), zero_mul, add_zero, smul_eq_mul])

theorem bForm_apply (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hMp : Sec7CentreMpStatement) (hCommN : Sec7CommNStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t)
    (hr : Sec7A hc t r) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (S : Submodule K (↥(wsub hS t) →ₗ[K] M₀.E))
    (hSΔ : ∀ f ∈ S, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      f = delta hS t g (mem_bar_H0_of_CN hg)) (f f' : ↥S) :
    bForm h310chi h52a hMp hCommN hS hs hr hZ0 S hSΔ f f' = bN hS hs.toSec5.mem f f' := by
  rw [bForm, LinearMap.mk₂_apply]

theorem bForm_self (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hMp : Sec7CentreMpStatement) (hCommN : Sec7CommNStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t)
    (hr : Sec7A hc t r) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (S : Submodule K (↥(wsub hS t) →ₗ[K] M₀.E))
    (hSΔ : ∀ f ∈ S, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      f = delta hS t g (mem_bar_H0_of_CN hg)) (f : ↥S) :
    bForm h310chi h52a hMp hCommN hS hs hr hZ0 S hSΔ f f = 0 := by
  rw [bForm_apply]
  unfold bN
  rw [commutatorElement_self, cscal_one h310chi hS hs]

theorem qN_smul (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement)
    (h52a : Stroth52aStatement) (hMp : Sec7CentreMpStatement) (hCommN : Sec7CommNStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t)
    (hr : Sec7A hc t r) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (S : Submodule K (↥(wsub hS t) →ₗ[K] M₀.E))
    (hSΔ : ∀ f ∈ S, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      f = delta hS t g (mem_bar_H0_of_CN hg)) (a : K) (f : ↥S) :
    qN hS hs.toSec5.mem ↑(a • f) = a ^ 2 * qN hS hs.toSec5.mem f := by
  have h := cscal_sq_comb h310chi h51 h52a hMp hCommN hS hs hr hZ0 (deltaLift_mem hS t f)
    (deltaLift_mem hS t f) (deltaLift_mem hS t ↑(a • f)) (k₁ := a) (k₂ := 0) fun w hw => by
      rw [dmap_deltaLift hS t (hSΔ _ (a • f).2) hw, dmap_deltaLift hS t (hSΔ _ f.2) hw]
      simp
  unfold qN
  rw [h]
  ring

theorem qN_add (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement)
    (h52a : Stroth52aStatement) (hMp : Sec7CentreMpStatement) (hCommN : Sec7CommNStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t)
    (hr : Sec7A hc t r) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (S : Submodule K (↥(wsub hS t) →ₗ[K] M₀.E))
    (hSΔ : ∀ f ∈ S, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      f = delta hS t g (mem_bar_H0_of_CN hg)) (f f' : ↥S) :
    qN hS hs.toSec5.mem ↑(f + f') = qN hS hs.toSec5.mem f + qN hS hs.toSec5.mem f' +
      bForm h310chi h52a hMp hCommN hS hs hr hZ0 S hSΔ f f' := by
  have h := cscal_sq_comb h310chi h51 h52a hMp hCommN hS hs hr hZ0 (deltaLift_mem hS t f)
    (deltaLift_mem hS t f') (deltaLift_mem hS t ↑(f + f')) (k₁ := 1) (k₂ := 1) fun w hw => by
      rw [dmap_deltaLift hS t (hSΔ _ (f + f').2) hw, dmap_deltaLift hS t (hSΔ _ f.2) hw,
        dmap_deltaLift hS t (hSΔ _ f'.2) hw]
      simp
  rw [bForm_apply]
  unfold qN bN
  rw [h]
  ring

theorem mem_ker_bForm_iff (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hMp : Sec7CentreMpStatement) (hCommN : Sec7CommNStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t)
    (hr : Sec7A hc t r) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (S : Submodule K (↥(wsub hS t) →ₗ[K] M₀.E))
    (hSΔ : ∀ f ∈ S, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      f = delta hS t g (mem_bar_H0_of_CN hg))
    (hΔS : ∀ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)), delta hS t g (mem_bar_H0_of_CN hg) ∈ S)
    {Zn : Subgroup G} (hZn : IsCentrePre Zn (hc.CN t) Q) {g : Mbar M Q}
    (hg : g ∈ bar M Q (hc.CN t)) :
    (⟨delta hS t g (mem_bar_H0_of_CN hg), hΔS g hg⟩ : ↥S) ∈
        LinearMap.ker (bForm h310chi h52a hMp hCommN hS hs hr hZ0 S hSΔ) ↔ g ∈ bar M Q Zn := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h0
    obtain ⟨x, hx, rfl⟩ := exists_of_mem_bar hg
    refine mk_mem_bar x ((hZn x).mpr ⟨hx, fun y hy => ?_⟩)
    have hyM : y ∈ M := hc.Rt_le_M t (Ctx.mem_CN.mp hy).1
    have hy' : (QuotientGroup.mk (⟨y, hyM⟩ : ↥M) : Mbar M Q) ∈ bar M Q (hc.CN t) :=
      mk_mem_bar _ hy
    have h1 : bN hS hs.toSec5.mem (delta hS t _ (mem_bar_H0_of_CN hg))
        (delta hS t _ (mem_bar_H0_of_CN hy')) = 0 :=
      LinearMap.congr_fun h0 ⟨_, hΔS _ hy'⟩
    rw [bN_delta h310chi h52a hMp hCommN hS hs hr hZ0 hg hy'] at h1
    have h2 := (cscal_eq_zero_iff h310chi h52a hMp hS hs hr hZ0
      (comm_mem_bar_Z0 hCommN hs hZ0 hg hy')).mp h1
    exact (mk_commute_iff x ⟨y, hyM⟩).mp (commutatorElement_eq_one_iff_commute.mp h2)
  · intro hgZ
    refine LinearMap.ext fun f => ?_
    obtain ⟨h, hh, hfh⟩ := hSΔ f f.2
    obtain ⟨z, hz, rfl⟩ := exists_of_mem_bar hgZ
    obtain ⟨y, hy, rfl⟩ := exists_of_mem_bar hh
    have hc1 : ⁅(QuotientGroup.mk z : Mbar M Q), QuotientGroup.mk y⁆ = 1 :=
      commutatorElement_eq_one_iff_commute.mpr ((mk_commute_iff z y).mpr (((hZn z).mp hz).2 y hy))
    rw [LinearMap.zero_apply, bForm_apply]
    show bN hS hs.toSec5.mem (delta hS t _ (mem_bar_H0_of_CN hg)) (f : ↥(wsub hS t) →ₗ[K] M₀.E) = 0
    rw [hfh, bN_delta h310chi h52a hMp hCommN hS hs hr hZ0 hg hh, hc1, cscal_one h310chi hS hs]

theorem forall_bForm_eq_zero_iff (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hMp : Sec7CentreMpStatement) (hCommN : Sec7CommNStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t)
    (hr : Sec7A hc t r) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (S : Submodule K (↥(wsub hS t) →ₗ[K] M₀.E))
    (hSΔ : ∀ f ∈ S, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      f = delta hS t g (mem_bar_H0_of_CN hg))
    (hΔS : ∀ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)), delta hS t g (mem_bar_H0_of_CN hg) ∈ S)
    {Zn : Subgroup G} (hZn : IsCentrePre Zn (hc.CN t) Q) {g : Mbar M Q}
    (hg : g ∈ bar M Q (hc.CN t)) :
    (∀ f, bForm h310chi h52a hMp hCommN hS hs hr hZ0 S hSΔ
        ⟨delta hS t g (mem_bar_H0_of_CN hg), hΔS g hg⟩ f = 0) ↔ g ∈ bar M Q Zn := by
  rw [← mem_ker_bForm_iff h310chi h52a hMp hCommN hS hs hr hZ0 S hSΔ hΔS hZn hg,
    LinearMap.mem_ker, LinearMap.ext_iff]
  rfl

theorem bN_conj (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hMp : Sec7CentreMpStatement) (hCommN : Sec7CommNStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t)
    (hr : Sec7A hc t r) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {x g h : Mbar M Q} (hx : x ∈ bar M Q (Rt M (LB M Q B) t)) (hg : g ∈ bar M Q (hc.CN t))
    (hh : h ∈ bar M Q (hc.CN t)) :
    bN hS hs.toSec5.mem
        (delta hS t (x * g * x⁻¹) (mem_bar_H0_of_CN (hc.bar_CN_conj_mem hs.toSec5.mem hx hg)))
        (delta hS t (x * h * x⁻¹) (mem_bar_H0_of_CN (hc.bar_CN_conj_mem hs.toSec5.mem hx hh))) =
      bN hS hs.toSec5.mem (delta hS t g (mem_bar_H0_of_CN hg))
        (delta hS t h (mem_bar_H0_of_CN hh)) := by
  rw [bN_delta h310chi h52a hMp hCommN hS hs hr hZ0 (hc.bar_CN_conj_mem hs.toSec5.mem hx hg)
      (hc.bar_CN_conj_mem hs.toSec5.mem hx hh),
    bN_delta h310chi h52a hMp hCommN hS hs hr hZ0 hg hh, ← conjugate_commutatorElement,
    conj_eq_of_mem_bar_centre hc hZ0 (comm_mem_bar_Z0 hCommN hs hZ0 hg hh) hx]

theorem qN_conj (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement)
    (h52a : Stroth52aStatement) (hMp : Sec7CentreMpStatement) (hCommN : Sec7CommNStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t)
    (hr : Sec7A hc t r) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {x g : Mbar M Q} (hx : x ∈ bar M Q (Rt M (LB M Q B) t)) (hg : g ∈ bar M Q (hc.CN t)) :
    qN hS hs.toSec5.mem
        (delta hS t (x * g * x⁻¹) (mem_bar_H0_of_CN (hc.bar_CN_conj_mem hs.toSec5.mem hx hg))) =
      qN hS hs.toSec5.mem (delta hS t g (mem_bar_H0_of_CN hg)) := by
  rw [qN_delta h310chi h51 h52a hMp hCommN hS hs hr hZ0 (hc.bar_CN_conj_mem hs.toSec5.mem hx hg),
    qN_delta h310chi h51 h52a hMp hCommN hS hs hr hZ0 hg, conj_pow,
    conj_eq_of_mem_bar_centre hc hZ0 (sq_mem_bar_Z0 h51 hs hr hZ0 hg) hx]

theorem bForm_deltaAct (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hMp : Sec7CentreMpStatement) (hCommN : Sec7CommNStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t)
    (hr : Sec7A hc t r) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hSΔ : ∀ f ∈ deltaSub hS t, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      f = delta hS t g (mem_bar_H0_of_CN hg))
    (x : ↥(bar M Q (Rt M (LB M Q B) t))) (f f' : ↥(deltaSub hS t)) :
    bForm h310chi h52a hMp hCommN hS hs hr hZ0 (deltaSub hS t) hSΔ
        (deltaAct hS hs.toSec5.mem x f) (deltaAct hS hs.toSec5.mem x f') =
      bForm h310chi h52a hMp hCommN hS hs hr hZ0 (deltaSub hS t) hSΔ f f' := by
  obtain ⟨f, hf⟩ := f
  obtain ⟨f', hf'⟩ := f'
  obtain ⟨g, hg, rfl⟩ := hSΔ f hf
  obtain ⟨h, hh, rfl⟩ := hSΔ f' hf'
  rw [deltaAct_delta hS hs.toSec5.mem x hg, deltaAct_delta hS hs.toSec5.mem x hh, bForm_apply,
    bForm_apply]
  exact bN_conj h310chi h52a hMp hCommN hS hs hr hZ0 x.2 hg hh

theorem qN_deltaAct (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement)
    (h52a : Stroth52aStatement) (hMp : Sec7CentreMpStatement) (hCommN : Sec7CommNStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t)
    (hr : Sec7A hc t r) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hSΔ : ∀ f ∈ deltaSub hS t, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      f = delta hS t g (mem_bar_H0_of_CN hg))
    (x : ↥(bar M Q (Rt M (LB M Q B) t))) (f : ↥(deltaSub hS t)) :
    qN hS hs.toSec5.mem (deltaAct hS hs.toSec5.mem x f) = qN hS hs.toSec5.mem f := by
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg, rfl⟩ := hSΔ f hf
  rw [deltaAct_delta hS hs.toSec5.mem x hg]
  exact qN_conj h310chi h51 h52a hMp hCommN hS hs hr hZ0 x.2 hg

end CFSG.RankThree.GF2n.Stroth80.S715L

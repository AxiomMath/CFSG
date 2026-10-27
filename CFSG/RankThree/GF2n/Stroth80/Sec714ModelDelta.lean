module

public import CFSG.RankThree.GF2n.Stroth80.Sec41iiTensorSide
public import CFSG.RankThree.GF2n.Stroth80.Sec7Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5Stmt
import CFSG.RankThree.GF2n.Stroth80.Sec7Transport
import CFSG.RankThree.GF2n.Stroth80.Sec111Order

public section

namespace CFSG.RankThree.GF2n.Stroth80.S714

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

section Maps

omit [Finite G] [Finite K] in
variable (ρ) in
@[expose] def dmap (g : Mbar M Q) (e : M₀.E) : M₀.E := (ρ g).toAdd e - e

omit [Finite G] [Finite K] in
theorem act_eq_add_dmap (g : Mbar M Q) (e : M₀.E) : (ρ g).toAdd e = e + dmap ρ g e := by
  simp [dmap]

omit [Finite G] [Finite K] in
theorem dmap_add (g : Mbar M Q) (e f : M₀.E) : dmap ρ g (e + f) = dmap ρ g e + dmap ρ g f := by
  simp only [dmap, map_add]
  abel

omit [Finite G] [Finite K] in
theorem dmap_zero (g : Mbar M Q) : dmap ρ g 0 = 0 := by
  simp [dmap]

omit [Finite G] [Finite K] in
theorem dmap_one (e : M₀.E) : dmap ρ 1 e = 0 := by
  simp only [dmap, map_one]
  exact sub_self e

omit [Finite G] [Finite K] in
theorem dmap_mul (g h : Mbar M Q) (e : M₀.E) :
    dmap ρ (g * h) e = dmap ρ g e + dmap ρ h e + dmap ρ g (dmap ρ h e) := by
  have hgh : (ρ (g * h)).toAdd e = (ρ g).toAdd ((ρ h).toAdd e) := by
    rw [map_mul]
    rfl
  simp only [dmap, hgh, map_sub]
  abel

theorem dmap_smul (hS : IsTensorSetup hc n M₀ ρ b) {g : Mbar M Q}
    (hg : g ∈ bar M Q (H0 M Z)) (c : K) (e : M₀.E) : dmap ρ g (c • e) = c • dmap ρ g e := by
  simp only [dmap, hS.lin g hg c e, smul_sub]

@[expose] def dlin (hS : IsTensorSetup hc n M₀ ρ b) (g : Mbar M Q)
    (hg : g ∈ bar M Q (H0 M Z)) : M₀.E →ₗ[K] M₀.E where
  toFun := dmap ρ g
  map_add' := dmap_add g
  map_smul' := dmap_smul hS hg

theorem dlin_apply (hS : IsTensorSetup hc n M₀ ρ b) {g : Mbar M Q}
    (hg : g ∈ bar M Q (H0 M Z)) (e : M₀.E) : dlin hS g hg e = dmap ρ g e := rfl

theorem dmap_iso (hS : IsTensorSetup hc n M₀ ρ b) {g : Mbar M Q}
    (hg : g ∈ bar M Q (H0 M Z)) (e f : M₀.E) :
    M₀.B (e + dmap ρ g e) (f + dmap ρ g f) = M₀.B e f := by
  rw [← act_eq_add_dmap, ← act_eq_add_dmap]
  exact hS.iso g hg e f

theorem dmap_pi (hS : IsTensorSetup hc n M₀ ρ b) (m : ↥M) {x : G} (hx : x ∈ Q) :
    dmap ρ (QuotientGroup.mk m) (M₀.π x) = M₀.π ⁅(m : G), x⁆ := by
  have hmx : (m : G) * x * (m : G)⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 m.2) x).mp hx
  rw [dmap, ← hS.conj m x hx, commutatorElement_def, M₀.π_mul _ hmx _ (Q.inv_mem hx),
    Tim79.QuadModel.pi_inv M₀ hx, sub_eq_add_neg]

omit [Finite G] [Finite K] in
theorem dmap_comm {g h : Mbar M Q} (hgh : g * h = h * g) (e : M₀.E) :
    dmap ρ g (dmap ρ h e) = dmap ρ h (dmap ρ g e) := by
  have h1 := dmap_mul (ρ := ρ) g h e
  have h2 := dmap_mul (ρ := ρ) h g e
  rw [hgh] at h1
  rw [h1] at h2
  linear_combination (norm := abel_nf) h2

end Maps

theorem mk_mem_bar {S : Subgroup G} (m : ↥M) (hm : (m : G) ∈ S) :
    (QuotientGroup.mk m : Mbar M Q) ∈ bar M Q S :=
  Subgroup.mem_map.mpr ⟨m, Subgroup.mem_subgroupOf.mpr hm, rfl⟩

theorem exists_of_mem_bar {S : Subgroup G} {g : Mbar M Q} (hg : g ∈ bar M Q S) :
    ∃ m : ↥M, (m : G) ∈ S ∧ (QuotientGroup.mk m : Mbar M Q) = g := by
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hg
  exact ⟨m, Subgroup.mem_subgroupOf.mp hm, rfl⟩

section Sub

variable (hS : IsTensorSetup hc n M₀ ρ b) (t : G) in
@[expose] def wsub : Submodule K M₀.E :=
  imgSub M₀ (Wt Q (Vt M (LB M Q B) B Z t))
    (fun c _ he => smul_mem_img_Wt M₀ hS.model.reg (hc.Vt_le_Q t) c he)

theorem mem_wsub (hS : IsTensorSetup hc n M₀ ρ b) (t : G) {e : M₀.E} :
    e ∈ wsub hS t ↔ e ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t)) := Iff.rfl

theorem bilin_wsub_vsub (hS : IsTensorSetup hc n M₀ ρ b) (t : G) {w v : M₀.E}
    (hw : w ∈ wsub hS t) (hv : v ∈ hc.VtSub hS.model t) : M₀.B w v = 0 :=
  (mem_img_Wt_iff M₀ hS.model.reg (hc.Vt_le_Q t)).mp hw v ((hc.mem_VtSub hS.model t).mp hv)

theorem bilin_vsub_wsub (hS : IsTensorSetup hc n M₀ ρ b) (t : G) {v w : M₀.E}
    (hv : v ∈ hc.VtSub hS.model t) (hw : w ∈ wsub hS t) : M₀.B v w = 0 := by
  rw [Tim79.QuadModel.B_comm, bilin_wsub_vsub hS t hw hv, neg_zero]

theorem psi_facts (h310chi : Stroth310ChiStatement) (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ}
    {t : G} (hs : Sec5Hyp hc n' t) (hSpOm : SpNat hc t ∨ OmegaNat hc t) (tm : ↥M)
    (htm : (tm : G) = t) :
    (∀ e, dmap ρ (QuotientGroup.mk tm) e ∈ hc.VtSub hS.model t) ∧
      (∀ v ∈ hc.VtSub hS.model t, ∃ e, dmap ρ (QuotientGroup.mk tm) e = v) ∧
      ∀ e, dmap ρ (QuotientGroup.mk tm) e = 0 ↔ e ∈ wsub hS t := by
  subst htm
  have ht : (tm : G) ∈ LB M Q B := hs.mem
  have htM : (tm : G) ∈ M := tm.2
  obtain ⟨hVeq, hWeq⟩ := h310chi G M Q Z B hc n' tm hs hSpOm
  obtain ⟨htQ, htQ'⟩ := hc.conj_mem_Q_of_mem_M htM
  have htH : (QuotientGroup.mk tm : Mbar M Q) ∈ bar M Q (H0 M Z) :=
    mk_mem_bar tm (hc.Rt_le_H0 _ (le_Rt (M := M) (LB M Q B) ht ht))
  let T : M₀.E ≃ₗ[K] M₀.E := AddEquiv.toLinearEquiv (ρ (QuotientGroup.mk tm)).toAdd
    (hS.lin _ htH)
  have hT : ∀ x ∈ Q, M₀.π ((tm : G) * x * (tm : G)⁻¹) = T (M₀.π x) := fun x hx => hS.conj tm x hx
  have hrange : ∀ v, v ∈ M₀.img (Vt M (LB M Q B) B Z tm) ↔
      v ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1) := by
    intro v
    rw [hVeq]
    exact mem_img_comm_zpowers_sup_iff M₀ hS.model.reg T htQ htQ' hT v
  refine ⟨fun e => ?_, fun v hv => ?_, fun e => ?_⟩
  · refine (hc.mem_VtSub hS.model tm).mpr ((hrange _).mpr ⟨e, rfl⟩)
  · obtain ⟨e, he⟩ := (hrange v).mp ((hc.mem_VtSub hS.model tm).mp hv)
    exact ⟨e, he⟩
  · rw [mem_wsub, hWeq]
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    have hcQ : ⁅(tm : G), x⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem (htQ x hxQ) (Q.inv_mem hxQ)
    rw [dmap_pi hS tm hxQ, M₀.π_ker _ hcQ]
    constructor
    · intro h
      exact M₀.pi_mem_img ((hc.mem_Q1_iff htM).mpr ⟨hxQ, h⟩) hxQ
    · rintro ⟨y, hyQ1, hyQ, hyx⟩
      have h1 : ⁅(tm : G), y⁆ ∈ Z := ((hc.mem_Q1_iff htM).mp hyQ1).2
      have h2 : M₀.π ((tm : G) * y * (tm : G)⁻¹) = M₀.π y :=
        (M₀.comm_mem_iff hyQ (htQ y hyQ)).mp h1
      have h3 : M₀.π ((tm : G) * x * (tm : G)⁻¹) = M₀.π x := by
        rw [hT x hxQ, ← hyx, ← hT y hyQ, h2]
      exact (M₀.comm_mem_iff hxQ (htQ x hxQ)).mpr h3

end Sub

section Delta

theorem mem_bar_H0_of_CN {t : G} {g : Mbar M Q} (hg : g ∈ bar M Q (hc.CN t)) :
    g ∈ bar M Q (H0 M Z) := by
  obtain ⟨m, hm, rfl⟩ := exists_of_mem_bar hg
  exact mk_mem_bar m (hc.Rt_le_H0 t (Ctx.mem_CN.mp hm).1)

theorem mem_bar_H0_of_Rt (hc : Ctx M Q Z B) {t : G} {g : Mbar M Q}
    (hg : g ∈ bar M Q (Rt M (LB M Q B) t)) :
    g ∈ bar M Q (H0 M Z) := by
  obtain ⟨m, hm, rfl⟩ := exists_of_mem_bar hg
  exact mk_mem_bar m (hc.Rt_le_H0 t hm)

theorem act_mem_wsub (hS : IsTensorSetup hc n M₀ ρ b) {t : G} (ht : t ∈ LB M Q B)
    {h : Mbar M Q} (hh : h ∈ bar M Q (Rt M (LB M Q B) t)) {w : M₀.E} (hw : w ∈ wsub hS t) :
    (ρ h).toAdd w ∈ wsub hS t := by
  obtain ⟨m, hm, rfl⟩ := exists_of_mem_bar hh
  obtain ⟨x, hxW, hxQ, rfl⟩ := M₀.mem_img.mp ((mem_wsub hS t).mp hw)
  rw [← hS.conj m x hxQ]
  have hmQ : (m : G) ∈ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2 m.2
  have hmV : (m : G) ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    hc.Rt_normalizes_Vt ht hm
  have hW := conj_mem_Wt hmQ hmV hxW
  exact M₀.pi_mem_img hW hW.1

theorem dmap_CN_facts (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t)
    (hr : Sec7A hc t r) {g : Mbar M Q} (hg : g ∈ bar M Q (hc.CN t)) :
    (∀ v ∈ hc.VtSub hS.model t, dmap ρ g v = 0) ∧
      (∀ w ∈ wsub hS t, dmap ρ g w ∈ hc.VtSub hS.model t) ∧ ∀ e, dmap ρ g e ∈ wsub hS t := by
  obtain ⟨m, hmN, rfl⟩ := exists_of_mem_bar hg
  have hmR : (m : G) ∈ Rt M (LB M Q B) t := (Ctx.mem_CN.mp hmN).1
  have hcQ : ∀ x ∈ Q, ⁅(m : G), x⁆ ∈ Q := fun x hx => by
    rw [commutatorElement_def]
    exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 m.2) x).mp hx)
      (Q.inv_mem hx)
  have h1 : ∀ v ∈ hc.VtSub hS.model t, dmap ρ (QuotientGroup.mk m) v = 0 := by
    intro v hv
    obtain ⟨x, hxV, hxQ, rfl⟩ := M₀.mem_img.mp ((hc.mem_VtSub hS.model t).mp hv)
    rw [dmap_pi hS m hxQ]
    exact (M₀.π_ker _ (hcQ x hxQ)).mpr ((Ctx.mem_CN.mp hmN).2 x hxV)
  have h2 : ∀ w ∈ wsub hS t, dmap ρ (QuotientGroup.mk m) w ∈ hc.VtSub hS.model t := by
    intro w hw
    obtain ⟨x, hxW, hxQ, rfl⟩ := M₀.mem_img.mp ((mem_wsub hS t).mp hw)
    rw [dmap_pi hS m hxQ]
    have hV := (h52a G M Q Z B hc n' t hs.toSec5 hs.omegaNat r hr.mem hr.plane _ _ _ _ rfl rfl
      rfl rfl).2 m hmN x hxW
    exact (hc.mem_VtSub hS.model t).mpr (M₀.pi_mem_img hV (hcQ x hxQ))
  refine ⟨h1, h2, fun e => ?_⟩
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  let tm : ↥M := ⟨t, hc.LB_le_M ht⟩
  obtain ⟨hψV, -, hψW⟩ := psi_facts h310chi hS hs.toSec5 (Or.inr hs.omegaNat) tm rfl
  have hcomm : (QuotientGroup.mk m : Mbar M Q) * QuotientGroup.mk tm =
      QuotientGroup.mk tm * QuotientGroup.mk m :=
    ((mk_commute_iff m tm).mpr (hc.Rt_comm_mem_Q hmR)).eq
  refine (hψW _).mp ?_
  rw [dmap_comm hcomm.symm e]
  exact h1 _ (hψV e)

variable (hS : IsTensorSetup hc n M₀ ρ b) (t : G) in
@[expose] def delta (g : Mbar M Q) (hg : g ∈ bar M Q (H0 M Z)) : ↥(wsub hS t) →ₗ[K] M₀.E :=
  (dlin hS g hg).comp (wsub hS t).subtype

theorem delta_apply (hS : IsTensorSetup hc n M₀ ρ b) (t : G) {g : Mbar M Q}
    (hg : g ∈ bar M Q (H0 M Z)) (w : ↥(wsub hS t)) : delta hS t g hg w = dmap ρ g w := rfl

theorem delta_congr (hS : IsTensorSetup hc n M₀ ρ b) (t : G) {g g' : Mbar M Q} (h : g = g')
    (hg : g ∈ bar M Q (H0 M Z)) (hg' : g' ∈ bar M Q (H0 M Z)) :
    delta hS t g hg = delta hS t g' hg' := by
  subst h
  rfl

theorem delta_mul (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t)
    (hr : Sec7A hc t r) {g₁ g₂ : Mbar M Q} (hg₁ : g₁ ∈ bar M Q (hc.CN t))
    (hg₂ : g₂ ∈ bar M Q (hc.CN t)) :
    delta hS t (g₁ * g₂) (Subgroup.mul_mem _ (mem_bar_H0_of_CN hg₁) (mem_bar_H0_of_CN hg₂)) =
      delta hS t g₁ (mem_bar_H0_of_CN hg₁) + delta hS t g₂ (mem_bar_H0_of_CN hg₂) := by
  refine LinearMap.ext fun w => ?_
  obtain ⟨h1, -, -⟩ := dmap_CN_facts h310chi h52a hS hs hr hg₁
  obtain ⟨-, h2, -⟩ := dmap_CN_facts h310chi h52a hS hs hr hg₂
  simp only [delta_apply, LinearMap.add_apply, dmap_mul, h1 _ (h2 _ w.2), add_zero]

theorem delta_eq_zero_iff (hCRW : Sec7CRWStatement) (hMp : Sec7CentreMpStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t : G} (hs : Sec7Hyp hc n' t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {g : Mbar M Q}
    (hg : g ∈ bar M Q (Rt M (LB M Q B) t)) :
    delta hS t g (mem_bar_H0_of_Rt hc hg) = 0 ↔ g ∈ bar M Q Z0 := by
  have hcQ : ∀ m : ↥M, ∀ x ∈ Q, ⁅(m : G), x⁆ ∈ Q := fun m x hx => by
    rw [commutatorElement_def]
    exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 m.2) x).mp hx)
      (Q.inv_mem hx)
  constructor
  · intro h0
    obtain ⟨m, hmR, rfl⟩ := exists_of_mem_bar hg
    refine mk_mem_bar m (hCRW G M Q Z B hc n' t hs Z0 hZ0 m hmR fun w hw => ?_)
    have hwQ : w ∈ Q := hw.1
    have h1 := LinearMap.congr_fun h0 ⟨M₀.π w, (mem_wsub hS t).mpr (M₀.pi_mem_img hw hwQ)⟩
    rw [delta_apply, LinearMap.zero_apply, dmap_pi hS m hwQ] at h1
    exact (M₀.π_ker _ (hcQ m w hwQ)).mp h1
  · intro hgZ
    obtain ⟨m, hmZ, rfl⟩ := exists_of_mem_bar hgZ
    refine LinearMap.ext fun w => ?_
    obtain ⟨x, hxW, hxQ, hx⟩ := M₀.mem_img.mp ((mem_wsub hS t).mp w.2)
    rw [delta_apply, LinearMap.zero_apply, ← hx, dmap_pi hS m hxQ]
    exact (M₀.π_ker _ (hcQ m x hxQ)).mpr ((hMp G M Q Z B hc n' t hs Z0 hZ0 m hmZ).2 x hxW)

theorem delta_conj (hS : IsTensorSetup hc n M₀ ρ b) {t : G} (ht : t ∈ LB M Q B)
    {h : Mbar M Q} (hh : h ∈ bar M Q (Rt M (LB M Q B) t)) {g : Mbar M Q}
    (hg : g ∈ bar M Q (H0 M Z)) (w : ↥(wsub hS t)) :
    delta hS t (h * g * h⁻¹) (Subgroup.mul_mem _ (Subgroup.mul_mem _ (mem_bar_H0_of_Rt hc hh) hg)
      (Subgroup.inv_mem _ (mem_bar_H0_of_Rt hc hh))) w =
      (ρ h).toAdd (delta hS t g hg ⟨(ρ h⁻¹).toAdd w,
        act_mem_wsub hS ht (Subgroup.inv_mem _ hh) w.2⟩) := by
  rw [delta_apply, delta_apply]
  have hinv : (ρ h).toAdd ((ρ h⁻¹).toAdd (w : M₀.E)) = w := by
    have e : (ρ (h * h⁻¹)).toAdd (w : M₀.E) = (ρ h).toAdd ((ρ h⁻¹).toAdd (w : M₀.E)) := by
      rw [map_mul]
      rfl
    rw [← e, mul_inv_cancel, map_one]
    rfl
  have e3 : ∀ (a c : Mbar M Q) (v : M₀.E), (ρ (a * c)).toAdd v = (ρ a).toAdd ((ρ c).toAdd v) :=
    fun a c v => by
      rw [map_mul]
      rfl
  have e2 : (ρ (h * g * h⁻¹)).toAdd (w : M₀.E) =
      (ρ h).toAdd ((ρ g).toAdd ((ρ h⁻¹).toAdd (w : M₀.E))) := by
    rw [e3, e3]
  simp only [dmap]
  rw [e2, map_sub, hinv]

end Delta

end CFSG.RankThree.GF2n.Stroth80.S714

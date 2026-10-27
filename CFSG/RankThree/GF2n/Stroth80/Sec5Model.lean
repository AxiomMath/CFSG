module

public import CFSG.RankThree.GF2n.Stroth80.Sec5Comm
import CFSG.RankThree.GF2n.Stroth80.Sec34Spure
import CFSG.RankThree.GF2n.Stroth80.InvolutionDim
public import CFSG.RankThree.GF2n.Stroth80.Sec39Rt

public section

namespace CFSG.RankThree.GF2n.Tim79.QuadModel

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}
  {M₀ : QuadModel QF V K γ}

theorem mem_range_sub_one_iff {T : M₀.E →ₗ[K] M₀.E} (hT : ∀ e f, M₀.B (T e) (T f) = M₀.B e f)
    (e : M₀.E) : e ∈ LinearMap.range (T - 1) ↔ ∀ f, T f = f → M₀.B e f = 0 := by
  have fwd : ∀ x f, T f = f → M₀.B ((T - 1) x) f = 0 := by
    intro x f hf
    have h := hT x f
    rw [hf] at h
    rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, LinearMap.sub_apply, h, sub_self]
  have hker : ∀ f, f ∈ LinearMap.ker (T - 1) → T f = f := by
    intro f hf
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hf
    exact hf
  constructor
  · rintro ⟨x, rfl⟩
    exact fwd x
  · intro h
    have hnd : M₀.B.Nondegenerate :=
      ⟨fun x hx => M₀.nondeg x hx, fun y hy => M₀.nondeg y fun f => by
        rw [B_comm, hy f, neg_zero]⟩
    have hle : LinearMap.range (T - 1) ≤ M₀.B.orthogonal (LinearMap.ker (T - 1)) := by
      rintro _ ⟨x, rfl⟩
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro f hf
      rw [B_comm, fwd x f (hker f hf), neg_zero]
    have hdim := LinearMap.BilinForm.finrank_orthogonal hnd (LinearMap.ker (T - 1))
    have hrk := LinearMap.finrank_range_add_finrank_ker (T - 1)
    have heq := Submodule.eq_of_le_of_finrank_eq hle (by omega)
    rw [heq, LinearMap.BilinForm.mem_orthogonal_iff]
    intro f hf
    rw [B_comm, h f (hker f hf), neg_zero]

theorem mem_range_sub_one_iff' {T : M₀.E ≃ₗ[K] M₀.E} (hT : ∀ e f, M₀.B (T e) (T f) = M₀.B e f)
    (e : M₀.E) :
    e ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1) ↔ ∀ f, T f = f → M₀.B e f = 0 :=
  mem_range_sub_one_iff (T := (T : M₀.E →ₗ[K] M₀.E)) hT e

end CFSG.RankThree.GF2n.Tim79.QuadModel

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section Model

variable {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {t : G} {T : M₀.E ≃ₗ[K] M₀.E}

theorem pi_comm_eq_sub (htQ : ∀ x ∈ Q, t * x * t⁻¹ ∈ Q)
    (hTπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = T (M₀.π x)) {x : G} (hx : x ∈ Q) :
    M₀.π ⁅x, t⁆ = M₀.π x - T (M₀.π x) := by
  rw [show ⁅x, t⁆ = x * (t * x⁻¹ * t⁻¹) by rw [commutatorElement_def]; group,
    M₀.π_mul _ hx _ (htQ _ (Q.inv_mem hx)), hTπ _ (Q.inv_mem hx), M₀.pi_inv hx, map_neg,
    sub_eq_add_neg]

theorem comm_mem_iff_fix (htQ : ∀ x ∈ Q, t * x * t⁻¹ ∈ Q)
    (hTπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = T (M₀.π x)) {x : G} (hx : x ∈ Q) :
    ⁅t, x⁆ ∈ Z ↔ T (M₀.π x) = M₀.π x := by
  rw [Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hx (htQ x hx), hTπ x hx]

theorem pi_zpow_conj (htQ : ∀ x ∈ Q, t * x * t⁻¹ ∈ Q) (htQ' : ∀ x ∈ Q, t⁻¹ * x * t ∈ Q)
    (hTπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = T (M₀.π x)) (hT2 : ∀ e, T (T e) = e) (k : ℤ) :
    ∀ y ∈ Q, t ^ k * y * (t ^ k)⁻¹ ∈ Q ∧ (M₀.π (t ^ k * y * (t ^ k)⁻¹) = M₀.π y ∨
      M₀.π (t ^ k * y * (t ^ k)⁻¹) = T (M₀.π y)) := by
  have hTπ' : ∀ x ∈ Q, M₀.π (t⁻¹ * x * t) = T (M₀.π x) := by
    intro x hx
    have h := hTπ _ (htQ' x hx)
    rw [show t * (t⁻¹ * x * t) * t⁻¹ = x by group] at h
    rw [h, hT2]
  induction k using Int.induction_on with
  | zero =>
    intro y hy
    rw [zpow_zero, one_mul, inv_one, mul_one]
    exact ⟨hy, Or.inl rfl⟩
  | succ k ih =>
    intro y hy
    obtain ⟨h1, h2⟩ := ih y hy
    have e : t ^ ((k : ℤ) + 1) * y * (t ^ ((k : ℤ) + 1))⁻¹ =
        t * (t ^ (k : ℤ) * y * (t ^ (k : ℤ))⁻¹) * t⁻¹ := by
      rw [zpow_add_one, mul_inv_rev]
      group
    rw [e, hTπ _ h1]
    refine ⟨htQ _ h1, ?_⟩
    rcases h2 with h | h
    · right
      rw [h]
    · left
      rw [h, hT2]
  | pred k ih =>
    intro y hy
    obtain ⟨h1, h2⟩ := ih y hy
    have e : t ^ (-(k : ℤ) - 1) * y * (t ^ (-(k : ℤ) - 1))⁻¹ =
        t⁻¹ * (t ^ (-(k : ℤ)) * y * (t ^ (-(k : ℤ)))⁻¹) * t := by
      rw [zpow_sub_one, mul_inv_rev, inv_inv]
      group
    rw [e, hTπ' _ h1]
    refine ⟨htQ' _ h1, ?_⟩
    rcases h2 with h | h
    · right
      rw [h]
    · left
      rw [h, hT2]

end Model

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

omit [Finite G] in
theorem comm_mem_Ut {t x : G} (hx : x ∈ Q) : ⁅x, t⁆ ∈ Ut Q Z t :=
  Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers t))

theorem Ctx.Ut_le_Q (hc : Ctx M Q Z B) {t : G} (htM : t ∈ M) : Ut Q Z t ≤ Q :=
  sup_le (comm_zpowers_le_of_conj (hc.conj_mem_Q_of_mem_M htM).1
    (hc.conj_mem_Q_of_mem_M htM).2) hc.Z_le_Q

theorem Ctx.exists_model_LB (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) :
    ∃ (m : ℕ) (γ : G → GaloisField 2 m) (M₀ : Tim79.QuadModel Q Z (GaloisField 2 m) γ)
      (T : M₀.E ≃ₗ[GaloisField 2 m] M₀.E), Tim79.GammaReg Q Z γ ∧
      (∀ x ∈ Q, M₀.π (t * x * t⁻¹) = T (M₀.π x)) ∧ (∀ e f, M₀.B (T e) (T f) = M₀.B e f) ∧
      (∀ e, T (T e) = e) ∧ ∀ x ∈ Q,
        (x ∈ Ut Q Z t ↔ M₀.π x ∈ LinearMap.range ((T : M₀.E →ₗ[GaloisField 2 m] M₀.E) - 1)) := by
  obtain ⟨m, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  have htM : t ∈ M := hc.LB_le_M ht
  obtain ⟨htQ, htQ'⟩ := hc.conj_mem_Q_of_mem_M htM
  obtain ⟨T, hTπ, -, hTB⟩ := h.linear_of_centralizes htM (hc.LB_centralizes_Z ht)
  refine ⟨m, γ, M₀, T, h.reg, hTπ, hTB, fun e => ?_, fun x hx =>
    (M₀.mem_img_iff (le_sup_right : Z ≤ Ut Q Z t) hx).symm.trans
      (mem_img_comm_zpowers_sup_iff M₀ h.reg T htQ htQ' hTπ _)⟩
  obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj e
  rw [← hTπ y hyQ, ← hTπ _ (htQ y hyQ)]
  have e2 : t * (t * y * t⁻¹) * t⁻¹ = t ^ 2 * y * (t ^ 2)⁻¹ := by rw [pow_two]; group
  rw [e2, Tim79.QuadModel.pi_conj_self (M₀ := M₀) (hc.sq_mem_Q_of_mem_LB ht) hyQ]

theorem Ctx.Ut_eq_center_Q1 (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) :
    Ut Q Z t = (Subgroup.center ↥(Q1 hc t)).map (Q1 hc t).subtype := by
  obtain ⟨m, γ, M₀, T, R, hTπ, hTB, hT2, hU⟩ := hc.exists_model_LB ht
  have htM : t ∈ M := hc.LB_le_M ht
  have hQ1 : ∀ x, x ∈ Q1 hc t ↔ x ∈ Q ∧ T (M₀.π x) = M₀.π x := fun x => by
    rw [hc.mem_Q1_iff htM]
    exact and_congr_right fun hx => comm_mem_iff_fix (hc.conj_mem_Q_of_mem_M htM).1 hTπ hx
  show Ut Q Z t = cen (Q1 hc t)
  rw [cen_eq]
  ext x
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx
    have hxQ : x ∈ Q := hc.Ut_le_Q htM hx
    have hxR := (hU x hxQ).mp hx
    have hxF : T (M₀.π x) = M₀.π x := by
      have h := Tim79.QuadModel.range_le_ker_of_sq_eq_one M₀
        (T := (T : M₀.E →ₗ[GaloisField 2 m] M₀.E)) (LinearMap.ext hT2) hxR
      rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h
    refine ⟨(hQ1 x).mpr ⟨hxQ, hxF⟩, fun y hy => ?_⟩
    obtain ⟨hyQ, hyT⟩ := (hQ1 y).mp hy
    exact ((M₀.comm_iff_B R hxQ hyQ).mpr
      ((Tim79.QuadModel.mem_range_sub_one_iff' hTB _).mp hxR _ hyT)).symm
  · rintro ⟨hx1, hxc⟩
    have hxQ : x ∈ Q := ((hQ1 x).mp hx1).1
    refine (hU x hxQ).mpr ((Tim79.QuadModel.mem_range_sub_one_iff' hTB _).mpr fun f hf => ?_)
    obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj f
    exact (M₀.comm_iff_B R hxQ hyQ).mp (hxc y ((hQ1 y).mpr ⟨hyQ, hf⟩)).symm

theorem Ctx.exists_comm_mul_inv_mem_Z (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {u : G}
    (hu : u ∈ Ut Q Z t) : ∃ x ∈ Q, ⁅x, t⁆ * u⁻¹ ∈ Z := by
  obtain ⟨m, γ, M₀, T, -, hTπ, -, -, hU⟩ := hc.exists_model_LB ht
  have htM : t ∈ M := hc.LB_le_M ht
  have huQ : u ∈ Q := hc.Ut_le_Q htM hu
  obtain ⟨w, hw⟩ := (hU u huQ).mp hu
  obtain ⟨x, hxQ, hx⟩ := M₀.π_surj (-w)
  have hcQ : ⁅x, t⁆ ∈ Q := hc.comm_mem_Q htM hxQ
  refine ⟨x, hxQ, (M₀.π_ker _ (Q.mul_mem hcQ (Q.inv_mem huQ))).mp ?_⟩
  rw [M₀.π_mul _ hcQ _ (Q.inv_mem huQ), pi_comm_eq_sub (hc.conj_mem_Q_of_mem_M htM).1 hTπ hxQ,
    hx, M₀.pi_inv huQ, ← hw]
  simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, map_neg]
  abel

theorem Ctx.isChiIso_Q1_Ut (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) :
    IsChiIso Q (Rt M (LB M Q B) t) (Q1 hc t) (Ut Q Z t) Z t := by
  have htM : t ∈ M := hc.LB_le_M ht
  refine ⟨fun x hx => comm_mem_Ut hx, fun u hu => hc.exists_comm_mul_inv_mem_Z ht hu,
    fun x hx y hy => hc.comm_mul_mem_Z htM hx hy, fun x hx => ?_, fun r hr x hx =>
    hc.comm_conj_mem_Z htM (hc.Rt_le_M t hr)
      (hc.Rt_comm_mem_Q ((Rt M (LB M Q B) t).inv_mem hr)) hx⟩
  rw [hc.mem_Q1_iff htM, ← commutatorElement_inv t x, Subgroup.inv_mem_iff]
  exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩

theorem Ctx.comm_mem_Tt_iff (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {V : Subgroup G}
    (hVU : V ≤ Ut Q Z t) {x : G} (hx : x ∈ Q) : ⁅x, t⁆ ∈ Tt Q Z V t ↔ x ∈ Wt Q V := by
  refine ⟨fun hxT => ?_, fun hxW =>
    Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hxW (Subgroup.mem_zpowers t))⟩
  obtain ⟨m, γ, M₀, T, R, hTπ, hTB, hT2, hU⟩ := hc.exists_model_LB ht
  have htM : t ∈ M := hc.LB_le_M ht
  obtain ⟨htQ, htQ'⟩ := hc.conj_mem_Q_of_mem_M htM
  have hVQ : V ≤ Q := hVU.trans (hc.Ut_le_Q htM)
  have hWQ : Wt Q V ≤ Q := inf_le_left
  have hZW : Z ≤ Wt Q V := fun z hz => ⟨hc.Z_le_Q hz,
    Subgroup.mem_centralizer_iff.mpr fun v hv => (hc.hyp.toHyp79.V_central hz (hVQ hv)).symm⟩
  have hFW : ∀ y ∈ Q, T (M₀.π y) = M₀.π y → y ∈ Wt Q V := fun y hy hfix =>
    ⟨hy, Subgroup.mem_centralizer_iff.mpr fun v hv => (M₀.comm_iff_B R (hVQ hv) hy).mpr
      ((Tim79.QuadModel.mem_range_sub_one_iff' hTB _).mp ((hU v (hVQ hv)).mp (hVU hv)) _
        hfix)⟩
  set S : AddSubgroup M₀.E :=
    (M₀.img (Wt Q V)).map ((T : M₀.E →ₗ[GaloisField 2 m] M₀.E) - 1).toAddMonoidHom with hS
  have hTS : Tt Q Z V t ≤ M₀.lift S := by
    refine sup_le (Subgroup.commutator_le.mpr fun w hw s hs => ?_) fun z hz => ?_
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
      have hwQ : w ∈ Q := hWQ hw
      obtain ⟨hq, hor⟩ := pi_zpow_conj htQ htQ' hTπ hT2 k w⁻¹ (Q.inv_mem hwQ)
      rw [show ⁅w, t ^ k⁆ = w * (t ^ k * w⁻¹ * (t ^ k)⁻¹) by rw [commutatorElement_def]; group]
      refine ⟨Q.mul_mem hwQ hq, ?_⟩
      rw [M₀.π_mul _ hwQ _ hq]
      rcases hor with h | h
      · rw [h, M₀.pi_inv hwQ, add_neg_cancel]
        exact S.zero_mem
      · rw [h, M₀.pi_inv hwQ]
        refine AddSubgroup.mem_map.mpr ⟨-M₀.π w, (M₀.img (Wt Q V)).neg_mem
          (M₀.pi_mem_img hw hwQ), ?_⟩
        simp only [LinearMap.toAddMonoidHom_coe, LinearMap.sub_apply, LinearEquiv.coe_coe,
          Module.End.one_apply, map_neg]
        abel
    · refine ⟨R.V_le hz, ?_⟩
      rw [(M₀.π_ker z (R.V_le hz)).mpr hz]
      exact S.zero_mem
  obtain ⟨w, hwW, hw⟩ := AddSubgroup.mem_map.mp (hTS hxT).2
  rw [pi_comm_eq_sub htQ hTπ hx] at hw
  simp only [LinearMap.toAddMonoidHom_coe, LinearMap.sub_apply, LinearEquiv.coe_coe,
    Module.End.one_apply] at hw
  obtain ⟨y, hyQ, hy⟩ := M₀.π_surj (M₀.π x + w)
  have hfix : T (M₀.π y) = M₀.π y := by
    have hTw : T w = w + (M₀.π x - T (M₀.π x)) := by rw [← hw]; abel
    rw [hy, map_add, hTw]
    abel
  have hyW : M₀.π x + w ∈ M₀.img (Wt Q V) := by
    rw [← hy]
    exact M₀.pi_mem_img (hFW y hyQ hfix) hyQ
  have hmem := (M₀.img (Wt Q V)).sub_mem hyW hwW
  rw [add_sub_cancel_right] at hmem
  exact (M₀.mem_img_iff hZW hx).mp hmem

theorem Ctx.isChiIso_Wt_Ut_Tt (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    (hV : Vt M (LB M Q B) B Z t ≤ Tt Q Z (Vt M (LB M Q B) B Z t) t) :
    IsChiIso Q (Rt M (LB M Q B) t) (Wt Q (Vt M (LB M Q B) B Z t)) (Ut Q Z t)
      (Tt Q Z (Vt M (LB M Q B) B Z t) t) t := by
  have hZT : Z ≤ Tt Q Z (Vt M (LB M Q B) B Z t) t := le_sup_right
  have hTU : Tt Q Z (Vt M (LB M Q B) B Z t) t ≤ Ut Q Z t :=
    sup_le_sup_right (Subgroup.commutator_mono inf_le_left le_rfl) Z
  obtain ⟨h1, h2, h3, -, h5⟩ := hc.isChiIso_Q1_Ut ht
  refine ⟨h1, fun u hu => ?_, fun x hx y hy => hZT (h3 x hx y hy),
    fun x hx => hc.comm_mem_Tt_iff ht (hV.trans hTU) hx, fun r hr x hx => hZT (h5 r hr x hx)⟩
  obtain ⟨x, hx, hxu⟩ := h2 u hu
  exact ⟨x, hx, hZT hxu⟩

end CFSG.RankThree.GF2n.Stroth80

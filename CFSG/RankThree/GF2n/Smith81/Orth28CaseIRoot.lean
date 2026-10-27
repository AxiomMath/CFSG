module

public import CFSG.RankThree.GF2n.Smith81.Orth28CaseIBasic

public section

namespace CFSG.RankThree.GF2n.Smith81

open QuadraticMap CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

namespace OrthCaseI

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

section Root

variable [Finite G] {X : Subgroup G} {x : G}

theorem jx_ne_bot_t (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) (hs : Sit M Q Z X x)
    {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)} (hI : InvAct C x !![1, 1; 0, 1] o)
    (hD : Q ⊓ QB X ≠ ⊥) : Jx Q X x ≠ ⊥ := by
  obtain ⟨d, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD
  have hdQ : (d : G) ∈ Q := (Subgroup.mem_inf.mp d.2).1
  have hdB : (d : G) ∈ QB X := (Subgroup.mem_inf.mp d.2).2
  have hdx : (d : G) * x = x * d := (hs.QB_comm_X hs.mem hdB).symm
  have hfix := fixed_of_commute hc C hs hI.act hdQ hdx
  obtain ⟨p', hp'⟩ := (mem_Rsp_iff C _ o).mp (fixed_mem_Rsp_t C o hI.oo hfix)
  have hJ : (d : G) ∈ ⁅Q, Subgroup.zpowers x⁆ := mem_comm_of_range hc C hs hI.act hdQ hp'
  intro hJ0
  have : (d : G) ∈ Jx Q X x := ⟨hJ, hdB⟩
  rw [hJ0, Subgroup.mem_bot] at this
  exact hd1 (Subtype.ext this)

theorem exists_centralizer_lift (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B)
    (hs : Sit M Q Z X x) (hIc : ∀ z' ∈ Z, ∃ q ∈ Q, q⁻¹ * x * q = x * z')
    {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)} (hI : InvAct C x 1 o)
    {s : G} (hsM : s ∈ M) (hsH : s ∈ H0 M Z) {u : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)}
    (hsu : ActsAsTensor Q Z C.M₀ C.φ s 1 u) (hcomm : ∀ v, u (o v) = o (u v))
    (hshift : ∀ y ∈ Q, ⁅x, y⁆ ∈ Z → ⁅x, s * y * s⁻¹⁆ = ⁅x, y⁆) :
    ∃ s₁ : G, s₁ ∈ M ∧ s₁ * x = x * s₁ ∧ ActsAsTensor Q Z C.M₀ C.φ s₁ 1 u := by
  have H := hc.ctx.hyp
  have h12 := smith_1_12 hs
  have hxZ := hs.x_cent h12
  have hx2 := hs.x_sq
  have hxM := hs.memM
  have hZQ : Z ≤ Q := H.Z_normal.1
  have hxQ : ∀ y ∈ Q, x * y * x⁻¹ ∈ Q := (hc.ctx.conj_mem_Q_of_mem_M hxM).1
  have hsQ : ∀ y ∈ Q, s * y * s⁻¹ ∈ Q := (hc.ctx.conj_mem_Q_of_mem_M hsM).1
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hsxA : ActsAsTensor Q Z C.M₀ C.φ (s * x) 1 ⇑(o.trans u) := by
    have h := ActsAsTensor.mul (M₀ := C.M₀) (φ := C.φ) (o := (u : (C.ι → C.K) →ₗ[C.K] _))
      (o' := (o : (C.ι → C.K) →ₗ[C.K] _)) hxQ hsu hI.act
    rw [mul_one] at h
    exact h
  have hxsA : ActsAsTensor Q Z C.M₀ C.φ (x * s) 1 ⇑(o.trans u) := by
    have h := ActsAsTensor.mul (M₀ := C.M₀) (φ := C.φ) (o := (o : (C.ι → C.K) →ₗ[C.K] _))
      (o' := (u : (C.ι → C.K) →ₗ[C.K] _)) hsQ hI.act hsu
    have e : ⇑((o : (C.ι → C.K) →ₗ[C.K] (C.ι → C.K)) ∘ₗ (u : (C.ι → C.K) →ₗ[C.K] (C.ι → C.K))) =
        ⇑(o.trans u) := funext fun v => (hcomm v).symm
    rw [mul_one, e] at h
    exact h
  have he₀ : (x * s)⁻¹ * (s * x) ∈ Q :=
    inv_mul_mem_Q_of_same_act hc.ctx C (M.mul_mem hsM hxM) (M.mul_mem hxM hsM)
      (g := 1) (g' := 1) (mul_one 1) hsxA hxsA
  set ε : G := ((x * s)⁻¹ * (s * x))⁻¹ with hε
  have hεQ : ε ∈ Q := Q.inv_mem he₀
  have hxε : s⁻¹ * x * s = x * ε := by rw [hε]; group
  have hsZ : ∀ z ∈ Z, s⁻¹ * z * s = z := by
    intro z hz
    have h := Subgroup.mem_centralizer_iff.mp hsH.2 z hz
    calc s⁻¹ * z * s = s⁻¹ * (z * s) := by group
      _ = s⁻¹ * (s * z) := by rw [h]
      _ = z := by group
  have hεy : ∀ y ∈ Q, ⁅x, y⁆ ∈ Z → ⁅ε, y⁆ = 1 := by
    intro y hy hxy
    have hy' : s * y * s⁻¹ ∈ Q := hsQ y hy
    have hfixy : orthTensor 1 (⇑o) (C.φ (C.M₀.π y)) = C.φ (C.M₀.π y) :=
      (comm_x_mem_Z_iff hc C hs hI.act hy).mp hxy
    have hfixy' : orthTensor 1 (⇑o) (C.φ (C.M₀.π (s * y * s⁻¹))) =
        C.φ (C.M₀.π (s * y * s⁻¹)) := by
      rw [hsu y hy]
      rw [orthTensor_one_apply] at hfixy
      have f1 : o (C.φ (C.M₀.π y)).1 = (C.φ (C.M₀.π y)).1 := congrArg Prod.fst hfixy
      have f2 : o (C.φ (C.M₀.π y)).2 = (C.φ (C.M₀.π y)).2 := congrArg Prod.snd hfixy
      simp only [orthTensor_one_apply]
      rw [← hcomm, ← hcomm, f1, f2]
    have hxy' : ⁅x, s * y * s⁻¹⁆ ∈ Z := (comm_x_mem_Z_iff hc C hs hI.act hy').mpr hfixy'
    have h1 : ⁅s⁻¹ * x * s, y⁆ = ⁅x, s * y * s⁻¹⁆ := by
      calc ⁅s⁻¹ * x * s, y⁆ = s⁻¹ * ⁅x, s * y * s⁻¹⁆ * s := by
            simp only [commutatorElement_def]; group
        _ = ⁅x, s * y * s⁻¹⁆ := hsZ _ hxy'
    rw [hxε, hshift y hy hxy] at h1
    have hz : ⁅ε, y⁆ ∈ Z := comm_mem_Z H hεQ hy
    have h2 : ⁅x * ε, y⁆ = ⁅ε, y⁆ * ⁅x, y⁆ := by
      calc ⁅x * ε, y⁆ = x * ⁅ε, y⁆ * x⁻¹ * ⁅x, y⁆ := by
            simp only [commutatorElement_def]; group
        _ = ⁅ε, y⁆ * ⁅x, y⁆ := by rw [hxZ _ hz]
    rw [h2] at h1
    exact mul_eq_right.mp h1
  have hnd := polarBilin_nondegenerate_of_hnd C.hF.nondeg
  have hperp : ∀ w : C.ι → C.K, o w = w →
      polar C.qU (C.φ (C.M₀.π ε)).1 w = 0 ∧ polar C.qU (C.φ (C.M₀.π ε)).2 w = 0 := by
    intro w hw
    have key : ∀ y ∈ Q, orthTensor 1 (⇑o) (C.φ (C.M₀.π y)) = C.φ (C.M₀.π y) →
        C.M₀.B (C.M₀.π ε) (C.M₀.π y) = 0 := by
      intro y hy hfix
      have hxy : ⁅x, y⁆ ∈ Z := (comm_x_mem_Z_iff hc C hs hI.act hy).mpr hfix
      exact (GM.comm_eq_one_iff C.hD hεQ hy).mp (hεy y hy hxy)
    obtain ⟨y₀, hy₀Q, hy₀⟩ :=
      exists_mem_phi_pi (M₀ := C.M₀) (φ := C.φ) ((0, w) : (C.ι → C.K) × (C.ι → C.K))
    obtain ⟨y₁, hy₁Q, hy₁⟩ :=
      exists_mem_phi_pi (M₀ := C.M₀) (φ := C.φ) ((w, 0) : (C.ι → C.K) × (C.ι → C.K))
    have k0 := key y₀ hy₀Q (by rw [hy₀, orthTensor_one_apply]; simp [hw])
    have k1 := key y₁ hy₁Q (by rw [hy₁, orthTensor_one_apply]; simp [hw])
    rw [B_phi, hy₀] at k0
    rw [B_phi, hy₁] at k1
    simp only [QuadraticMap.polar_zero_left, QuadraticMap.polar_zero_right, add_zero,
      zero_add] at k0 k1
    exact ⟨k0, by rw [QuadraticMap.polar_comm]; exact k1⟩
  have haP : (C.φ (C.M₀.π ε)).1 ∈ OrthogonalInvolutions.commSpace o :=
    mem_commSpace_of_polar_fix hnd hI.mem_orth hI.mul_self fun w hw => (hperp w hw).1
  have hbP : (C.φ (C.M₀.π ε)).2 ∈ OrthogonalInvolutions.commSpace o :=
    mem_commSpace_of_polar_fix hnd hI.mem_orth hI.mul_self fun w hw => (hperp w hw).2
  have hε'Q : x * ε * x⁻¹ ∈ Q := hxQ ε hεQ
  have hε'φ : C.φ (C.M₀.π (x * ε * x⁻¹)) = C.φ (C.M₀.π ε) := by
    rw [hI.act ε hεQ, orthTensor_one_apply, hI.fix_of_mem_commSpace haP,
      hI.fix_of_mem_commSpace hbP]
  have hε'R : C.φ (C.M₀.π (x * ε * x⁻¹)) ∈ Rsp C 1 o := by
    rw [Rsp_one, hε'φ]
    exact ⟨haP, hbP⟩
  obtain ⟨p', hp'⟩ := (mem_Rsp_iff C 1 o).mp hε'R
  obtain ⟨q₃, hq₃, hz₃, -⟩ := exists_comm_rep hc C hs hI.act hε'Q hp'
  set z₃ : G := ⁅q₃, x⁆⁻¹ * (x * ε * x⁻¹) with hz₃def
  have hz3x : x⁻¹ * z₃ * x = z₃ := by
    have := hxZ z₃ hz₃
    rw [hxinv] at this ⊢
    exact this
  have hcentral : z₃ * q₃⁻¹ = q₃⁻¹ * z₃ := Z_central H hz₃ (Q.inv_mem hq₃)
  have hx_eq : s⁻¹ * x * s = q₃ * (x * z₃) * q₃⁻¹ := by
    have hε'eq : x * ε * x⁻¹ = ⁅q₃, x⁆ * z₃ := by rw [hz₃def]; group
    calc s⁻¹ * x * s = x * ε := hxε
      _ = (x * ε * x⁻¹) * x := by group
      _ = (⁅q₃, x⁆ * z₃) * x := by rw [hε'eq]
      _ = q₃ * x * q₃⁻¹ * (x⁻¹ * z₃ * x) := by simp only [commutatorElement_def]; group
      _ = q₃ * x * q₃⁻¹ * z₃ := by rw [hz3x]
      _ = q₃ * x * (z₃ * q₃⁻¹) := by rw [hcentral]; group
      _ = q₃ * (x * z₃) * q₃⁻¹ := by group
  obtain ⟨q, hq, hqx⟩ := hIc z₃ hz₃
  set q₄ : G := q * q₃⁻¹ with hq₄
  have hq₄Q : q₄ ∈ Q := Q.mul_mem hq (Q.inv_mem hq₃)
  refine ⟨s * q₄⁻¹, M.mul_mem hsM (M.inv_mem (H.Q_normal.1 hq₄Q)), ?_, ?_⟩
  · have h1 : (s * q₄⁻¹)⁻¹ * x * (s * q₄⁻¹) = x := by
      calc (s * q₄⁻¹)⁻¹ * x * (s * q₄⁻¹) = q₄ * (s⁻¹ * x * s) * q₄⁻¹ := by group
        _ = q₄ * (q₃ * (x * z₃) * q₃⁻¹) * q₄⁻¹ := by rw [hx_eq]
        _ = q₄ * (q₃ * (q⁻¹ * x * q) * q₃⁻¹) * q₄⁻¹ := by rw [hqx]
        _ = x := by rw [hq₄]; group
    calc s * q₄⁻¹ * x = (s * q₄⁻¹) * ((s * q₄⁻¹)⁻¹ * x * (s * q₄⁻¹)) := by rw [h1]
      _ = x * (s * q₄⁻¹) := by group
  · have h2 := ActsAsTensor.mul (M₀ := C.M₀) (φ := C.φ) (o := (u : (C.ι → C.K) →ₗ[C.K] _))
      (o' := LinearMap.id)
      (fun y hy => Q.mul_mem (Q.mul_mem (Q.inv_mem hq₄Q) hy) (Q.inv_mem (Q.inv_mem hq₄Q))) hsu
      (ActsAsTensor.of_mem (Q.inv_mem hq₄Q))
    rw [mul_one] at h2
    exact h2

theorem eichler_sub_of_polar_eq_zero {K : Type} [Field K] [CharP K 2] {ι : Type} [Fintype ι]
    {qU : QuadraticForm K (ι → K)} {e w v : ι → K} (hqe : qU e = 0) (hew : polar qU e w = 0)
    (hve : polar qU v e = 0) :
    CFSG.ClassicalGroups.Orthogonal.eichler qU e w v - v = polar qU v w • e := by
  rw [CFSG.ClassicalGroups.Orthogonal.eichler_apply hqe hew v, hve]
  simp only [zero_smul, add_zero, mul_zero]
  rw [sub_eq_add_neg, sub_eq_add_neg, add_comm, ← add_assoc, neg_add_cancel, zero_add,
    OrthogonalInvolutions.neg_vec_eq K]

theorem eichler_pair_sub {C : OrthCtx M Q Z B} {x : G} {g : Matrix (Fin 2) (Fin 2) C.K}
    {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)} (hI : InvAct C x g o) {e w a b : C.ι → C.K}
    (heP : e ∈ OrthogonalInvolutions.commSpace o) (hqe : C.qU e = 0) (hew : polar C.qU e w = 0)
    (ha : o a = a) (hb : o b = b) :
    ((CFSG.ClassicalGroups.Orthogonal.eichler C.qU e w a,
        CFSG.ClassicalGroups.Orthogonal.eichler C.qU e w b) : (C.ι → C.K) × (C.ι → C.K)) - (a, b) =
      (polar C.qU a w • e, polar C.qU b w • e) := by
  have hnd := polarBilin_nondegenerate_of_hnd C.hF.nondeg
  refine Prod.ext ?_ ?_
  · exact eichler_sub_of_polar_eq_zero hqe hew (by
      rw [QuadraticMap.polar_comm]
      exact polar_commSpace_fix hnd hI.mem_orth hI.mul_self heP ha)
  · exact eichler_sub_of_polar_eq_zero hqe hew (by
      rw [QuadraticMap.polar_comm]
      exact polar_commSpace_fix hnd hI.mem_orth hI.mul_self heP hb)

theorem eichler_comm_o {K : Type} [Field K] {ι : Type} [Fintype ι] {qU : QuadraticForm K (ι → K)}
    {o : (ι → K) ≃ₗ[K] (ι → K)} (hO : o ∈ TauCeti.QuadraticMap.orthogonalGroup qU) {e w : ι → K}
    (hoe : o e = e) (hw : o w = w) (v : ι → K) :
    CFSG.ClassicalGroups.Orthogonal.eichler qU e w (o v) =
      o (CFSG.ClassicalGroups.Orthogonal.eichler qU e w v) := by
  have h := CFSG.ClassicalGroups.Orthogonal.eichler_conj hO e w
  rw [hoe, hw] at h
  have := congrArg (fun T : (ι → K) ≃ₗ[K] (ι → K) => T (o v)) h
  simpa using this.symm

theorem eichler_shift (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) (hs : Sit M Q Z X x)
    {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)} (hI : InvAct C x 1 o) {e w : C.ι → C.K}
    (heP : e ∈ OrthogonalInvolutions.commSpace o) (hqe : C.qU e = 0)
    (hew : polar C.qU e w = 0) (hw : o w = w) {s : G} (hsM : s ∈ M)
    (hsact : ActsAsTensor Q Z C.M₀ C.φ s 1 (CFSG.ClassicalGroups.Orthogonal.eichler C.qU e w))
    {y : G} (hy : y ∈ Q) (hxy : ⁅x, y⁆ ∈ Z) : ⁅x, s * y * s⁻¹⁆ = ⁅x, y⁆ := by
  have H := hc.ctx.hyp
  have hsQ : ∀ y ∈ Q, s * y * s⁻¹ ∈ Q := (hc.ctx.conj_mem_Q_of_mem_M hsM).1
  have hfix := (comm_x_mem_Z_iff hc C hs hI.act hy).mp hxy
  rw [orthTensor_one_apply] at hfix
  have fa : o (C.φ (C.M₀.π y)).1 = (C.φ (C.M₀.π y)).1 := congrArg Prod.fst hfix
  have fb : o (C.φ (C.M₀.π y)).2 = (C.φ (C.M₀.π y)).2 := congrArg Prod.snd hfix
  have hy' : s * y * s⁻¹ ∈ Q := hsQ y hy
  set δ : G := (s * y * s⁻¹) * y⁻¹ with hδ
  have hδQ : δ ∈ Q := Q.mul_mem hy' (Q.inv_mem hy)
  have hδφ : C.φ (C.M₀.π δ) =
      (polar C.qU (C.φ (C.M₀.π y)).1 w • e, polar C.qU (C.φ (C.M₀.π y)).2 w • e) := by
    rw [hδ, C.M₀.π_mul _ hy' _ (Q.inv_mem hy), Tim79.QuadModel.pi_inv C.M₀ hy, map_add, map_neg,
      hsact y hy, orthTensor_one_apply, ← sub_eq_add_neg]
    exact eichler_pair_sub hI heP hqe hew fa fb
  have hδ1 : ⁅x, δ⁆ = 1 := comm_one_of_mem_P hc C hs hI hδQ
    (by rw [hδφ]; exact Submodule.smul_mem _ _ heP)
    (by rw [hδφ]; exact Submodule.smul_mem _ _ heP)
  have hcent : δ * ⁅x, y⁆ * δ⁻¹ = ⁅x, y⁆ := by
    rw [← Z_central H hxy hδQ]
    group
  calc ⁅x, s * y * s⁻¹⁆ = ⁅x, δ * y⁆ := by rw [hδ]; group
    _ = ⁅x, δ⁆ * (δ * ⁅x, y⁆ * δ⁻¹) := by simp only [commutatorElement_def]; group
    _ = ⁅x, y⁆ := by rw [hδ1, hcent, one_mul]

theorem eichler_step (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) (hs : Sit M Q Z X x)
    (hIc : ∀ z' ∈ Z, ∃ q ∈ Q, q⁻¹ * x * q = x * z')
    {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)} (hI : InvAct C x 1 o) (hJ : Jx Q X x = ⊥)
    {e : C.ι → C.K} (heP : e ∈ OrthogonalInvolutions.commSpace o) (he0 : e ≠ 0)
    (hqe : C.qU e = 0) {d : G} (hd : d ∈ Q ⊓ QB X) {w : C.ι → C.K} (hw : o w = w) :
    polar C.qU (C.φ (C.M₀.π d)).1 w = 0 ∧ polar C.qU (C.φ (C.M₀.π d)).2 w = 0 := by
  have hnd := polarBilin_nondegenerate_of_hnd C.hF.nondeg
  have hdQ : d ∈ Q := hd.1
  have hdfix := fixed_of_commute hc C hs hI.act hdQ (hs.QB_comm_X hs.mem hd.2).symm
  rw [orthTensor_one_apply] at hdfix
  have hfa : o (C.φ (C.M₀.π d)).1 = (C.φ (C.M₀.π d)).1 := congrArg Prod.fst hdfix
  have hfb : o (C.φ (C.M₀.π d)).2 = (C.φ (C.M₀.π d)).2 := congrArg Prod.snd hdfix
  have hew : polar C.qU e w = 0 := polar_commSpace_fix hnd hI.mem_orth hI.mul_self heP hw
  obtain ⟨s, hsL, hsact⟩ := C.hA.eich e w hqe hew
  have hsM : s ∈ M := Lgen_le hc.ctx.LB_le_M hsL
  have hsH : s ∈ H0 M Z := Lgen_le_H0 hc.ctx hsL
  have hcomm : ∀ v, CFSG.ClassicalGroups.Orthogonal.eichler C.qU e w (o v) =
      o (CFSG.ClassicalGroups.Orthogonal.eichler C.qU e w v) :=
    eichler_comm_o hI.mem_orth (hI.fix_of_mem_commSpace heP) hw
  obtain ⟨s₁, hs₁M, hs₁x, hs₁act⟩ := exists_centralizer_lift hc C hs hIc hI hsM hsH hsact hcomm
    (fun y hy hxy => eichler_shift hc C hs hI heP hqe hew hw hsM hsact hy hxy)
  have hs₁N : ∀ y ∈ Q ⊓ QB X, s₁ * y * s₁⁻¹ ∈ Q ⊓ QB X := by
    intro y hy
    have hk : s₁ ∈ Subgroup.normalizer (X : Set G) :=
      Tim77.mem_normalizer_of_commute_of_isTI hs.X_isTI hs.mem hs.ne_one hs₁x
    exact ⟨(hc.ctx.conj_mem_Q_of_mem_M hs₁M).1 y hy.1, hs.normalizer_QB hk hy.2⟩
  set d' : G := (s₁ * d * s₁⁻¹) * d⁻¹ with hd'
  have hd'D : d' ∈ Q ⊓ QB X := (Q ⊓ QB X).mul_mem (hs₁N _ hd) ((Q ⊓ QB X).inv_mem hd)
  have hd'φ : C.φ (C.M₀.π d') =
      (polar C.qU (C.φ (C.M₀.π d)).1 w • e, polar C.qU (C.φ (C.M₀.π d)).2 w • e) := by
    rw [hd', C.M₀.π_mul _ (hs₁N _ hd).1 _ (Q.inv_mem hdQ), Tim79.QuadModel.pi_inv C.M₀ hdQ,
      map_add, map_neg, hs₁act d hdQ, orthTensor_one_apply, ← sub_eq_add_neg]
    exact eichler_pair_sub hI heP hqe hew hfa hfb
  have hd'R : C.φ (C.M₀.π d') ∈ Rsp C 1 o := by
    rw [Rsp_one, hd'φ]
    exact ⟨Submodule.smul_mem _ _ heP, Submodule.smul_mem _ _ heP⟩
  obtain ⟨p', hp'⟩ := (mem_Rsp_iff C 1 o).mp hd'R
  have hd'J : d' ∈ ⁅Q, Subgroup.zpowers x⁆ := mem_comm_of_range hc C hs hI.act hd'D.1 hp'
  have hd'1 : d' = 1 := by
    have : d' ∈ Jx Q X x := ⟨hd'J, hd'D.2⟩
    rw [hJ, Subgroup.mem_bot] at this
    exact this
  rw [hd'1, Tim79.QuadModel.pi_one, map_zero] at hd'φ
  have h0 := Prod.ext_iff.mp hd'φ.symm
  simp only [Prod.fst_zero, Prod.snd_zero] at h0
  exact ⟨(smul_eq_zero.mp h0.1).resolve_right he0, (smul_eq_zero.mp h0.2).resolve_right he0⟩

theorem jx_ne_bot_one (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) (hs : Sit M Q Z X x)
    (hIc : ∀ z' ∈ Z, ∃ q ∈ Q, q⁻¹ * x * q = x * z')
    {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)} (hI : InvAct C x 1 o) (hD : Q ⊓ QB X ≠ ⊥) :
    Jx Q X x ≠ ⊥ := by
  intro hJ
  have hnd := polarBilin_nondegenerate_of_hnd C.hF.nondeg
  have ho1 : o ≠ 1 := by
    intro h1
    refine hs.notQ (mem_Q_of_pi_conj_eq (M₀ := C.M₀) hc.ctx.hyp hs.memM fun y hy => ?_)
    apply C.φ.injective
    rw [hI.act y hy, h1, orthTensor_one_apply]
    rfl
  have hrk : 2 ≤ Module.finrank C.K (OrthogonalInvolutions.commSpace o) := by
    have h1 := OrthogonalInvolutions.one_le_finrank_commSpace ho1
    obtain ⟨r, hr⟩ := hI.even
    omega
  obtain ⟨e, heP, he0, hqe⟩ :=
    OrthEps.exists_singular_mem_commSpace hI.mem_orth hI.mul_self hrk
  obtain ⟨d, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD
  have hclaim := fun w hw => eichler_step hc C hs hIc hI hJ heP he0 hqe d.2 (w := w) hw
  have haP : (C.φ (C.M₀.π d)).1 ∈ OrthogonalInvolutions.commSpace o :=
    mem_commSpace_of_polar_fix hnd hI.mem_orth hI.mul_self fun w hw => (hclaim w hw).1
  have hbP : (C.φ (C.M₀.π d)).2 ∈ OrthogonalInvolutions.commSpace o :=
    mem_commSpace_of_polar_fix hnd hI.mem_orth hI.mul_self fun w hw => (hclaim w hw).2
  have hdR : C.φ (C.M₀.π d) ∈ Rsp C 1 o := by
    rw [Rsp_one]
    exact ⟨haP, hbP⟩
  obtain ⟨p', hp'⟩ := (mem_Rsp_iff C 1 o).mp hdR
  have hdJ : (d : G) ∈ ⁅Q, Subgroup.zpowers x⁆ :=
    mem_comm_of_range hc C hs hI.act (Subgroup.mem_inf.mp d.2).1 hp'
  have : (d : G) ∈ Jx Q X x := ⟨hdJ, (Subgroup.mem_inf.mp d.2).2⟩
  rw [hJ, Subgroup.mem_bot] at this
  exact hd1 (Subtype.ext this)

end Root

end OrthCaseI

open OrthCaseI

theorem orthCaseIRoot_of (h24 : Smith24ActStatement)
    (hT : OrthTacitStatement) : OrthCaseIRootStatement := by
  intro G _ _ M Q Z B hc X x hs hxL hI hD
  obtain ⟨C⟩ := exists_orthCtx h24 hc
  have hno := noA2_of_tacit hT hc
  have hJ : Jx Q X x ≠ ⊥ := by
    obtain ⟨o, h | ⟨h, hdet, h'⟩⟩ := normal_form hc hno C hxL hs.x_sq
    · exact jx_ne_bot_one hc C hs hI h hD
    · exact jx_ne_bot_t hc (C.change h hdet) hs h' hD
  have hfus : ∀ z ∈ Z, IsConj x (x * z) := fun z hz => by
    obtain ⟨q, -, hqx⟩ := hI z hz
    exact isConj_iff.mpr ⟨q⁻¹, by simpa using hqx⟩
  obtain ⟨v, hxv, hvQ, hvB⟩ := smith28_of_fused hs hJ hfus
  refine ⟨v, ?_, hxv, hvQ, hvB⟩
  intro hv1
  rw [hv1] at hxv
  exact hs.ne_one (isConj_one_left.mp hxv)

end CFSG.RankThree.GF2n.Smith81

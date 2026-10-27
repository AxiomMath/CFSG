module

public import CFSG.RankThree.GF2n.Smith81.Orth28CaseIBasic

public section

namespace CFSG.RankThree.GF2n.Smith81

open QuadraticMap CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

namespace OrthCaseI

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

section Obeta

variable {K : Type} [Field K] [CharP K 2] {ι : Type} [Fintype ι]
  {qU : QuadraticForm K (ι → K)} {o : (ι → K) ≃ₗ[K] (ι → K)}

@[expose] def oBeta (o : (ι → K) ≃ₗ[K] (ι → K)) (β : K) (v : ι → K) : ι → K :=
  v + β • (o v - v)

theorem oBeta_oBeta (hoo : ∀ v, o (o v) = v) (β : K) (v : ι → K) :
    oBeta o β (oBeta o β v) = v := by
  have h2N : (2 : K) • (o v - v) = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
  simp only [oBeta, map_add, map_smul, map_sub, hoo]
  linear_combination (norm := module) (β - β * β) • h2N

theorem polar_oBeta (hO : o ∈ TauCeti.QuadraticMap.orthogonalGroup qU) (hoo : o * o = 1)
    (β : K) (u v : ι → K) : polar qU (oBeta o β u) v = polar qU u (oBeta o β v) := by
  have h := OrthogonalInvolutions.polar_sub_eq_polar_sub hO hoo u v
  simp only [oBeta, polar_add_left, polar_add_right, polar_smul_left, polar_smul_right,
    smul_eq_mul]
  rw [h]

end Obeta

section PBotOne

variable [Finite G] {X : Subgroup G} {x : G}

theorem even_card_of_cfg (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) :
    Even (Fintype.card C.ι) := by
  obtain ⟨n, hw', hev, -⟩ := hc.orth.exists_width
  have hZ : 2 ≤ Nat.card Z := by have := hc.ctx.hyp.q4; omega
  rw [width_eq_of_width hZ (width_of_tensor C.hD C.φ) hw']
  exact hev

theorem exists_ne_one_mem_Z (H : StrothHyp M Q Z) : ∃ z ∈ Z, z ≠ 1 := by
  have hZne : Z ≠ ⊥ := by
    intro h
    have h4 := H.q4
    rw [h, Subgroup.card_bot] at h4
    omega
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  exact ⟨z, z.2, fun h => hz1 (Subtype.ext h)⟩

theorem pbot_one (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) (hs : Sit M Q Z X x)
    (hIc : ∀ z' ∈ Z, ∃ q ∈ Q, q⁻¹ * x * q = x * z')
    {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)} (hI : InvAct C x 1 o) (hD : Q ⊓ QB X = ⊥) : False := by
  have H := hc.ctx.hyp
  have h12 := smith_1_12 hs
  have hxZ := hs.x_cent h12
  have hq2 : 2 ≤ Nat.card Z := by have := H.q4; omega
  have hw : Width Q Z (Fintype.card C.ι) := width_of_tensor C.hD C.φ
  have hdim : HasDim Q Z (Fintype.card C.ι) x :=
    hasDim_of_even hs hw (even_card_of_cfg hc C) hD
  have h1 : Nat.card ↥(⁅Q, Subgroup.zpowers x⁆ ⊔ Z) = Nat.card Z * Nat.card ↥(Rsp C 1 o) := by
    rw [comm_sup_eq_preimSub hc C hs hI.act]
    exact card_preimSub C hc _
  have hRcard : Nat.card ↥(Rsp C 1 o) = Nat.card Z ^ (Fintype.card C.ι) := by
    have h := hdim
    unfold HasDim at h
    rw [h1, pow_succ'] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  have hfr : Module.finrank C.K ↥(Rsp C 1 o) = Fintype.card C.ι := by
    have h := Module.natCard_eq_pow_finrank (K := C.K) (V := ↥(Rsp C 1 o))
    rw [C.hD.card, hRcard] at h
    exact (Nat.pow_right_injective hq2 h).symm
  have hfr2 : 2 * Module.finrank C.K ↥(OrthogonalInvolutions.commSpace o) = Fintype.card C.ι := by
    rw [← hfr]
    exact (finrank_range_one (o : (C.ι → C.K) →ₗ[C.K] (C.ι → C.K))).symm
  have hsum := OrthogonalInvolutions.finrank_commSpace_add_finrank_fixSpace o
  rw [Module.finrank_fintype_fun_eq_card] at hsum
  have hfixeq : OrthogonalInvolutions.commSpace o = OrthogonalInvolutions.fixSpace o :=
    Submodule.eq_of_le_of_finrank_eq (OrthogonalInvolutions.commSpace_le_fixSpace hI.mul_self)
      (by omega)
  obtain ⟨w, hwZ, hw1⟩ := exists_ne_one_mem_Z H
  obtain ⟨y, hyQ, hxy⟩ := exists_comm_of_hI hxZ hIc w hwZ
  have hfix := (comm_x_mem_Z_iff hc C hs hI.act hyQ).mp (hxy ▸ hwZ)
  rw [orthTensor_one_apply] at hfix
  have fa : o (C.φ (C.M₀.π y)).1 = (C.φ (C.M₀.π y)).1 := congrArg Prod.fst hfix
  have fb : o (C.φ (C.M₀.π y)).2 = (C.φ (C.M₀.π y)).2 := congrArg Prod.snd hfix
  have h0 := comm_one_of_mem_P hc C hs hI hyQ
    (by rw [hfixeq]; exact OrthogonalInvolutions.mem_fixSpace.mpr fa)
    (by rw [hfixeq]; exact OrthogonalInvolutions.mem_fixSpace.mpr fb)
  exact hw1 (hxy ▸ h0)

end PBotOne

section PBotT

variable [Finite G] {X : Subgroup G} {x : G}

@[expose] def TensorFactor (C : OrthCtx M Q Z B) (l : G) : Prop :=
  ∃ (g : Matrix (Fin 2) (Fin 2) C.K) (p : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)) (ρ : C.K),
    g.det ≠ 0 ∧ ρ ≠ 0 ∧ (∀ v, C.qU (p v) = ρ * C.qU v) ∧ ActsAsTensor Q Z C.M₀ C.φ l g p

theorem exists_not_typeA (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) (hs : Sit M Q Z X x)
    (hIc : ∀ z' ∈ Z, ∃ q ∈ Q, q⁻¹ * x * q = x * z')
    {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)} (hI : InvAct C x !![1, 1; 0, 1] o) :
    ∃ a, C.qU (o a - a) ≠ 0 := by
  have H := hc.ctx.hyp
  have hxZ := hs.x_cent (smith_1_12 hs)
  obtain ⟨w, hwZ, hw1⟩ := exists_ne_one_mem_Z H
  obtain ⟨y, hyQ, hxy⟩ := exists_comm_of_hI hxZ hIc w hwZ
  have hfix := (comm_x_mem_Z_iff hc C hs hI.act hyQ).mp (by rw [hxy]; exact hwZ)
  obtain ⟨-, hγ⟩ := theta_fixed_t hc C hs hI hyQ hfix
  refine ⟨(C.φ (C.M₀.π y)).1, fun h0 => hw1 ?_⟩
  rw [h0, hxy] at hγ
  exact C.hD.reg.inj w hwZ hγ

theorem exists_kx_over (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) (hs : Sit M Q Z X x)
    {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)} (hI : InvAct C x !![1, 1; 0, 1] o)
    {a : C.ι → C.K} (ha : C.qU (o a - a) = 0) :
    ∃ y ∈ Q, ⁅x, y⁆ = 1 ∧ C.φ (C.M₀.π y) = (a, o a - a) := by
  obtain ⟨y, hyQ, hy⟩ :=
    exists_mem_phi_pi (M₀ := C.M₀) (φ := C.φ) ((a, o a - a) : (C.ι → C.K) × (C.ι → C.K))
  have hfix : orthTensor !![1, 1; 0, 1] (⇑o) (C.φ (C.M₀.π y)) = C.φ (C.M₀.π y) := by
    rw [hy, orthTensor_t_apply]
    simp only [map_sub, hI.oo]
    refine Prod.ext ?_ ?_
    · simp only
      abel
    · simp only [OrthogonalInvolutions.sub_eq_add_vec C.K, add_comm]
  obtain ⟨hZ, hγ⟩ := theta_fixed_t hc C hs hI hyQ hfix
  rw [hy] at hγ
  simp only at hγ
  rw [ha] at hγ
  exact ⟨y, hyQ, C.hD.reg.inj _ hZ hγ, hy⟩

theorem rep_of_mem_Lx (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) (hs : Sit M Q Z X x)
    {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)} (hI : InvAct C x !![1, 1; 0, 1] o)
    (hD : Q ⊓ QB X = ⊥) {p₀ a₀ : C.ι → C.K} (hp0 : p₀ ≠ 0)
    (hqp0 : C.qU p₀ = 0) (hap : o a₀ - a₀ = p₀) (hpfix : o p₀ = p₀) {l : G} (hl : l ∈ Lx M X)
    (hfac : TensorFactor C l) :
    ∃ (β ρ' : C.K) (p' : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)),
      ActsAsTensor Q Z C.M₀ C.φ l !![1, β; 0, 1] p' ∧
      (∀ u v, polar C.qU (p' u) (p' v) = ρ' * polar C.qU u v) ∧
      ∀ a, C.qU (o a - a) = 0 → p' a = oBeta o β a := by
  have H := hc.ctx.hyp
  have h12 := smith_1_12 hs
  have hw : Width Q Z (Fintype.card C.ι) := width_of_tensor C.hD C.φ
  have hKL := (smith115Statement_holds G M Q Z X x hs _ hw hD).2.1
  obtain ⟨h, p, ρ, hdet, hρ, hq, hactl⟩ := hfac
  have hΛ : ∀ a, C.qU (o a - a) = 0 → orthTensor h p (a, o a - a) = (a, o a - a) := by
    intro a ha
    obtain ⟨y, hyQ, hy1, hyφ⟩ := exists_kx_over hc C hs hI ha
    have hyK : y ∈ Kx Q X := by
      rw [Kx_eq hs h12]
      exact ⟨hyQ, Subgroup.mem_centralizer_singleton_iff.mpr
        (commutatorElement_eq_one_iff_mul_comm.mp hy1).symm⟩
    have hyl : l * y * l⁻¹ = y := by
      calc l * y * l⁻¹ = y * l * l⁻¹ := by rw [← hKL y hyK l hl]
        _ = y := by group
    rw [← hyφ, ← hactl y hyQ, hyl]
  have hp0' : p p₀ ≠ 0 := fun h0 => hp0 (p.map_eq_zero_iff.mp h0)
  have hqp0' : C.qU (o p₀ - p₀) = 0 := by rw [hpfix, sub_self, QuadraticMap.map_zero]
  have e1 := hΛ p₀ hqp0'
  rw [hpfix, sub_self] at e1
  simp only [orthTensor, map_zero, smul_zero, add_zero] at e1
  obtain ⟨e1a, e1b⟩ := Prod.mk.inj e1
  have hqa₀ : C.qU (o a₀ - a₀) = 0 := by rw [hap]; exact hqp0
  have e2 := hΛ a₀ hqa₀
  rw [hap] at e2
  simp only [orthTensor] at e2
  obtain ⟨e2a, e2b⟩ := Prod.mk.inj e2
  have h10 : h 1 0 = 0 := (smul_eq_zero.mp e1b).resolve_right hp0'
  have h11 : h 1 1 • p p₀ = p₀ := by
    rw [h10, zero_smul, zero_add] at e2b
    exact e2b
  have h00 : h 0 0 = h 1 1 := by
    have : (h 0 0 - h 1 1) • p p₀ = 0 := by rw [sub_smul, e1a, h11, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hp0')
  have hα : h 0 0 ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at e1a
    exact hp0 e1a.symm
  set α : C.K := h 0 0 with hαdef
  let p' : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K) :=
    p.trans (LinearEquiv.smulOfNeZero C.K (C.ι → C.K) α hα)
  have hp'app : ∀ v, p' v = α • p v := fun v => rfl
  refine ⟨h 0 1 / α, α * α * ρ, p', ?_, ?_, ?_⟩
  · intro y hy
    rw [hactl y hy]
    refine Prod.ext ?_ ?_
    · simp only [orthTensor, hp'app, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, one_smul]
      rw [smul_smul, div_mul_cancel₀ _ hα]
    · simp only [orthTensor, hp'app, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, one_smul, zero_smul,
        zero_add]
      rw [h10, zero_smul, zero_add, ← h00]
  · intro u v
    have hpq : polar C.qU (p u) (p v) = ρ * polar C.qU u v := by
      simp only [QuadraticMap.polar, ← map_add, hq]
      ring
    rw [hp'app, hp'app, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hpq]
    simp only [smul_eq_mul]
    ring
  · intro a ha
    have e := hΛ a ha
    simp only [orthTensor] at e
    obtain ⟨ea, eb⟩ := Prod.mk.inj e
    rw [h10, zero_smul, zero_add, ← h00] at eb
    have hpN : p (o a - a) = α⁻¹ • (o a - a) := by
      have := congrArg (fun w => α⁻¹ • w) eb
      simpa [smul_smul, inv_mul_cancel₀ hα] using this
    rw [hpN] at ea
    have h2N : (2 : C.K) • (o a - a) = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
    rw [hp'app]
    unfold oBeta
    linear_combination (norm := module) ea - (h 0 1 / α) • h2N

theorem transv_mul_self {K : Type} [Field K] [CharP K 2] (β : K) :
    (!![1, β; 0, 1] : Matrix (Fin 2) (Fin 2) K) * !![1, β; 0, 1] = 1 := by
  have h : β + β = 0 := CharTwo.add_self_eq_zero β
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h]

theorem card_le_sq_of_tensorFactor (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B)
    (hs : Sit M Q Z X x) (hIc : ∀ z' ∈ Z, ∃ q ∈ Q, q⁻¹ * x * q = x * z')
    {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)} (hI : InvAct C x !![1, 1; 0, 1] o)
    (hD : Q ⊓ QB X = ⊥) {S : Subgroup G} (hS : S ≤ Lx M X) (hfac : ∀ l ∈ S, TensorFactor C l) :
    Nat.card ↥S ≤ Nat.card C.K ^ 2 := by
  have H := hc.ctx.hyp
  have hnd := polarBilin_nondegenerate_of_hnd C.hF.nondeg
  have hn4 : 4 ≤ Fintype.card C.ι := four_le_card_of_cfg hc C
  obtain ⟨a₁, ha₁⟩ := exists_not_typeA hc C hs hIc hI
  have ho1 : o ≠ 1 := fun h => ha₁ (by rw [h]; simp)
  have hrk : 2 ≤ Module.finrank C.K (OrthogonalInvolutions.commSpace o) := by
    have h1 := OrthogonalInvolutions.one_le_finrank_commSpace ho1
    obtain ⟨r, hr⟩ := hI.even
    omega
  obtain ⟨p₀, hp₀P, hp00, hqp0⟩ :=
    OrthEps.exists_singular_mem_commSpace hI.mem_orth hI.mul_self hrk
  obtain ⟨a₀, ha₀⟩ := OrthogonalInvolutions.mem_commSpace.mp hp₀P
  have hpfix : o p₀ = p₀ := hI.fix_of_mem_commSpace hp₀P
  obtain ⟨ℓ, hℓ⟩ := OrthEps.exists_linear_sq (K := C.K) (V := C.ι → C.K)
    (fun v => C.qU (o v - v)) (OrthEps.map_sub_add_apply hI.mem_orth hI.mul_self)
    OrthEps.map_sub_smul_apply
  have hmemH : ∀ a, a ∈ LinearMap.ker ℓ ↔ C.qU (o a - a) = 0 := fun a => by
    rw [LinearMap.mem_ker, ← hℓ a]
    exact ⟨fun h => by rw [h]; ring, fun h => (pow_eq_zero_iff two_ne_zero).mp h⟩
  have hℓa₁ : ℓ a₁ ≠ 0 := fun h => ha₁ (by rw [← hℓ a₁, h]; ring)
  have ha₁H : a₁ ∉ LinearMap.ker ℓ := fun h => hℓa₁ (LinearMap.mem_ker.mp h)
  have hdimH : Module.finrank C.K (LinearMap.ker ℓ) + 1 = Fintype.card C.ι := by
    have h1 := OrthEps.finrank_le_finrank_ker_add_one ℓ
    have h2 : Module.finrank C.K (LinearMap.ker ℓ) < Module.finrank C.K (C.ι → C.K) := by
      refine Submodule.finrank_lt (fun h => ha₁H ?_)
      rw [h]
      exact Submodule.mem_top
    rw [Module.finrank_fintype_fun_eq_card] at h1 h2
    omega
  have horth : Module.finrank C.K ↥(LinearMap.BilinForm.orthogonal C.qU.polarBilin
      (LinearMap.ker ℓ)) = 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hnd, Module.finrank_fintype_fun_eq_card]
    omega
  have hrep : ∀ l : ↥S, ∃ (β ρ' : C.K) (p' : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)),
      ActsAsTensor Q Z C.M₀ C.φ (l : G) !![1, β; 0, 1] p' ∧
      (∀ u v, polar C.qU (p' u) (p' v) = ρ' * polar C.qU u v) ∧
      ∀ a, C.qU (o a - a) = 0 → p' a = oBeta o β a :=
    fun l => rep_of_mem_Lx hc C hs hI hD hp00 hqp0 ha₀ hpfix (hS l.2) (hfac l l.2)
  choose β ρ' p' hact hpol hpa using hrep
  have hHnot : ∃ h ∈ LinearMap.ker ℓ, ∃ h' ∈ LinearMap.ker ℓ, polar C.qU h h' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hle : LinearMap.ker ℓ ≤
        LinearMap.BilinForm.orthogonal C.qU.polarBilin (LinearMap.ker ℓ) := by
      intro h hh
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro h' hh'
      simpa [LinearMap.BilinForm.IsOrtho, QuadraticMap.polarBilin_apply_apply] using
        hcon h' hh' h hh
    have := Submodule.finrank_mono hle
    omega
  have hρ1 : ∀ l, ρ' l = 1 := by
    intro l
    obtain ⟨h, hh, h', hh', hne⟩ := hHnot
    have e := hpol l h h'
    rw [hpa l h ((hmemH h).mp hh), hpa l h' ((hmemH h').mp hh'),
      polar_oBeta hI.mem_orth hI.mul_self, oBeta_oBeta hI.oo] at e
    have : (ρ' l - 1) * polar C.qU h h' = 0 := by linear_combination -e
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hne)
  have hperp : ∀ l : ↥S, oBeta o (β l) (p' l a₁) - a₁ ∈
      LinearMap.BilinForm.orthogonal C.qU.polarBilin (LinearMap.ker ℓ) := by
    intro l
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro h hh
    have hh' := (hmemH h).mp hh
    have e1 : polar C.qU (oBeta o (β l) (p' l a₁)) h = polar C.qU a₁ h := by
      rw [polar_oBeta hI.mem_orth hI.mul_self, ← hpa l h hh', hpol, hρ1, one_mul]
    simp only [LinearMap.BilinForm.IsOrtho, QuadraticMap.polarBilin_apply_apply]
    rw [QuadraticMap.polar_comm, QuadraticMap.polar_sub_left, e1, sub_self]
  let Ψ : ↥S → C.K × ↥(LinearMap.BilinForm.orthogonal C.qU.polarBilin
      (LinearMap.ker ℓ)) := fun l => (β l, ⟨_, hperp l⟩)
  have hinj : Function.Injective Ψ := by
    intro l l' hll
    obtain ⟨hβ, hκ⟩ := Prod.mk.inj hll
    have hκ' : oBeta o (β l) (p' l a₁) - a₁ = oBeta o (β l') (p' l' a₁) - a₁ :=
      congrArg Subtype.val hκ
    rw [← hβ] at hκ'
    have h1 : oBeta o (β l) (p' l a₁) = oBeta o (β l) (p' l' a₁) := sub_left_injective hκ'
    have h2 : p' l a₁ = p' l' a₁ := by
      have := congrArg (oBeta o (β l)) h1
      rwa [oBeta_oBeta hI.oo, oBeta_oBeta hI.oo] at this
    have hpp : p' l = p' l' := by
      refine LinearEquiv.ext fun v => ?_
      have hvH : v - (ℓ v / ℓ a₁) • a₁ ∈ LinearMap.ker ℓ := by
        rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hℓa₁, sub_self]
      have e1 := hpa l _ ((hmemH _).mp hvH)
      have e2 := hpa l' _ ((hmemH _).mp hvH)
      rw [← hβ] at e2
      calc p' l v = p' l (v - (ℓ v / ℓ a₁) • a₁) + (ℓ v / ℓ a₁) • p' l a₁ := by
            rw [map_sub, map_smul]; abel
        _ = p' l' (v - (ℓ v / ℓ a₁) • a₁) + (ℓ v / ℓ a₁) • p' l' a₁ := by rw [e1, e2, h2]
        _ = p' l' v := by rw [map_sub, map_smul]; abel
    have hact' : ActsAsTensor Q Z C.M₀ C.φ (l' : G) !![1, β l; 0, 1] (p' l) := by
      have := hact l'
      rw [← hβ, ← hpp] at this
      exact this
    have h12 := smith_1_12 hs
    have hmemQ : (l : G)⁻¹ * l' ∈ Q := inv_mul_mem_Q_of_same_act hc.ctx C
      (Lx_le_H0 hs h12 (hS l'.2)).1 (Lx_le_H0 hs h12 (hS l.2)).1 (g := !![1, β l; 0, 1])
      (g' := !![1, β l; 0, 1]) (transv_mul_self (β l)) hact' (hact l)
    have hmemB : (l : G)⁻¹ * l' ∈ QB X := (QB X).mul_mem
      ((QB X).inv_mem (Subgroup.mem_inf.mp (hS l.2)).1) (Subgroup.mem_inf.mp (hS l'.2)).1
    have hD' : (l : G)⁻¹ * l' ∈ Q ⊓ QB X := ⟨hmemQ, hmemB⟩
    rw [hD, Subgroup.mem_bot, inv_mul_eq_one] at hD'
    exact Subtype.ext hD'
  have hcard := Nat.card_le_card_of_injective Ψ hinj
  rw [Nat.card_prod, Module.natCard_eq_pow_finrank (K := C.K)
    (V := ↥(LinearMap.BilinForm.orthogonal C.qU.polarBilin (LinearMap.ker ℓ))), horth,
    pow_one] at hcard
  calc Nat.card ↥S ≤ Nat.card C.K * Nat.card C.K := hcard
    _ = Nat.card C.K ^ 2 := by ring

theorem pbot_t (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) (hs : Sit M Q Z X x)
    (hIc : ∀ z' ∈ Z, ∃ q ∈ Q, q⁻¹ * x * q = x * z')
    {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)} (hI : InvAct C x !![1, 1; 0, 1] o)
    (hD : Q ⊓ QB X = ⊥) (hsim : OrthSim C) : False := by
  have H := hc.ctx.hyp
  have hw : Width Q Z (Fintype.card C.ι) := width_of_tensor C.hD C.φ
  have hn4 : 4 ≤ Fintype.card C.ι := four_le_card_of_cfg hc C
  have hcard := card_le_sq_of_tensorFactor hc C hs hIc hI hD (le_refl (Lx M X))
    (fun l hl => hsim l (Lx_le_H0 hs (smith_1_12 hs) hl))
  have hLge := Sit.card_Lx_ge hs hw
  rw [← C.hD.card] at hLge
  have hq : 2 ≤ Nat.card C.K := by
    rw [C.hD.card]
    have := H.q4
    omega
  have h3 : Nat.card C.K ^ 2 < Nat.card C.K ^ (Fintype.card C.ι) :=
    Nat.pow_lt_pow_right hq (by omega)
  omega

theorem pbot_t_of_index (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) (hs : Sit M Q Z X x)
    (hIc : ∀ z' ∈ Z, ∃ q ∈ Q, q⁻¹ * x * q = x * z')
    {o : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)} (hI : InvAct C x !![1, 1; 0, 1] o)
    (hD : Q ⊓ QB X = ⊥) (h4 : Fintype.card C.ι = 4) {S₀ : Subgroup G} (hS₀ : S₀ ≤ H0 M Z)
    (hidx : S₀.relIndex (H0 M Z) ≤ 6) (hfac : ∀ m ∈ S₀, TensorFactor C m) : False := by
  have H := hc.ctx.hyp
  have hw : Width Q Z (Fintype.card C.ι) := width_of_tensor C.hD C.φ
  have h12 := smith_1_12 hs
  have hcard := card_le_sq_of_tensorFactor hc C hs hIc hI hD (S := S₀ ⊓ Lx M X)
    inf_le_right (fun l hl => hfac l hl.1)
  have hne : S₀.relIndex (H0 M Z) ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hidx' : S₀.relIndex (Lx M X) ≤ 6 :=
    (Subgroup.relIndex_le_of_le_right (Lx_le_H0 hs h12) hne).trans hidx
  have hmul := Subgroup.relIndex_mul_card (H := S₀) (K := Lx M X)
  have hLge := Sit.card_Lx_ge hs hw
  rw [h4, ← C.hD.card] at hLge
  have hq : 4 ≤ Nat.card C.K := by
    rw [C.hD.card]
    exact H.q4
  have h1 : Nat.card ↥(Lx M X) ≤ 6 * Nat.card C.K ^ 2 := by
    rw [← hmul]
    exact (Nat.mul_le_mul hidx' hcard)
  have h2 : Nat.card C.K ^ 4 = Nat.card C.K ^ 2 * Nat.card C.K ^ 2 := by ring
  have h3 : 16 ≤ Nat.card C.K ^ 2 := by nlinarith
  set m := Nat.card C.K ^ 2
  nlinarith

end PBotT

end OrthCaseI

open OrthCaseI

section Assembly

@[expose] def OrthSimFourPlusStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ C : OrthCtx M Q Z B, Fintype.card C.ι = 4 → ¬ NoTotallySingularPlane C.qU →
      ∃ S : Subgroup G, S ≤ H0 M Z ∧ S.relIndex (H0 M Z) ≤ 6 ∧ ∀ m ∈ S, TensorFactor C m

theorem orthCaseIPBot_of_fourPlus (h24 : Smith24ActStatement)
    (hT : OrthTacitStatement) (h4 : OrthSimFourPlusStatement) : OrthCaseIPBotStatement := by
  intro G _ _ M Q Z B hc X x hs hxL hI hD
  obtain ⟨C⟩ := exists_orthCtx h24 hc
  have hno := noA2_of_tacit hT hc
  obtain ⟨o, h1 | ⟨h1, hdet, h'⟩⟩ := normal_form hc hno C hxL hs.x_sq
  · exact pbot_one hc C hs hI h1 hD
  · by_cases hdim : Fintype.card C.ι ≠ 4 ∨ NoTotallySingularPlane C.qU
    · exact pbot_t hc (C.change h1 hdet) hs hI h' hD (orthSim_of_dim hc (C.change h1 hdet) hdim)
    · push Not at hdim
      obtain ⟨S₀, hS₀, hidx, hfac⟩ := h4 G M Q Z B hc (C.change h1 hdet) hdim.1 hdim.2
      exact pbot_t_of_index hc (C.change h1 hdet) hs hI h' hD hdim.1 hS₀ hidx hfac

end Assembly

end CFSG.RankThree.GF2n.Smith81

module

public import CFSG.RankThree.GF2n.Stroth80.Sec7LinA0
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsE
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatComm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem exists_natLinear_conj [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    {Kg : Type} [Field Kg] [Finite Kg] {γ : G → Kg} {M₀ : Tim79.QuadModel Q Z Kg γ}
    {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)} {b : M₀.E} (hS : IsTensorSetup hc n M₀ ρ b)
    {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K))
    (θ : Kg ≃+* K)
    (hθ : ∀ (c : Kg) (v w : ↥(Vt M (LB M Q B) B Z t)), M₀.π w = c • M₀.π v →
      secVec ψ w = θ c • secVec ψ v)
    (hSmul : ∀ (c : Kg) (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z t))
    {y : G} (hyM : y ∈ M) (hyH : y ∈ H0 M Z)
    (hyV : ∀ v ∈ Vt M (LB M Q B) B Z t, y * v * y⁻¹ ∈ Vt M (LB M Q B) B Z t) :
    ∃ F : (ι → K) →ₗ[K] (ι → K), ∀ (k k' : ↥(Vt M (LB M Q B) B Z t)),
      (k' : G) = y * k * y⁻¹ → F (secVec ψ k) = secVec ψ k' := by
  classical
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZn : ∀ m ∈ M, ∀ z ∈ Z, m * z * m⁻¹ ∈ Z := fun m hm z hz =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hm) z).mp hz
  let ν : ↥(Vt M (LB M Q B) B Z t) →* ↥(Vt M (LB M Q B) B Z t) :=
    { toFun := fun k => ⟨y * k * y⁻¹, hyV k k.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hν : Z.subgroupOf (Vt M (LB M Q B) B Z t) ≤
      (Z.subgroupOf (Vt M (LB M Q B) B Z t)).comap ν := by
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact hZn y hyM z hz
  let f : Multiplicative (ι → K) →* Multiplicative (ι → K) :=
    ψ.toMonoidHom.comp ((QuotientGroup.map _ _ ν hν).comp ψ.symm.toMonoidHom)
  let Fa : (ι → K) →+ (ι → K) :=
    { toFun := fun w => Multiplicative.toAdd (f (Multiplicative.ofAdd w))
      map_zero' := by simp
      map_add' := fun a b => by simp [ofAdd_add, toAdd_mul] }
  have hFa : ∀ k : ↥(Vt M (LB M Q B) B Z t),
      Fa (secVec ψ k) = secVec ψ ⟨y * k * y⁻¹, hyV k k.2⟩ := by
    intro k
    show Multiplicative.toAdd (f (Multiplicative.ofAdd (secVec ψ k))) = _
    unfold secVec
    rw [ofAdd_toAdd]
    show Multiplicative.toAdd (ψ ((QuotientGroup.map _ _ ν hν) (ψ.symm (ψ (QuotientGroup.mk k)))))
      = _
    rw [MulEquiv.symm_apply_apply, QuotientGroup.map_mk]
    rfl
  have hbar : (QuotientGroup.mk (⟨y, hyM⟩ : ↥M) : Mbar M Q) ∈ bar M Q (H0 M Z) :=
    Subgroup.mem_map.mpr ⟨⟨y, hyM⟩, Subgroup.mem_subgroupOf.mpr hyH, rfl⟩
  have hsurj : ∀ w : ι → K, ∃ k : ↥(Vt M (LB M Q B) B Z t), secVec ψ k = w :=
    fun w => exists_secVec_eq ψ w
  refine ⟨{ toFun := Fa, map_add' := Fa.map_add, map_smul' := ?_ }, ?_⟩
  · intro c w
    obtain ⟨k, rfl⟩ := hsurj w
    obtain ⟨k₁, hk₁V, hk₁Q, hk₁π⟩ := hSmul (θ.symm c) (M₀.π k)
      (M₀.pi_mem_img k.2 (hVQ k.2))
    have hk₁ : secVec ψ ⟨k₁, hk₁V⟩ = c • secVec ψ k := by
      have := hθ (θ.symm c) k ⟨k₁, hk₁V⟩ hk₁π
      rw [RingEquiv.apply_symm_apply] at this
      exact this
    have e1 : Fa (c • secVec ψ k) = secVec ψ ⟨y * k₁ * y⁻¹, hyV k₁ hk₁V⟩ := by
      rw [← hk₁]
      exact hFa ⟨k₁, hk₁V⟩
    have hπ2 : M₀.π (y * k₁ * y⁻¹) = θ.symm c • M₀.π (y * (k : G) * y⁻¹) := by
      have h1 := hS.conj ⟨y, hyM⟩ k₁ hk₁Q
      have h2 := hS.conj ⟨y, hyM⟩ (k : G) (hVQ k.2)
      simp only at h1 h2
      rw [h1, h2, hk₁π, hS.lin _ hbar]
    have e2 := hθ (θ.symm c) ⟨y * k * y⁻¹, hyV k k.2⟩ ⟨y * k₁ * y⁻¹, hyV k₁ hk₁V⟩ hπ2
    rw [RingEquiv.apply_symm_apply] at e2
    show Fa (c • secVec ψ k) = c • Fa (secVec ψ k)
    rw [e1, hFa k]
    exact e2
  · intro k k' hk'
    have : k' = ⟨y * k * y⁻¹, hyV k k.2⟩ := Subtype.ext hk'
    subst this
    exact hFa k

theorem exists_conj_family [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (htM : t ∈ M) {Kg : Type} [Field Kg] [Finite Kg] {γ : G → Kg}
    {M₀ : Tim79.QuadModel Q Z Kg γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)} {b : M₀.E}
    (hS : IsTensorSetup hc n M₀ ρ b) {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K))
    (θ : Kg ≃+* K)
    (hθ : ∀ (c : Kg) (v w : ↥(Vt M (LB M Q B) B Z t)), M₀.π w = c • M₀.π v →
      secVec ψ w = θ c • secVec ψ v)
    {ψA : M₀.E →ₗ[Kg] M₀.E}
    (hψA : ∀ e, ψA e = (ρ (QuotientGroup.mk (⟨t, htM⟩ : ↥M))).toAdd e - e)
    {Z0 : Subgroup G}
    (hA0 : ∀ c : Kg, ∃ a ∈ bar M Q Z0, ∀ e, (ρ a).toAdd e = e + c • ψA e)
    {g : G} (hg : g ∈ M) (c : K) :
    ∃ y ∈ conjSubgroup g Z0, ∃ hyM : y ∈ M,
      ∀ (k k' k'' : ↥(Vt M (LB M Q B) B Z t)), (k' : G) = y * k * y⁻¹ →
        (k'' : G) = (g * t * g⁻¹) * k * (g * t * g⁻¹)⁻¹ →
        secVec ψ k' = secVec ψ k + c • (secVec ψ k'' - secVec ψ k) := by
  classical
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  obtain ⟨σ, a₀, T, hTs, hTπ, -, -⟩ := hS.model.act g hg
  set gb : Mbar M Q := QuotientGroup.mk (⟨g, hg⟩ : ↥M) with hgb
  have hρg : ∀ e, (ρ gb).toAdd e = T e := by
    intro e
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    rw [← hS.conj ⟨g, hg⟩ x hxQ, hTπ x hxQ]
  have hρg_smul : ∀ (c : Kg) e, (ρ gb).toAdd (c • e) = σ c • (ρ gb).toAdd e := by
    intro c e
    rw [hρg, hρg]
    exact hTs c e
  obtain ⟨a, haZ, haρ⟩ := hA0 (σ.symm (θ.symm c))
  obtain ⟨a', ha'Z0, ha'⟩ := Subgroup.mem_map.mp haZ
  have ha'Z : (a' : G) ∈ Z0 := Subgroup.mem_subgroupOf.mp ha'Z0
  have hyM : g * (a' : G) * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg a'.2) (M.inv_mem hg)
  refine ⟨g * (a' : G) * g⁻¹, ?_, hyM, ?_⟩
  · rw [mem_conjSubgroup]
    simpa [mul_assoc] using ha'Z
  intro k k' k'' hk' hk''
  have hxM : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg htM) (M.inv_mem hg)
  have hkQ : (k : G) ∈ Q := hVQ k.2
  have hk'Q : (k' : G) ∈ Q := hVQ k'.2
  have hk''Q : (k'' : G) ∈ Q := hVQ k''.2
  set e : M₀.E := M₀.π (k : G) with he
  set e₁ : M₀.E := (ρ gb⁻¹).toAdd e with he₁
  have hge₁ : (ρ gb).toAdd e₁ = e := by
    have h1 : ρ gb * ρ gb⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have h2 := congrArg (fun f : Multiplicative (AddAut M₀.E) => f.toAdd e) h1
    exact h2
  have hπy : M₀.π (k' : G) = e + σ (σ.symm (θ.symm c)) • (ρ gb).toAdd (ψA e₁) := by
    have h1 := hS.conj ⟨g * (a' : G) * g⁻¹, hyM⟩ (k : G) hkQ
    have h2 : (QuotientGroup.mk (⟨g * (a' : G) * g⁻¹, hyM⟩ : ↥M) : Mbar M Q) =
        gb * QuotientGroup.mk a' * gb⁻¹ := by
      rw [hgb, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rfl
    simp only at h1
    rw [← hk', h2] at h1
    have h3 : (ρ (gb * QuotientGroup.mk a' * gb⁻¹)).toAdd e =
        (ρ gb).toAdd ((ρ (QuotientGroup.mk a')).toAdd e₁) := by
      rw [map_mul ρ, map_mul ρ]
      rfl
    rw [h3] at h1
    have h4 : (ρ (QuotientGroup.mk a' : Mbar M Q)).toAdd e₁ =
        e₁ + σ.symm (θ.symm c) • ψA e₁ := by
      rw [← haρ e₁, ← ha']
      rfl
    rw [h4, map_add, hρg_smul, hge₁] at h1
    exact h1
  have hπx : M₀.π (k'' : G) = e + (ρ gb).toAdd (ψA e₁) := by
    have h1 := hS.conj ⟨g * t * g⁻¹, hxM⟩ (k : G) hkQ
    have h2 : (QuotientGroup.mk (⟨g * t * g⁻¹, hxM⟩ : ↥M) : Mbar M Q) =
        gb * QuotientGroup.mk (⟨t, htM⟩ : ↥M) * gb⁻¹ := by
      rw [hgb, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rfl
    simp only at h1
    rw [← hk'', h2] at h1
    have h3 : (ρ (gb * QuotientGroup.mk (⟨t, htM⟩ : ↥M) * gb⁻¹)).toAdd e =
        (ρ gb).toAdd ((ρ (QuotientGroup.mk (⟨t, htM⟩ : ↥M))).toAdd e₁) := by
      rw [map_mul ρ, map_mul ρ]
      rfl
    rw [h3] at h1
    have h4 : (ρ (QuotientGroup.mk (⟨t, htM⟩ : ↥M) : Mbar M Q)).toAdd e₁ = e₁ + ψA e₁ := by
      rw [hψA e₁]
      abel
    rw [h4, map_add, hge₁] at h1
    exact h1
  have hπ1 : M₀.π ((k' : G) * (k : G)⁻¹) = σ (σ.symm (θ.symm c)) • (ρ gb).toAdd (ψA e₁) := by
    rw [M₀.π_mul _ hk'Q _ (Q.inv_mem hkQ), M₀.pi_inv hkQ, hπy]
    abel
  have hπ2 : M₀.π ((k'' : G) * (k : G)⁻¹) = (ρ gb).toAdd (ψA e₁) := by
    rw [M₀.π_mul _ hk''Q _ (Q.inv_mem hkQ), M₀.pi_inv hkQ, hπx]
    abel
  have key := hθ (σ (σ.symm (θ.symm c)))
    (⟨(k'' : G) * (k : G)⁻¹, (Vt M (LB M Q B) B Z t).mul_mem k''.2
      ((Vt M (LB M Q B) B Z t).inv_mem k.2)⟩ : ↥(Vt M (LB M Q B) B Z t))
    (⟨(k' : G) * (k : G)⁻¹, (Vt M (LB M Q B) B Z t).mul_mem k'.2
      ((Vt M (LB M Q B) B Z t).inv_mem k.2)⟩ : ↥(Vt M (LB M Q B) B Z t))
    (by
      show M₀.π ((k' : G) * (k : G)⁻¹) = _ • M₀.π ((k'' : G) * (k : G)⁻¹)
      rw [hπ1, hπ2])
  have e1 : secVec ψ (⟨(k' : G) * (k : G)⁻¹, (Vt M (LB M Q B) B Z t).mul_mem k'.2
      ((Vt M (LB M Q B) B Z t).inv_mem k.2)⟩ : ↥(Vt M (LB M Q B) B Z t)) =
      secVec ψ k' - secVec ψ k := by
    have : (⟨(k' : G) * (k : G)⁻¹, (Vt M (LB M Q B) B Z t).mul_mem k'.2
        ((Vt M (LB M Q B) B Z t).inv_mem k.2)⟩ : ↥(Vt M (LB M Q B) B Z t)) = k' * k⁻¹ :=
      Subtype.ext rfl
    rw [this, secVec_mul, secVec_inv, sub_eq_add_neg]
  have e2 : secVec ψ (⟨(k'' : G) * (k : G)⁻¹, (Vt M (LB M Q B) B Z t).mul_mem k''.2
      ((Vt M (LB M Q B) B Z t).inv_mem k.2)⟩ : ↥(Vt M (LB M Q B) B Z t)) =
      secVec ψ k'' - secVec ψ k := by
    have : (⟨(k'' : G) * (k : G)⁻¹, (Vt M (LB M Q B) B Z t).mul_mem k''.2
        ((Vt M (LB M Q B) B Z t).inv_mem k.2)⟩ : ↥(Vt M (LB M Q B) B Z t)) = k'' * k⁻¹ :=
      Subtype.ext rfl
    rw [this, secVec_mul, secVec_inv, sub_eq_add_neg]
  rw [e1, e2, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply] at key
  rw [← key]
  abel

theorem exists_vanish_family (h34 : Stroth34Statement) (h310chi : Stroth310ChiStatement)
    (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement) (hZcard : Sec7ZCardStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = Nat.card Z) {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {X : Subgroup (GL ι K)} (hX : AddCommutantScalar X)
    (φ : ↥(Rt M (LB M Q B) t) →* GL ι K) (hφ : φ.range = X)
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    {g : G} (hg : g ∈ M) (hΓ : ∀ z ∈ Z0, ∀ y ∈ conjSubgroup g Z0, ⁅z, y⁆ ∈ Q) :
    ∃ T : (ι → K) →ₗ[K] (ι → K), (∀ w, T (T w) = 0) ∧
      (∀ c : K, ∃ A : GL ι K, (∀ w, (A : Matrix ι ι K) *ᵥ w = w + c • T w) ∧
        ∀ ω ∈ X, A * ω * A⁻¹ ∈ X) ∧
      ∀ k : ↥(Vt M (LB M Q B) B Z t), ∃ k' : ↥(Vt M (LB M Q B) B Z t),
        (k' : G) = ⁅g * t * g⁻¹, (k : G)⁆ ∧ T (secVec ψ k) = secVec ψ k' := by
  classical
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZ0H : Z0 ≤ H0 M Z := fun z hz => hc.Rt_le_H0 t (hZ0.le hz)
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  obtain ⟨Kg, fKg, finKg, γ, M₀, ρ, b, hS, ψA, hψA, -, -, -, -, hA0b⟩ :=
    sec7_A0 h34 h310chi hZc hZV hZcard hc hs hZ0
  have hcard : Nat.card Kg = Nat.card K := by rw [hS.card, hK]
  have hSmul : ∀ (c : Kg) (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z t) := fun c e he =>
    hc.smul_mem_img_Vt hS.model t c he
  have hlin : ∀ r ∈ Rt M (LB M Q B) t, ∃ T : M₀.E →ₗ[Kg] M₀.E,
      ∀ x ∈ Q, M₀.π (r * x * r⁻¹) = T (M₀.π x) := by
    intro r hr
    have hrM : r ∈ M := hc.Rt_le_M t hr
    have hrbar : (QuotientGroup.mk (⟨r, hrM⟩ : ↥M) : Mbar M Q) ∈ bar M Q (H0 M Z) :=
      Subgroup.mem_map.mpr ⟨⟨r, hrM⟩, Subgroup.mem_subgroupOf.mpr (hc.Rt_le_H0 t hr), rfl⟩
    refine ⟨(AddEquiv.toLinearEquiv (ρ (QuotientGroup.mk (⟨r, hrM⟩ : ↥M))).toAdd
      (hS.lin _ hrbar)).toLinearMap, fun x hx => ?_⟩
    exact hS.conj ⟨r, hrM⟩ x hx
  obtain ⟨θ, hθ⟩ := exists_ringEquiv_natural hcard M₀ hVQ hX hSmul hlin φ hφ
    (hc.Rt_normalizes_Vt ht) ψ hψ
  have hconj : ∀ y ∈ conjSubgroup g Z0, y ∈ M ∧ y ∈ H0 M Z ∧
      (∀ v ∈ Vt M (LB M Q B) B Z t, y * v * y⁻¹ ∈ Vt M (LB M Q B) B Z t) ∧
      (∀ r ∈ Rt M (LB M Q B) t, y * r * y⁻¹ ∈ Rt M (LB M Q B) t) := by
    intro y hy
    have hyM : y ∈ M := by
      have hz := hZ0M (mem_conjSubgroup.mp hy)
      have := M.mul_mem (M.mul_mem hg hz) (M.inv_mem hg)
      simpa [mul_assoc] using this
    have hyt : ⁅y, t⁆ ∈ Q := by
      have := Q.inv_mem (hΓ t htZ0 y hy)
      rwa [commutatorElement_inv] at this
    refine ⟨hyM, conjSubgroup_mem_H0 hc hZ0H hg hy, fun v hv => ?_, fun r hr => ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp
        (conjSubgroup_eq_self_iff.mp (endg_F0_Vt hc hyM hyt)) v).mp hv
    · exact (Subgroup.mem_normalizer_iff.mp
        (conjSubgroup_eq_self_iff.mp (endg_F0_Rt hc hyM hyt)) r).mp hr
  have hxmem : g * t * g⁻¹ ∈ conjSubgroup g Z0 := by
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using htZ0
  obtain ⟨hxM, hxH, hxV, hxR⟩ := hconj _ hxmem
  obtain ⟨Fx, hFx⟩ := exists_natLinear_conj hc hS ψ θ hθ hSmul hxM hxH hxV
  let T : (ι → K) →ₗ[K] (ι → K) := Fx - LinearMap.id
  have hTsv : ∀ k k' : ↥(Vt M (LB M Q B) B Z t), (k' : G) = (g * t * g⁻¹) * k * (g * t * g⁻¹)⁻¹ →
      T (secVec ψ k) = secVec ψ k' - secVec ψ k := by
    intro k k' hk'
    show Fx (secVec ψ k) - secVec ψ k = _
    rw [hFx k k' hk']
  have hsurj : ∀ w : ι → K, ∃ k : ↥(Vt M (LB M Q B) B Z t), secVec ψ k = w :=
    fun w => exists_secVec_eq ψ w
  have hVx : ∀ k : ↥(Vt M (LB M Q B) B Z t), ∃ k' : ↥(Vt M (LB M Q B) B Z t),
      (k' : G) = (g * t * g⁻¹) * k * (g * t * g⁻¹)⁻¹ :=
    fun k => ⟨⟨_, hxV k k.2⟩, rfl⟩
  have hx2 : (g * t * g⁻¹) ^ 2 ∈ Q := by
    rw [conj_pow]
    exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) (t ^ 2)).mp
      (hc.sq_mem_Q_of_mem_LB ht)
  have h2v : ∀ v : ι → K, v + v = 0 := fun v => by
    ext i
    simp [CharTwo.add_self_eq_zero]
  have hFxFx : ∀ w, Fx (Fx w) = w := by
    intro w
    obtain ⟨k, rfl⟩ := hsurj w
    have e1 := hFx k ⟨_, hxV k k.2⟩ rfl
    have e2 := hFx ⟨_, hxV k k.2⟩ ⟨_, hxV _ (hxV k k.2)⟩ rfl
    rw [e1, e2, secVec_eq_iff]
    have e : (g * t * g⁻¹) * ((g * t * g⁻¹) * (k : G) * (g * t * g⁻¹)⁻¹) * (g * t * g⁻¹)⁻¹ *
        (k : G)⁻¹ = ⁅(g * t * g⁻¹) ^ 2, (k : G)⁆ := by
      simp only [commutatorElement_def]
      rw [pow_two]
      group
    show (g * t * g⁻¹) * ((g * t * g⁻¹) * (k : G) * (g * t * g⁻¹)⁻¹) * (g * t * g⁻¹)⁻¹ *
        (k : G)⁻¹ ∈ Z
    rw [e]
    exact hc.hyp.toHyp79.comm_mem_V hx2 (hVQ k.2)
  have hT2 : ∀ w, T (T w) = 0 := by
    intro w
    have h1 : T (T w) = Fx (Fx w) - Fx w - Fx w + w := by
      show Fx (Fx w - w) - (Fx w - w) = _
      rw [map_sub]
      abel
    rw [h1, hFxFx w]
    have h3 : w - Fx w - Fx w + w = (w + w) - (Fx w + Fx w) := by abel
    rw [h3, h2v, h2v, sub_zero]
  have hmv : ∀ w, (LinearMap.toMatrix' T) *ᵥ w = T w := fun w => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  have mat_eq : ∀ (P N : Matrix ι ι K), (∀ w, P *ᵥ w = N *ᵥ w) → P = N := fun P N h =>
    Matrix.toLin'.injective (LinearMap.ext fun w => by
      simpa [Matrix.toLin'_apply] using h w)
  refine ⟨T, hT2, fun c => ?_, fun k => ?_⟩
  ·
    obtain ⟨y, hyZ, hyM, hy⟩ := exists_conj_family hc htM hS ψ θ hθ hψA hA0b hg c
    obtain ⟨-, hyH, hyV, hyR⟩ := hconj y hyZ
    obtain ⟨Fy, hFy⟩ := exists_natLinear_conj hc hS ψ θ hθ hSmul hyM hyH hyV
    have hFyT : ∀ k : ↥(Vt M (LB M Q B) B Z t),
        secVec ψ k + c • T (secVec ψ k) = secVec ψ ⟨y * k * y⁻¹, hyV k k.2⟩ := by
      intro k
      obtain ⟨k'', hk''⟩ := hVx k
      have := hy k ⟨y * k * y⁻¹, hyV k k.2⟩ k'' rfl hk''
      rw [hTsv k k'' hk'']
      exact this.symm
    let Mx : Matrix ι ι K := 1 + c • LinearMap.toMatrix' T
    have hMx : ∀ w, Mx *ᵥ w = w + c • T w := fun w => by
      show (1 + c • LinearMap.toMatrix' T) *ᵥ w = _
      rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hmv]
    have hMM : ∀ w, Mx *ᵥ (Mx *ᵥ w) = w := fun w => by
      rw [hMx, hMx, map_add, map_smul, hT2, smul_zero, add_zero]
      rw [add_assoc, h2v, add_zero]
    have hMul : Mx * Mx = 1 := mat_eq _ _ fun w => by
      rw [← Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec]
    let A : GL ι K := ⟨Mx, Mx, hMul, hMul⟩
    have hAv : ∀ k : ↥(Vt M (LB M Q B) B Z t),
        Mx *ᵥ secVec ψ k = secVec ψ ⟨y * k * y⁻¹, hyV k k.2⟩ := fun k => by
      rw [hMx]
      exact hFyT k
    refine ⟨A, hMx, fun ω hω => ?_⟩
    obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp (hφ ▸ hω)
    have hr' : y * (r : G) * y⁻¹ ∈ Rt M (LB M Q B) t := hyR r r.2
    have hmem : φ ⟨y * (r : G) * y⁻¹, hr'⟩ ∈ X := hφ ▸ MonoidHom.mem_range.mpr ⟨_, rfl⟩
    have hAinv : (A⁻¹ : GL ι K) = A := rfl
    convert hmem using 1
    apply Units.ext
    refine mat_eq _ _ fun w => ?_
    obtain ⟨k, hk⟩ := hsurj (Mx *ᵥ w)
    have hw : w = secVec ψ ⟨y * k * y⁻¹, hyV k k.2⟩ := by
      rw [← hAv k, hk, hMM]
    have hrk : (r : G) * k * (r : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht r.2) k).mp k.2
    have h1 := hψ r k ⟨(r : G) * k * (r : G)⁻¹, hrk⟩ rfl
    have h2 := hAv ⟨(r : G) * k * (r : G)⁻¹, hrk⟩
    have h3 := hψ ⟨y * (r : G) * y⁻¹, hr'⟩ ⟨y * k * y⁻¹, hyV k k.2⟩
      ⟨y * ((r : G) * k * (r : G)⁻¹) * y⁻¹, hyV _ hrk⟩ (by
        show y * ((r : G) * k * (r : G)⁻¹) * y⁻¹ = y * (r : G) * y⁻¹ * (y * k * y⁻¹) *
          (y * (r : G) * y⁻¹)⁻¹
        group)
    simp only [Units.val_mul, hAinv]
    show (Mx * ((φ r : GL ι K) : Matrix ι ι K) * Mx) *ᵥ w = _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hk]
    have h1' : (φ r : Matrix ι ι K) *ᵥ secVec ψ k = secVec ψ ⟨(r : G) * k * (r : G)⁻¹, hrk⟩ :=
      h1.symm
    rw [h1', h2]
    conv_rhs => rw [hw]
    exact h3
  · obtain ⟨k₂, hk₂⟩ := hVx k
    have hxk : ⁅g * t * g⁻¹, (k : G)⁆ ∈ Vt M (LB M Q B) B Z t := by
      rw [commutatorElement_def]
      exact (Vt M (LB M Q B) B Z t).mul_mem (hxV k k.2) ((Vt M (LB M Q B) B Z t).inv_mem k.2)
    refine ⟨⟨_, hxk⟩, rfl, ?_⟩
    have e : (⟨⁅g * t * g⁻¹, (k : G)⁆, hxk⟩ : ↥(Vt M (LB M Q B) B Z t)) = k₂ * k⁻¹ :=
      Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_inv, hk₂]; rfl)
    rw [e, secVec_mul, secVec_inv, hTsv k k₂ hk₂, sub_eq_add_neg]

end CFSG.RankThree.GF2n.Stroth80

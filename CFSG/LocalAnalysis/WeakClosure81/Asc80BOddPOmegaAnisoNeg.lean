module

public import CFSG.LieType.SeitzGeneration.OrthHyperRad
import CFSG.Mathlib.FieldTheory.Finite.QuadraticZeroMulti

public section

namespace CFSG.LocalAnalysis.WeakClosure81.POmegaOuter

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.SeitzGeneration
open scoped commutatorElement

section Basic

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private lemma Q_add_of_polar_eq_zero {Q : QuadraticForm K V} {x y : V}
    (hxy : polar Q x y = 0) (a b : K) :
    Q (a • x + b • y) = a ^ 2 * Q x + b ^ 2 * Q y := by
  rw [QuadraticMap.map_add Q (a • x) (b • y), map_smul_eq_sq, map_smul_eq_sq]
  have hp : polar Q (a • x) (b • y) = 0 := by
    rw [polar_smul_left, polar_smul_right, hxy, smul_zero, smul_zero]
  rw [hp, add_zero]

private lemma Q_add_add_of_orthogonal {Q : QuadraticForm K V} {x y z : V}
    (hxy : polar Q x y = 0) (hxz : polar Q x z = 0) (hyz : polar Q y z = 0) :
    Q (x + y + z) = Q x + Q y + Q z := by
  rw [QuadraticMap.map_add Q (x + y) z, QuadraticMap.map_add Q x y]
  have h : polar Q (x + y) z = 0 := by rw [polar_add_left, hxz, hyz, add_zero]
  rw [h, hxy, add_zero, add_zero]

private lemma linearIndependent_pair_of_polar_subtype {Q : QuadraticForm K V}
    {P : Submodule K V} {x y : V} (hx : x ∈ P) (hy : y ∈ P)
    (hxx : polar Q x x ≠ 0) (hy0 : y ≠ 0) (hxy : polar Q x y = 0) :
    LinearIndependent K ![(⟨x, hx⟩ : P), (⟨y, hy⟩ : P)] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hV : polar Q x (s • x + t • y) = 0 := by
    have h := congrArg (fun v : P => polar Q x (v : V)) hst
    simpa using h
  rw [polar_add_right, polar_smul_right, polar_smul_right, hxy] at hV
  have hs : s = 0 := by
    have h' : s * polar Q x x = 0 := by simpa [smul_eq_mul] using hV
    exact (mul_eq_zero.mp h').resolve_right hxx
  subst hs
  have ht : t • y = 0 := by
    have h := congrArg (fun v : P => (v : V)) hst
    simpa using h
  exact ⟨rfl, (smul_eq_zero.mp ht).resolve_right hy0⟩

end Basic

section Finite

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [Finite K] in
private lemma exists_ne_zero_polar_eq_zero_of_aniso {Q : QuadraticForm K V}
    (h2 : (2 : K) ≠ 0) {P : Submodule K V}
    (haniso : ∀ x ∈ P, Q x = 0 → x = 0)
    (hP : Module.finrank K P = 2) {x : P} (hx : x ≠ 0) :
    ∃ y ∈ P, y ≠ 0 ∧ polar Q (x : V) y = 0 := by
  classical
  let f : Module.Dual K P := ((polarBilin Q) (x : V)).comp P.subtype
  have hfx : f x = 2 * Q (x : V) := by
    simp [f, QuadraticMap.polarBilin_apply_apply]
  have hQx : Q (x : V) ≠ 0 := fun h => hx (Subtype.ext (haniso x x.2 h))
  have hf : f ≠ 0 := by
    intro h
    have h0 : f x = 0 := by rw [h]; rfl
    rw [hfx] at h0
    exact (mul_ne_zero h2 hQx) h0
  have hfker : Module.finrank K (LinearMap.ker f) + 1 = 2 := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero (K := K) (V₁ := P) (f := f) hf
    rwa [hP] at h
  have hne : LinearMap.ker f ≠ ⊥ := by
    intro hbot
    have h0 : Module.finrank K (LinearMap.ker f) = 0 := by rw [hbot, finrank_bot]
    omega
  obtain ⟨y, hyker, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨(y : V), y.2, fun h => hy0 (Subtype.ext h), ?_⟩
  have h := LinearMap.mem_ker.mp hyker
  simpa [f, QuadraticMap.polarBilin_apply_apply] using h

private lemma exists_aniso_plane_value {Q : QuadraticForm K V}
    {P : Submodule K V} (haniso : ∀ x ∈ P, Q x = 0 → x = 0)
    (hP : Module.finrank K P = 2) {c : K} (hc : c ≠ 0) :
    ∃ x ∈ P, Q x = c := by
  classical
  let q : QuadraticForm K (P × K) :=
    (Q.restrict P).comp (LinearMap.fst K P K) +
      (-c) • ((QuadraticMap.sq : QuadraticForm K K).comp (LinearMap.snd K P K))
  have hq : ∀ (p : P) (t : K), q (p, t) = Q (p : V) - c * t ^ 2 := by
    intro p t
    simp [q, QuadraticMap.comp_apply, QuadraticMap.sq_apply, QuadraticMap.restrict_apply,
      pow_two, sub_eq_add_neg]
  have hdim : Module.finrank K (P × K) = 3 := by
    rw [Module.finrank_prod, hP, Module.finrank_self]
  obtain ⟨v, hv0, hv⟩ :=
    CFSG.FiniteField.exists_ne_zero_forall_eq_zero_of_quadraticForm
      (K := K) (V := P × K) (fun _ : Fin 1 => q) (by rw [hdim]; norm_num)
  obtain ⟨p, t⟩ := v
  have hval : Q (p : V) - c * t ^ 2 = 0 := by
    have h := hv 0
    rwa [hq] at h
  have ht : t ≠ 0 := by
    intro ht0
    have hQp : Q (p : V) = 0 := by
      have h := hval
      rw [ht0] at h
      simpa using h
    have hp0 : p = 0 := Subtype.ext (haniso p p.2 hQp)
    apply hv0
    simp [hp0, ht0]
  refine ⟨t⁻¹ • p, P.smul_mem _ p.2, ?_⟩
  rw [map_smul_eq_sq]
  have hQp : Q (p : V) = c * t ^ 2 := by linear_combination hval
  rw [hQp]
  field_simp

private lemma exists_isometry_of_aniso_planes {Q : QuadraticForm K V}
    (h2 : (2 : K) ≠ 0) {P₁ P₂ : Submodule K V}
    (h₁ : Module.finrank K P₁ = 2) (h₂ : Module.finrank K P₂ = 2)
    (ha₁ : ∀ x ∈ P₁, Q x = 0 → x = 0) (ha₂ : ∀ x ∈ P₂, Q x = 0 → x = 0) :
    ∃ σ : P₁ ≃ₗ[K] P₂, ∀ x : P₁, Q ((σ x : P₂) : V) = Q (x : V) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have hP₁ne : P₁ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at h₁
    omega
  obtain ⟨x₁, hx₁P, hx₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP₁ne
  have hQx₁ : Q x₁ ≠ 0 := fun h => hx₁0 (ha₁ x₁ hx₁P h)
  have hxx₁ : polar Q x₁ x₁ ≠ 0 := by
    rw [polar_self_eq_two_mul]
    exact mul_ne_zero h2 hQx₁
  obtain ⟨y₁, hy₁P, hy₁0, hxy₁⟩ :=
    exists_ne_zero_polar_eq_zero_of_aniso h2 ha₁ h₁ (x := ⟨x₁, hx₁P⟩) (by simpa using hx₁0)
  have hQy₁ : Q y₁ ≠ 0 := fun h => hy₁0 (ha₁ y₁ hy₁P h)
  obtain ⟨x₂, hx₂P, hQx₂⟩ := exists_aniso_plane_value ha₂ h₂ (c := Q x₁) hQx₁
  have hx₂0 : x₂ ≠ 0 := by
    intro h
    apply hQx₁
    rw [← hQx₂, h]
    exact map_zero Q
  have hxx₂ : polar Q x₂ x₂ ≠ 0 := by
    rw [polar_self_eq_two_mul, hQx₂]
    exact mul_ne_zero h2 hQx₁
  obtain ⟨y₂, hy₂P, hy₂0, hxy₂⟩ :=
    exists_ne_zero_polar_eq_zero_of_aniso h2 ha₂ h₂ (x := ⟨x₂, hx₂P⟩) (by simpa using hx₂0)
  have hQy₂ : Q y₂ ≠ 0 := fun h => hy₂0 (ha₂ y₂ hy₂P h)
  have hnsq : ∀ (P : Submodule K V) (han : ∀ z ∈ P, Q z = 0 → z = 0)
      (x y : V) (hxP : x ∈ P) (hyP : y ∈ P), polar Q x x ≠ 0 → y ≠ 0 →
      polar Q x y = 0 → ¬ IsSquare (-(Q y / Q x)) := by
    intro P han x y hxP hyP hxx hy0 hxy hsq
    obtain ⟨s, hs⟩ := hsq
    have hQx : Q x ≠ 0 := fun h => hxx (by rw [polar_self_eq_two_mul, h, mul_zero])
    have hmem : s • x + y ∈ P := P.add_mem (P.smul_mem s hxP) hyP
    have hval : Q (s • x + y) = 0 := by
      have h1 := Q_add_of_polar_eq_zero hxy s 1
      rw [one_smul] at h1
      rw [h1]
      have hs' : s * s * Q x = -Q y := by
        have h := congrArg (fun z => z * Q x) hs
        have h' : -(Q y / Q x) * Q x = -Q y := by
          rw [neg_mul, div_mul_cancel₀ _ hQx]
        rw [h'] at h
        exact h.symm
      rw [show s ^ 2 * Q x + 1 ^ 2 * Q y = s * s * Q x + Q y by ring]
      linear_combination hs'
    have hzero : s • x + y = 0 := han _ hmem hval
    have hli : LinearIndependent K ![(⟨x, hxP⟩ : P), (⟨y, hyP⟩ : P)] :=
      linearIndependent_pair_of_polar_subtype hxP hyP hxx hy0 hxy
    have hz : s • (⟨x, hxP⟩ : P) + (1 : K) • (⟨y, hyP⟩ : P) = 0 := by
      apply Subtype.ext
      simpa using hzero
    have hpair := (LinearIndependent.pair_iff.mp hli) s 1 hz
    exact one_ne_zero hpair.2
  have hnsq₁ : ¬ IsSquare (-(Q y₁ / Q x₁)) :=
    hnsq P₁ ha₁ x₁ y₁ hx₁P hy₁P hxx₁ hy₁0 hxy₁
  have hnsq₂ : ¬ IsSquare (-(Q y₂ / Q x₂)) :=
    hnsq P₂ ha₂ x₂ y₂ hx₂P hy₂P hxx₂ hy₂0 hxy₂
  have hc₂ : Q x₂ ≠ 0 := by rw [hQx₂]; exact hQx₁
  have hratio₂ : Q y₂ / Q x₂ = Q y₂ / Q x₁ := by rw [hQx₂]
  have hne₁ : -(Q y₁ / Q x₁) ≠ 0 := by
    have : Q y₁ / Q x₁ ≠ 0 := div_ne_zero hQy₁ hQx₁
    exact neg_ne_zero.mpr this
  have hne₂ : -(Q y₂ / Q x₂) ≠ 0 := by
    have : Q y₂ / Q x₂ ≠ 0 := div_ne_zero hQy₂ hc₂
    exact neg_ne_zero.mpr this
  have hsq : IsSquare (Q y₁ / Q y₂) := by
    have hχ₁ : (quadraticChar K) (-(Q y₁ / Q x₁)) = -1 :=
      quadraticChar_neg_one_iff_not_isSquare.mpr hnsq₁
    have hχ₂ : (quadraticChar K) (-(Q y₂ / Q x₂)) = -1 :=
      quadraticChar_neg_one_iff_not_isSquare.mpr hnsq₂
    have hprod : IsSquare ((-(Q y₁ / Q x₁)) * (-(Q y₂ / Q x₂))) := by
      rw [← quadraticChar_one_iff_isSquare (mul_ne_zero hne₁ hne₂)]
      rw [map_mul, hχ₁, hχ₂]
      norm_num
    have hq₂sq : IsSquare ((Q y₂ / Q x₂) * (Q y₂ / Q x₂)) := IsSquare.mul_self _
    have hdiv := IsSquare.div hprod hq₂sq
    have hratio_eq : (-(Q y₁ / Q x₁)) * (-(Q y₂ / Q x₂)) /
        ((Q y₂ / Q x₂) * (Q y₂ / Q x₂)) = Q y₁ / Q y₂ := by
      rw [hQx₂]
      field_simp
    rwa [hratio_eq] at hdiv
  obtain ⟨lam, hlam⟩ := hsq
  have hlam0 : lam ≠ 0 := by
    intro h
    have h0 : Q y₁ / Q y₂ = 0 := by rw [hlam, h]; ring
    exact (div_ne_zero hQy₁ hQy₂) h0
  have hlamQ : Q (lam • y₂) = Q y₁ := by
    rw [map_smul_eq_sq, show lam ^ 2 = Q y₁ / Q y₂ by rw [pow_two]; exact hlam.symm]
    field_simp
  have hxy₂' : polar Q x₂ (lam • y₂) = 0 := by
    rw [polar_smul_right, hxy₂, smul_zero]
  have hli₁ : LinearIndependent K ![(⟨x₁, hx₁P⟩ : P₁), (⟨y₁, hy₁P⟩ : P₁)] :=
    linearIndependent_pair_of_polar_subtype hx₁P hy₁P hxx₁ hy₁0 hxy₁
  have hli₂ : LinearIndependent K
      ![(⟨x₂, hx₂P⟩ : P₂), (⟨lam • y₂, P₂.smul_mem lam hy₂P⟩ : P₂)] :=
    linearIndependent_pair_of_polar_subtype hx₂P (P₂.smul_mem lam hy₂P) hxx₂
      (smul_ne_zero hlam0 hy₂0) hxy₂'
  let b₁ : Module.Basis (Fin 2) K P₁ :=
    basisOfLinearIndependentOfCardEqFinrank hli₁ (by rw [h₁]; simp)
  let b₂ : Module.Basis (Fin 2) K P₂ :=
    basisOfLinearIndependentOfCardEqFinrank hli₂ (by rw [h₂]; simp)
  have hb₁ : ⇑b₁ = ![(⟨x₁, hx₁P⟩ : P₁), (⟨y₁, hy₁P⟩ : P₁)] :=
    coe_basisOfLinearIndependentOfCardEqFinrank hli₁ (by rw [h₁]; simp)
  have hb₂ : ⇑b₂ = ![(⟨x₂, hx₂P⟩ : P₂), (⟨lam • y₂, P₂.smul_mem lam hy₂P⟩ : P₂)] :=
    coe_basisOfLinearIndependentOfCardEqFinrank hli₂ (by rw [h₂]; simp)
  let σ : P₁ ≃ₗ[K] P₂ := b₁.equivFun.trans b₂.equivFun.symm
  have hv : ∀ v : P₁, (v : V) =
      b₁.equivFun v 0 • x₁ + b₁.equivFun v 1 • y₁ := by
    intro v
    have h : (v : V) = ((b₁.equivFun.symm (b₁.equivFun v) : P₁) : V) := by
      rw [LinearEquiv.symm_apply_apply]
    rw [h, Module.Basis.equivFun_symm_apply, Fin.sum_univ_two]
    simp [hb₁]
  have hσv : ∀ v : P₁, (σ v : V) =
      b₁.equivFun v 0 • x₂ + b₁.equivFun v 1 • (lam • y₂) := by
    intro v
    have h : (σ v : V) = ((b₂.equivFun.symm (b₁.equivFun v) : P₂) : V) := rfl
    rw [h, Module.Basis.equivFun_symm_apply, Fin.sum_univ_two]
    simp [hb₂]
  refine ⟨σ, fun v => ?_⟩
  rw [hσv v, hv v]
  rw [Q_add_of_polar_eq_zero hxy₂' (b₁.equivFun v 0) (b₁.equivFun v 1)]
  rw [Q_add_of_polar_eq_zero hxy₁ (b₁.equivFun v 0) (b₁.equivFun v 1)]
  rw [hQx₂, hlamQ]

end Finite

section Main

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem mem_commutator_of_neg_on_aniso_planes {Q : QuadraticForm K V} (h2 : (2 : K) ≠ 0)
    {P₁ P₂ : Submodule K V} (h₁ : Module.finrank K P₁ = 2) (h₂ : Module.finrank K P₂ = 2)
    (ha₁ : ∀ x ∈ P₁, Q x = 0 → x = 0) (ha₂ : ∀ x ∈ P₂, Q x = 0 → x = 0)
    (h₁₂ : ∀ x ∈ P₁, ∀ y ∈ P₂, polar Q x y = 0) (T : V ≃ₗ[K] V)
    (hT : ∀ x ∈ P₁ ⊔ P₂, T x = -x) (hT' : ∀ x ∈ qPerp Q (P₁ ⊔ P₂), T x = x) :
    T ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  classical
  let U : Submodule K V := P₁ ⊔ P₂
  let U' : Submodule K V := qPerp Q U
  have hP₁U : P₁ ≤ U := le_sup_left
  have hP₂U : P₂ ≤ U := le_sup_right
  have hP₁P₂ : Disjoint P₁ P₂ := by
    rw [disjoint_iff_inf_le]
    intro x hx
    rw [Submodule.mem_bot]
    obtain ⟨hx₁, hx₂⟩ := hx
    have h := h₁₂ x hx₁ x hx₂
    have h2Q : (2 : K) * Q x = 0 := by
      rw [← polar_self_eq_two_mul]
      exact h
    exact ha₁ x hx₁ ((mul_eq_zero.mp h2Q).resolve_left h2)
  have hP₁P₂_inf : P₁ ⊓ P₂ = ⊥ :=
    le_bot_iff.mp (disjoint_iff_inf_le.mp hP₁P₂)
  have hdisj : Disjoint U U' := by
    rw [disjoint_iff_inf_le]
    intro x hx
    rw [Submodule.mem_bot]
    obtain ⟨hxU, hxU'⟩ := hx
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxU
    subst hab
    have hQa : Q a = 0 := by
      have h := hxU' a (Submodule.mem_sup_left ha)
      rw [polar_add_right, polar_self_eq_two_mul, h₁₂ a ha b hb, add_zero] at h
      exact (mul_eq_zero.mp h).resolve_left h2
    have hQb : Q b = 0 := by
      have h := hxU' b (Submodule.mem_sup_right hb)
      rw [polar_add_right, polar_comm Q b a, h₁₂ a ha b hb, zero_add,
        polar_self_eq_two_mul] at h
      exact (mul_eq_zero.mp h).resolve_left h2
    rw [ha₁ a ha hQa, ha₂ b hb hQb]
    simp
  have horth : LinearMap.BilinForm.orthogonal (polarBilin Q) U = U' := by
    ext v
    change (∀ n ∈ U, polar Q n v = 0) ↔ v ∈ qPerp Q U
    simp only [mem_qPerp]
  have hBnd : (LinearMap.BilinForm.restrict (polarBilin Q) U).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal (polarBilin Q)
      (QuadraticMap.isSymm_polarBilin Q).isRefl (by rw [horth]; exact hdisj)
  have hcompl : IsCompl U U' := by
    have h := LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
      (B := polarBilin Q) (W := U) (QuadraticMap.isSymm_polarBilin Q).isRefl hBnd
    rw [horth] at h
    exact h
  let P₁' : Submodule K U := P₁.comap U.subtype
  let P₂' : Submodule K U := P₂.comap U.subtype
  have hP' : IsCompl P₁' P₂' := by
    refine IsCompl.of_eq ?_ ?_
    · rw [Submodule.eq_bot_iff]
      intro u hu
      have h1 : (u : V) ∈ P₁ := hu.1
      have h2 : (u : V) ∈ P₂ := hu.2
      have hbot : (u : V) ∈ P₁ ⊓ P₂ := ⟨h1, h2⟩
      rw [hP₁P₂_inf] at hbot
      exact Subtype.ext (by simpa using hbot)
    · rw [Submodule.eq_top_iff']
      intro u
      have hu : (u : V) ∈ P₁ ⊔ P₂ := u.2
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hu
      refine Submodule.mem_sup.mpr ⟨⟨a, Submodule.mem_sup_left ha⟩, ha,
        ⟨b, Submodule.mem_sup_right hb⟩, hb, ?_⟩
      apply Subtype.ext
      exact hab
  obtain ⟨σ, hσQ⟩ := exists_isometry_of_aniso_planes h2 h₁ h₂ ha₁ ha₂
  let e₁ : P₁' ≃ₗ[K] P₁ := Submodule.comapSubtypeEquivOfLe hP₁U
  let e₂ : P₂' ≃ₗ[K] P₂ := Submodule.comapSubtypeEquivOfLe hP₂U
  let π₁ : U →ₗ[K] P₁' := Submodule.projectionOnto P₁' P₂' hP'
  let π₂ : U →ₗ[K] P₂' := Submodule.projectionOnto P₂' P₁' hP'.symm
  let fU : U →ₗ[K] V :=
    ((P₂.subtype.comp σ.toLinearMap).comp e₁.toLinearMap).comp π₁ +
      ((P₁.subtype.comp σ.symm.toLinearMap).comp e₂.toLinearMap).comp π₂
  have hπ₁a : ∀ a : P₁, π₁ ⟨(a : V), hP₁U a.2⟩ = e₁.symm a := by
    intro a
    have hco : ((e₁.symm a : P₁') : U) = ⟨(a : V), hP₁U a.2⟩ := Subtype.ext rfl
    calc π₁ ⟨(a : V), hP₁U a.2⟩ = π₁ ((e₁.symm a : P₁') : U) := by rw [hco]
      _ = e₁.symm a := Submodule.projectionOnto_apply_left hP' (e₁.symm a)
  have hπ₂a : ∀ a : P₁, π₂ ⟨(a : V), hP₁U a.2⟩ = 0 := fun a =>
    Submodule.projectionOnto_apply_right hP'.symm (⟨⟨(a : V), hP₁U a.2⟩, a.2⟩ : P₁')
  have hπ₁b : ∀ b : P₂, π₁ ⟨(b : V), hP₂U b.2⟩ = 0 := fun b =>
    Submodule.projectionOnto_apply_right hP' (⟨⟨(b : V), hP₂U b.2⟩, b.2⟩ : P₂')
  have hπ₂b : ∀ b : P₂, π₂ ⟨(b : V), hP₂U b.2⟩ = e₂.symm b := by
    intro b
    have hco : ((e₂.symm b : P₂') : U) = ⟨(b : V), hP₂U b.2⟩ := Subtype.ext rfl
    calc π₂ ⟨(b : V), hP₂U b.2⟩ = π₂ ((e₂.symm b : P₂') : U) := by rw [hco]
      _ = e₂.symm b := Submodule.projectionOnto_apply_left hP'.symm (e₂.symm b)
  have hfU₁ : ∀ a : P₁, fU ⟨(a : V), hP₁U a.2⟩ = (σ a : V) := by
    intro a
    rw [show fU ⟨(a : V), hP₁U a.2⟩ =
      ((P₂.subtype.comp σ.toLinearMap).comp e₁.toLinearMap) (π₁ ⟨(a : V), hP₁U a.2⟩) +
      ((P₁.subtype.comp σ.symm.toLinearMap).comp e₂.toLinearMap)
        (π₂ ⟨(a : V), hP₁U a.2⟩) from rfl]
    rw [hπ₁a a, hπ₂a a]
    simp
  have hfU₂ : ∀ b : P₂, fU ⟨(b : V), hP₂U b.2⟩ = (σ.symm b : V) := by
    intro b
    rw [show fU ⟨(b : V), hP₂U b.2⟩ =
      ((P₂.subtype.comp σ.toLinearMap).comp e₁.toLinearMap) (π₁ ⟨(b : V), hP₂U b.2⟩) +
      ((P₁.subtype.comp σ.symm.toLinearMap).comp e₂.toLinearMap)
        (π₂ ⟨(b : V), hP₂U b.2⟩) from rfl]
    rw [hπ₁b b, hπ₂b b]
    simp
  let τlin : V →ₗ[K] V := LinearMap.ofIsCompl hcompl fU U'.subtype
  have hτ₁ : ∀ a : P₁, τlin (a : V) = (σ a : V) := by
    intro a
    have h := LinearMap.ofIsCompl_apply_left (h := hcompl) (φ := fU) (ψ := U'.subtype)
      (u := (⟨(a : V), hP₁U a.2⟩ : U))
    exact h.trans (hfU₁ a)
  have hτ₂ : ∀ b : P₂, τlin (b : V) = (σ.symm b : V) := by
    intro b
    have h := LinearMap.ofIsCompl_apply_left (h := hcompl) (φ := fU) (ψ := U'.subtype)
      (u := (⟨(b : V), hP₂U b.2⟩ : U))
    exact h.trans (hfU₂ b)
  have hτ₀ : ∀ w : U', τlin (w : V) = (w : V) := fun w =>
    LinearMap.ofIsCompl_apply_right hcompl (φ := fU) (ψ := U'.subtype) w
  let rU : U →ₗ[K] V :=
    -(((P₁.subtype.comp e₁.toLinearMap).comp π₁)) +
      ((P₂.subtype.comp e₂.toLinearMap).comp π₂)
  have hfU₁' : ∀ a : P₁, rU ⟨(a : V), hP₁U a.2⟩ = -(a : V) := by
    intro a
    simp only [rU, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply]
    rw [hπ₁a a, hπ₂a a]
    simp
  have hfU₂' : ∀ b : P₂, rU ⟨(b : V), hP₂U b.2⟩ = (b : V) := by
    intro b
    simp only [rU, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply]
    rw [hπ₁b b, hπ₂b b]
    simp
  let rlin : V →ₗ[K] V := LinearMap.ofIsCompl hcompl rU U'.subtype
  have hr₁ : ∀ a : P₁, rlin (a : V) = -(a : V) := by
    intro a
    have h := LinearMap.ofIsCompl_apply_left (h := hcompl) (φ := rU) (ψ := U'.subtype)
      (u := (⟨(a : V), hP₁U a.2⟩ : U))
    exact h.trans (hfU₁' a)
  have hr₂ : ∀ b : P₂, rlin (b : V) = (b : V) := by
    intro b
    have h := LinearMap.ofIsCompl_apply_left (h := hcompl) (φ := rU) (ψ := U'.subtype)
      (u := (⟨(b : V), hP₂U b.2⟩ : U))
    exact h.trans (hfU₂' b)
  have hr₀ : ∀ w : U', rlin (w : V) = (w : V) := fun w =>
    LinearMap.ofIsCompl_apply_right hcompl (φ := rU) (ψ := U'.subtype) w
  have hdecomp : ∀ v : V, ∃ a ∈ P₁, ∃ b ∈ P₂, ∃ w ∈ U', a + b + w = v := by
    intro v
    have hv : v ∈ U ⊔ U' := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hv
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hu
    exact ⟨a, ha, b, hb, w, hw, by rw [← huw, ← hab]⟩
  have hττ : ∀ v : V, τlin (τlin v) = v := by
    intro v
    obtain ⟨a, ha, b, hb, w, hw, hav⟩ := hdecomp v
    let a' : P₁ := ⟨a, ha⟩
    let b' : P₂ := ⟨b, hb⟩
    let w' : U' := ⟨w, hw⟩
    have hτv : τlin v = (σ a' : V) + (σ.symm b' : V) + (w' : V) := by
      rw [← hav]
      change τlin ((a' : V) + (b' : V) + (w' : V)) = _
      rw [map_add, map_add, hτ₁, hτ₂, hτ₀]
    rw [hτv, map_add, map_add, hτ₂, hτ₁, hτ₀]
    simp only [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
    simpa using hav
  have hrr : ∀ v : V, rlin (rlin v) = v := by
    intro v
    obtain ⟨a, ha, b, hb, w, hw, hav⟩ := hdecomp v
    let a' : P₁ := ⟨a, ha⟩
    let b' : P₂ := ⟨b, hb⟩
    let w' : U' := ⟨w, hw⟩
    have hrv : rlin v = -(a' : V) + (b' : V) + (w' : V) := by
      rw [← hav]
      change rlin ((a' : V) + (b' : V) + (w' : V)) = _
      rw [map_add, map_add, hr₁, hr₂, hr₀]
    rw [hrv, map_add, map_add]
    have h1 : rlin (-(a' : V)) = (a' : V) := by
      have h := hr₁ (-a')
      simpa using h
    rw [h1, hr₂, hr₀]
    simpa using hav
  have hτQ : ∀ v, Q (τlin v) = Q v := by
    intro v
    obtain ⟨a, ha, b, hb, w, hw, hav⟩ := hdecomp v
    let a' : P₁ := ⟨a, ha⟩
    let b' : P₂ := ⟨b, hb⟩
    let w' : U' := ⟨w, hw⟩
    have hv : v = (a' : V) + (b' : V) + (w' : V) := by simpa using hav.symm
    have hτv : τlin v = (σ a' : V) + (σ.symm b' : V) + (w' : V) := by
      rw [← hav]
      change τlin ((a' : V) + (b' : V) + (w' : V)) = _
      rw [map_add, map_add, hτ₁, hτ₂, hτ₀]
    have h₁ : polar Q (σ a' : V) (σ.symm b' : V) = 0 := by
      rw [polar_comm]
      exact h₁₂ (σ.symm b') (σ.symm b').2 (σ a') (σ a').2
    have h₂ : polar Q (σ a' : V) (w' : V) = 0 :=
      mem_qPerp.mp w'.2 (σ a') (hP₂U (σ a').2)
    have h₃ : polar Q (σ.symm b' : V) (w' : V) = 0 :=
      mem_qPerp.mp w'.2 (σ.symm b') (hP₁U (σ.symm b').2)
    have h₄ : polar Q (a' : V) (b' : V) = 0 := h₁₂ a' a'.2 b' b'.2
    have h₅ : polar Q (a' : V) (w' : V) = 0 := mem_qPerp.mp w'.2 a' (hP₁U a'.2)
    have h₆ : polar Q (b' : V) (w' : V) = 0 := mem_qPerp.mp w'.2 b' (hP₂U b'.2)
    have hσsymm : Q (σ.symm b' : V) = Q (b' : V) := by
      have h := hσQ (σ.symm b')
      rw [LinearEquiv.apply_symm_apply] at h
      exact h.symm
    rw [hτv, hv, Q_add_add_of_orthogonal h₁ h₂ h₃, Q_add_add_of_orthogonal h₄ h₅ h₆,
      hσQ a', hσsymm]
  have hrQ : ∀ v, Q (rlin v) = Q v := by
    intro v
    obtain ⟨a, ha, b, hb, w, hw, hav⟩ := hdecomp v
    let a' : P₁ := ⟨a, ha⟩
    let b' : P₂ := ⟨b, hb⟩
    let w' : U' := ⟨w, hw⟩
    have hv : v = (a' : V) + (b' : V) + (w' : V) := by simpa using hav.symm
    have hrv : rlin v = -(a' : V) + (b' : V) + (w' : V) := by
      rw [← hav]
      change rlin ((a' : V) + (b' : V) + (w' : V)) = _
      rw [map_add, map_add, hr₁, hr₂, hr₀]
    have h₁ : polar Q (-(a' : V)) (b' : V) = 0 := by
      rw [polar_neg_left, h₁₂ a' a'.2 b' b'.2, neg_zero]
    have h₂ : polar Q (-(a' : V)) (w' : V) = 0 := by
      rw [polar_neg_left, mem_qPerp.mp w'.2 a' (hP₁U a'.2), neg_zero]
    have h₃ : polar Q (b' : V) (w' : V) = 0 := mem_qPerp.mp w'.2 b' (hP₂U b'.2)
    have h₄ : polar Q (a' : V) (b' : V) = 0 := h₁₂ a' a'.2 b' b'.2
    have h₅ : polar Q (a' : V) (w' : V) = 0 := mem_qPerp.mp w'.2 a' (hP₁U a'.2)
    have h₆ : polar Q (b' : V) (w' : V) = 0 := mem_qPerp.mp w'.2 b' (hP₂U b'.2)
    rw [hrv, hv, Q_add_add_of_orthogonal h₁ h₂ h₃, Q_add_add_of_orthogonal h₄ h₅ h₆,
      QuadraticMap.map_neg]
  have hτ_inj : Function.Injective τlin := fun x y hxy => by
    have := congrArg τlin hxy
    simpa [hττ] using this
  have hτ_surj : Function.Surjective τlin := fun v => ⟨τlin v, hττ v⟩
  let τ : V ≃ₗ[K] V := LinearEquiv.ofBijective τlin ⟨hτ_inj, hτ_surj⟩
  have hρ_inj : Function.Injective rlin := fun x y hxy => by
    have := congrArg rlin hxy
    simpa [hrr] using this
  have hρ_surj : Function.Surjective rlin := fun v => ⟨rlin v, hrr v⟩
  let ρ : V ≃ₗ[K] V := LinearEquiv.ofBijective rlin ⟨hρ_inj, hρ_surj⟩
  have hτ_apply : ∀ v, τ v = τlin v := fun v => rfl
  have hρ_apply : ∀ v, ρ v = rlin v := fun v => rfl
  have hτa : ∀ a : P₁, τ (a : V) = (σ a : V) := fun a => by rw [hτ_apply, hτ₁]
  have hτb : ∀ b : P₂, τ (b : V) = (σ.symm b : V) := fun b => by rw [hτ_apply, hτ₂]
  have hτw : ∀ w : U', τ (w : V) = (w : V) := fun w => by rw [hτ_apply, hτ₀]
  have hρa : ∀ a : P₁, ρ (a : V) = -(a : V) := fun a => by rw [hρ_apply, hr₁]
  have hρb : ∀ b : P₂, ρ (b : V) = (b : V) := fun b => by rw [hρ_apply, hr₂]
  have hρw : ∀ w : U', ρ (w : V) = (w : V) := fun w => by rw [hρ_apply, hr₀]
  have hτ_mem : τ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [hτ_apply, hτQ]
  have hρ_mem : ρ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [hρ_apply, hrQ]
  have hτ_mul : τ * τ = 1 := by
    ext v
    rw [LinearEquiv.mul_apply]
    change τ (τ v) = v
    rw [hτ_apply, hτ_apply, hττ]
  have hρ_mul : ρ * ρ = 1 := by
    ext v
    rw [LinearEquiv.mul_apply]
    change ρ (ρ v) = v
    rw [hρ_apply, hρ_apply, hrr]
  have hτ_inv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ_mul
  have hρ_inv : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρ_mul
  have hcomm₁ : ∀ a : P₁, ⁅τ, ρ⁆ (a : V) = -(a : V) := by
    intro a
    rw [commutatorElement_def]
    simp only [LinearEquiv.mul_apply, hτ_inv, hρ_inv]
    have h1 : τ (-(a : V)) = -((σ a : P₂) : V) := by
      have h := hτa (-a)
      simpa using h
    have h2 : ρ (-((σ a : P₂) : V)) = -((σ a : P₂) : V) := by
      have h := hρb (-(σ a))
      simpa using h
    have h3 : τ (-((σ a : P₂) : V)) = -(a : V) := by
      have h := hτb (-(σ a))
      simpa using h
    rw [hρa a, h1, h2, h3]
  have hcomm₂ : ∀ b : P₂, ⁅τ, ρ⁆ (b : V) = -(b : V) := by
    intro b
    rw [commutatorElement_def]
    simp only [LinearEquiv.mul_apply, hτ_inv, hρ_inv]
    have h1 : τ (-(σ.symm b : V)) = -(b : V) := by
      have h := hτa (-(σ.symm b))
      simpa using h
    rw [hρb b, hτb b, hρa (σ.symm b), h1]
  have hcomm₀ : ∀ w : U', ⁅τ, ρ⁆ (w : V) = (w : V) := by
    intro w
    rw [commutatorElement_def]
    simp only [LinearEquiv.mul_apply, hτ_inv, hρ_inv]
    rw [hρw w, hτw w, hρw w, hτw w]
  have hTeq : T = ⁅τ, ρ⁆ := by
    ext v
    obtain ⟨a, ha, b, hb, w, hw, hav⟩ := hdecomp v
    let a' : P₁ := ⟨a, ha⟩
    let b' : P₂ := ⟨b, hb⟩
    let w' : U' := ⟨w, hw⟩
    have hTv : T v = -((a' : V) + (b' : V)) + (w' : V) := by
      rw [← hav]
      have hTa : T (a' : V) = -(a' : V) := hT a' (Submodule.mem_sup_left a'.2)
      have hTb : T (b' : V) = -(b' : V) := hT b' (Submodule.mem_sup_right b'.2)
      have hTw : T (w' : V) = (w' : V) := hT' w' w'.2
      change T ((a' : V) + (b' : V) + (w' : V)) = _
      rw [map_add, map_add, hTa, hTb, hTw]
      abel
    have hT'v : ⁅τ, ρ⁆ v = -((a' : V) + (b' : V)) + (w' : V) := by
      rw [← hav]
      have h1 : ⁅τ, ρ⁆ (a' : V) = -(a' : V) := hcomm₁ a'
      have h2 : ⁅τ, ρ⁆ (b' : V) = -(b' : V) := hcomm₂ b'
      have h3 : ⁅τ, ρ⁆ (w' : V) = (w' : V) := hcomm₀ w'
      change ⁅τ, ρ⁆ ((a' : V) + (b' : V) + (w' : V)) = _
      rw [map_add, map_add, h1, h2, h3]
      abel
    rw [hTv, hT'v]
  rw [hTeq]
  exact Subgroup.commutator_mem_commutator hτ_mem hρ_mem

end Main

end CFSG.LocalAnalysis.WeakClosure81.POmegaOuter


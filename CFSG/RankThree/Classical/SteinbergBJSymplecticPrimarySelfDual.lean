module

public import CFSG.RankThree.Classical.SteinbergBJSymplecticPrimaryCentralizer
public import CFSG.RankThree.PartOne.KC.UnitaryPrimarySelfDual
public import CFSG.RankThree.PartOne.KC.OrthogonalTraceModels
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

public section

namespace CFSG.RankThree.Classical

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCUnitary (gl_centralizer mem_gl_centralizer glCentralizerEquivPi
  blockGL blockApply blockApply_one unitaryCentralizer mem_unitaryCentralizer supportedUnitary
  supportedUnitary_le_gl_centralizer eq_one_of_forall_apply_eq dualPoly eval₂_theta_root_inv
  root_ne_zero selfDualVal selfDualVal_spec selfDualVal_eq_iff selfDualVal_add_left
  selfDualVal_add_right selfDualVal_smul_right)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial exists_involution_eq_frobPow
  frobPow_apply)

section RootInv

variable {K : Type*} [Field K] {a : K[X]} [Fact (Irreducible a)]

theorem dualPoly_id_eq (a : K[X]) : dualPoly (RingHom.id K) a = reciprocalPolynomial a := by
  rw [dualPoly, reciprocalPolynomial, Polynomial.map_id, RingHom.id_apply]

theorem eval₂_root_inv (h0 : a.coeff 0 ≠ 0) (hself : reciprocalPolynomial a = a) :
    a.eval₂ (algebraMap K (AdjoinRoot a)) (AdjoinRoot.root a)⁻¹ = 0 := by
  have := eval₂_theta_root_inv (σ := RingHom.id K) h0 (by rw [dualPoly_id_eq, hself])
  rwa [RingHom.comp_id] at this

@[expose] noncomputable def rootInvHom (h0 : a.coeff 0 ≠ 0) (hself : reciprocalPolynomial a = a) :
    AdjoinRoot a →ₐ[K] AdjoinRoot a :=
  AdjoinRoot.liftAlgHom a (Algebra.ofId K (AdjoinRoot a)) (AdjoinRoot.root a)⁻¹
    (eval₂_root_inv h0 hself)

theorem rootInvHom_root (h0 : a.coeff 0 ≠ 0) (hself : reciprocalPolynomial a = a) :
    rootInvHom h0 hself (AdjoinRoot.root a) = (AdjoinRoot.root a)⁻¹ :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem rootInvHom_comp (h0 : a.coeff 0 ≠ 0) (hself : reciprocalPolynomial a = a) :
    (rootInvHom h0 hself).comp (rootInvHom h0 hself) = AlgHom.id K (AdjoinRoot a) := by
  apply AdjoinRoot.algHom_ext
  simp [rootInvHom_root, map_inv₀]

@[expose] noncomputable def rootInv (h0 : a.coeff 0 ≠ 0) (hself : reciprocalPolynomial a = a) :
    AdjoinRoot a ≃ₐ[K] AdjoinRoot a :=
  AlgEquiv.ofAlgHom (rootInvHom h0 hself) (rootInvHom h0 hself) (rootInvHom_comp h0 hself)
    (rootInvHom_comp h0 hself)

theorem rootInv_root (h0 : a.coeff 0 ≠ 0) (hself : reciprocalPolynomial a = a) :
    rootInv h0 hself (AdjoinRoot.root a) = (AdjoinRoot.root a)⁻¹ :=
  rootInvHom_root h0 hself

theorem rootInv_rootInv (h0 : a.coeff 0 ≠ 0) (hself : reciprocalPolynomial a = a)
    (z : AdjoinRoot a) : rootInv h0 hself (rootInv h0 hself z) = z :=
  AlgHom.congr_fun (rootInvHom_comp h0 hself) z

theorem rootInv_ne_one (h0 : a.coeff 0 ≠ 0) (hself : reciprocalPolynomial a = a)
    (hsq : AdjoinRoot.root a ^ 2 ≠ 1) : rootInv h0 hself ≠ 1 := by
  intro h
  have h1 := congrArg (fun σ : AdjoinRoot a ≃ₐ[K] AdjoinRoot a => σ (AdjoinRoot.root a)) h
  simp only [rootInv_root, AlgEquiv.one_apply] at h1
  apply hsq
  calc AdjoinRoot.root a ^ 2 = AdjoinRoot.root a * (AdjoinRoot.root a)⁻¹ := by rw [h1, sq]
    _ = 1 := mul_inv_cancel₀ (root_ne_zero h0)

theorem exists_rootInv_eq_pow [Finite K] (h0 : a.coeff 0 ≠ 0)
    (hself : reciprocalPolynomial a = a) (hsq : AdjoinRoot.root a ^ 2 ≠ 1) :
    ∃ d : ℕ, finrank K (AdjoinRoot a) = 2 * d ∧
      ∀ z, rootInv h0 hself z = z ^ (Nat.card K ^ d) := by
  have : Finite (AdjoinRoot a) := Module.finite_of_finite K
  obtain ⟨d, hd, hσ⟩ := exists_involution_eq_frobPow (rootInv h0 hself)
    (rootInv_rootInv h0 hself) (rootInv_ne_one h0 hself hsq)
  exact ⟨d, hd, fun z => by rw [hσ, frobPow_apply]⟩

theorem exists_ne_zero_neg (σ : AdjoinRoot a ≃ₐ[K] AdjoinRoot a) (hσσ : ∀ z, σ (σ z) = z)
    (hne : σ ≠ 1) : ∃ η : AdjoinRoot a, η ≠ 0 ∧ σ η = -η := by
  obtain ⟨z, hz⟩ : ∃ z, σ z ≠ z := by
    by_contra h
    push Not at h
    exact hne (AlgEquiv.ext h)
  refine ⟨z - σ z, sub_ne_zero.mpr (Ne.symm hz), ?_⟩
  rw [map_sub, hσσ, neg_sub]

end RootInv

namespace AltPrimaryData

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : LinearMap.BilinForm K V} {x : LinearMap.GeneralLinearGroup K V}

section SelfDual

variable (H : AltPrimaryData B x) {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V))
  (hself : reciprocalPolynomial a = a) [Fact (Irreducible a)]
include H ha hself

theorem smul_adjoint (e : AdjoinRoot a) (v w : primaryComponent (x : Module.End K V) a) :
    B ((e • v : primaryComponent (x : Module.End K V) a) : V) (w : V) =
      B (v : V) ((rootInv (H.coeff_zero_ne ha) hself e • w :
        primaryComponent (x : Module.End K V) a) : V) := by
  set h0 := H.coeff_zero_ne ha
  set θ := rootInv h0 hself with hθ
  let P : AdjoinRoot a → Prop := fun e => ∀ v w : primaryComponent (x : Module.End K V) a,
    B ((e • v : primaryComponent (x : Module.End K V) a) : V) (w : V) =
      B (v : V) ((θ e • w : primaryComponent (x : Module.End K V) a) : V)
  have hP_alg : ∀ c : K, P (algebraMap K (AdjoinRoot a) c) := by
    intro c v w
    rw [AlgEquiv.commutes, coe_algebraMap_smul_primaryComponent,
      coe_algebraMap_smul_primaryComponent, LinearMap.map_smul₂, map_smul]
  have hρ : (AdjoinRoot.root a) ≠ 0 := root_ne_zero h0
  have hP_root : P (AdjoinRoot.root a) := by
    intro v w
    rw [show θ (AdjoinRoot.root a) = (AdjoinRoot.root a)⁻¹ from rootInv_root h0 hself,
      coe_root_smul_primaryComponent, bilin_apply_left_eq (Units.mul_inv x) H.isom_apply]
    congr 1
    have h2 : ((AdjoinRoot.root a • (AdjoinRoot.root a)⁻¹ • w :
        primaryComponent (x : Module.End K V) a) : V) = (w : V) := by
      rw [smul_inv_smul₀ hρ]
    rw [coe_root_smul_primaryComponent] at h2
    rw [← h2, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]
    rfl
  have hP_add : ∀ e e', P e → P e' → P (e + e') := by
    intro e e' he he' v w
    rw [add_smul, map_add, add_smul, Submodule.coe_add, map_add, LinearMap.add_apply,
      he v w, he' v w, Submodule.coe_add, map_add]
  have hP_mul : ∀ e e', P e → P e' → P (e * e') := by
    intro e e' he he' v w
    rw [mul_smul, he (e' • v) w, he' v (θ e • w), ← mul_smul, map_mul, mul_comm (θ e') (θ e)]
  have hP_mk : ∀ g : K[X], P (AdjoinRoot.mk a g) := by
    intro g
    induction g using Polynomial.induction_on with
    | C c => rw [AdjoinRoot.mk_C]; exact hP_alg c
    | add p q hp hq => rw [map_add]; exact hP_add _ _ hp hq
    | monomial n c hn =>
      rw [pow_succ, ← mul_assoc, map_mul, AdjoinRoot.mk_X]
      exact hP_mul _ _ hn hP_root
  induction e using AdjoinRoot.induction_on with
  | _ g => exact hP_mk g v w

variable [Finite K]

theorem selfDualVal_smul_left (c : AdjoinRoot a) (v w : primaryComponent (x : Module.End K V) a) :
    selfDualVal B (x : Module.End K V) a (c • v) w =
      rootInv (H.coeff_zero_ne ha) hself c * selfDualVal B (x : Module.End K V) a v w := by
  rw [selfDualVal_eq_iff]
  intro b
  have h1 := selfDualVal_spec (B := B) v w (rootInv (H.coeff_zero_ne ha) hself c * b)
  rw [mul_smul, ← H.smul_adjoint ha hself c v (b • w)] at h1
  rw [show rootInv (H.coeff_zero_ne ha) hself c * selfDualVal B (x : Module.End K V) a v w * b =
    selfDualVal B (x : Module.End K V) a v w * (rootInv (H.coeff_zero_ne ha) hself c * b) by ring]
  exact h1

theorem selfDualVal_skew (v w : primaryComponent (x : Module.End K V) a) :
    selfDualVal B (x : Module.End K V) a w v =
      -rootInv (H.coeff_zero_ne ha) hself (selfDualVal B (x : Module.End K V) a v w) := by
  rw [selfDualVal_eq_iff]
  intro b
  set σ := rootInv (H.coeff_zero_ne ha) hself with hσ
  have h1 : B (w : V) ((b • v : primaryComponent (x : Module.End K V) a) : V) =
      -B ((b • v : primaryComponent (x : Module.End K V) a) : V) (w : V) := H.skew _ _
  rw [neg_mul, map_neg, h1, H.smul_adjoint ha hself b v w,
    ← selfDualVal_spec (B := B) v w (σ b),
    ← Algebra.trace_eq_of_algEquiv σ (selfDualVal B (x : Module.End K V) a v w * σ b),
    map_mul σ, rootInv_rootInv]

variable (σ : AdjoinRoot a →+* AdjoinRoot a)
  (hσ : ∀ z, σ z = rootInv (H.coeff_zero_ne ha) hself z)

@[expose] noncomputable def altHermForm (η : AdjoinRoot a) :
    primaryComponent (x : Module.End K V) a →ₛₗ[σ]
      primaryComponent (x : Module.End K V) a →ₗ[AdjoinRoot a] AdjoinRoot a :=
  LinearMap.mk₂'ₛₗ σ (RingHom.id _) (fun v w => η * selfDualVal B (x : Module.End K V) a v w)
    (fun v₁ v₂ w => by rw [selfDualVal_add_left, mul_add])
    (fun c v w => by
      rw [H.selfDualVal_smul_left ha hself, ← hσ, smul_eq_mul]
      ring)
    (fun v w₁ w₂ => by rw [selfDualVal_add_right, mul_add])
    (fun c v w => by
      rw [selfDualVal_smul_right, RingHom.id_apply, smul_eq_mul]
      ring)

theorem altHermForm_apply (η : AdjoinRoot a) (v w : primaryComponent (x : Module.End K V) a) :
    H.altHermForm ha hself σ hσ η v w = η * selfDualVal B (x : Module.End K V) a v w := rfl

theorem altHermForm_isSymm {η : AdjoinRoot a} (hη : σ η = -η) :
    (H.altHermForm ha hself σ hσ η).IsSymm :=
  ⟨fun v w => by
    rw [altHermForm_apply, altHermForm_apply, map_mul, hη, hσ, H.selfDualVal_skew ha hself v w]
    ring⟩

theorem altHermForm_separatingLeft {η : AdjoinRoot a} (hη0 : η ≠ 0) :
    (H.altHermForm ha hself σ hσ η).SeparatingLeft := by
  intro v hv
  refine Subtype.ext (H.eq_zero_of_perfect_left ha v.2 fun w hw => ?_)
  have hw' : w ∈ primaryComponent (x : Module.End K V) a := by rwa [hself] at hw
  have h1 := hv ⟨w, hw'⟩
  rw [altHermForm_apply] at h1
  have h2 : selfDualVal B (x : Module.End K V) a v ⟨w, hw'⟩ = 0 :=
    (mul_eq_zero.mp h1).resolve_left hη0
  have h3 := selfDualVal_spec (B := B) v ⟨w, hw'⟩ 1
  rw [h2, zero_mul, map_zero, one_smul] at h3
  exact h3.symm

theorem trace_altHermForm (η : AdjoinRoot a) (v w : primaryComponent (x : Module.End K V) a)
    (c : AdjoinRoot a) :
    Algebra.trace K (AdjoinRoot a) (c * H.altHermForm ha hself σ hσ η v w) =
      B (v : V) (((c * η) • w : primaryComponent (x : Module.End K V) a) : V) := by
  rw [altHermForm_apply, ← selfDualVal_spec (B := B) v w (c * η)]
  congr 1
  ring

theorem mem_sesqUnitaryGroup_altHermForm_iff {η : AdjoinRoot a} (hη0 : η ≠ 0)
    (γ : blockGL (x : Module.End K V) a) :
    γ ∈ sesqUnitaryGroup (H.altHermForm ha hself σ hσ η) ↔
      ∀ v w : primaryComponent (x : Module.End K V) a,
        B (((γ : Module.End (AdjoinRoot a) (primaryComponent (x : Module.End K V) a)) v :
          primaryComponent (x : Module.End K V) a) : V)
          (((γ : Module.End (AdjoinRoot a) (primaryComponent (x : Module.End K V) a)) w :
          primaryComponent (x : Module.End K V) a) : V) = B (v : V) (w : V) := by
  rw [mem_sesqUnitaryGroup]
  constructor
  · intro h v w
    have h1 := h v w
    rw [altHermForm_apply, altHermForm_apply] at h1
    have h2 := mul_left_cancel₀ hη0 h1
    have e1 := selfDualVal_spec (B := B)
      ((γ : Module.End (AdjoinRoot a) (primaryComponent (x : Module.End K V) a)) v)
      ((γ : Module.End (AdjoinRoot a) (primaryComponent (x : Module.End K V) a)) w) 1
    have e2 := selfDualVal_spec (B := B) v w 1
    rw [one_smul] at e1 e2
    rw [← e1, ← e2, h2]
  · intro h v w
    rw [altHermForm_apply, altHermForm_apply]
    congr 1
    rw [selfDualVal_eq_iff]
    intro b
    rw [← map_smul (γ : Module.End (AdjoinRoot a) (primaryComponent (x : Module.End K V) a)) b w,
      h v (b • w), selfDualVal_spec]

theorem blockRestrict_mem_altHerm {η : AdjoinRoot a} (hη0 : η ≠ 0)
    (g : supportedUnitary B x {a}) :
    blockRestrict H.squarefree {a} ⟨a, ha⟩ g ∈
      sesqUnitaryGroup (H.altHermForm ha hself σ hσ η) := by
  rw [H.mem_sesqUnitaryGroup_altHermForm_iff ha hself σ hσ hη0]
  intro v w
  exact mem_sesqUnitaryGroup.mp (mem_unitaryCentralizer.mp g.2.1).1 (v : V) (w : V)

theorem blockRestrict_injective_of_selfDual {η : AdjoinRoot a} (hη0 : η ≠ 0) :
    Function.Injective ((blockRestrict H.squarefree {a} ⟨a, ha⟩).codRestrict
      (sesqUnitaryGroup (H.altHermForm ha hself σ hσ η))
      (H.blockRestrict_mem_altHerm ha hself σ hσ hη0)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply Subtype.ext
  refine eq_one_of_forall_apply_eq H.squarefree fun b hb v hv => ?_
  by_cases hba : b = a
  · subst hba
    have h1 := congrArg (fun γ : blockGL (x : Module.End K V) b =>
      ((γ : Module.End (AdjoinRoot b) (primaryComponent (x : Module.End K V) b)) ⟨v, hv⟩ :
        primaryComponent (x : Module.End K V) b)) (congrArg Subtype.val hg)
    exact congrArg Subtype.val h1
  · exact g.2.2 b hb (by simpa using hba) v hv

theorem blockRestrict_surjective_of_selfDual {η : AdjoinRoot a} (hη0 : η ≠ 0) :
    Function.Surjective ((blockRestrict H.squarefree {a} ⟨a, ha⟩).codRestrict
      (sesqUnitaryGroup (H.altHermForm ha hself σ hσ η))
      (H.blockRestrict_mem_altHerm ha hself σ hσ hη0)) := by
  classical
  rintro ⟨γ, hγ⟩
  have hsq := H.squarefree
  let ia : primaryFactors (x : Module.End K V) := ⟨a, ha⟩
  let Γ : (b : primaryFactors (x : Module.End K V)) → blockGL (x : Module.End K V) (b : K[X]) :=
    Function.update 1 ia γ
  let g : gl_centralizer x := (glCentralizerEquivPi hsq).symm Γ
  have hga : ∀ (v : V) (hv : v ∈ primaryComponent (x : Module.End K V) a),
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = blockApply γ v hv :=
    fun v hv => by rw [glue_apply_of_mem hsq Γ ia hv]; simp [Γ, ia]
  have hgo : ∀ c ∈ primaryFactors (x : Module.End K V), c ≠ a →
      ∀ v ∈ primaryComponent (x : Module.End K V) c,
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v := by
    intro c hc hca v hv
    rw [glue_apply_of_mem hsq Γ ⟨c, hc⟩ hv]
    have hne : (⟨c, hc⟩ : primaryFactors (x : Module.End K V)) ≠ ia :=
      fun h => hca (congrArg Subtype.val h)
    have : Γ ⟨c, hc⟩ = 1 := by
      simp only [Γ, Function.update_of_ne hne]
      rfl
    rw [this, blockApply_one]
  have hmem : (g : LinearMap.GeneralLinearGroup K V) ∈ supportedUnitary B x {a} := by
    refine ⟨(H.mem_unitaryCentralizer_iff_blocks).mpr ⟨mem_gl_centralizer.mp g.2, ?_⟩, ?_⟩
    · intro c hc v hv w hw
      by_cases hca : c = a
      · subst hca
        rw [hself] at hw
        rw [hga v hv, hga w hw]
        exact (H.mem_sesqUnitaryGroup_altHermForm_iff ha hself σ hσ hη0 γ).mp hγ ⟨v, hv⟩ ⟨w, hw⟩
      · have hc2 : reciprocalPolynomial c ≠ a := fun h => hca (by
          rw [← H.reciprocal_reciprocal hc, h, hself])
        rw [hgo c hc hca v hv, hgo (reciprocalPolynomial c) (H.reciprocal_mem hc) hc2 w hw]
    · intro c hc hcS v hv
      exact hgo c hc (fun h => hcS (by simp [h])) v hv
  refine ⟨⟨(g : LinearMap.GeneralLinearGroup K V), hmem⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact hga v v.2

@[expose] noncomputable def selfDualEquiv {η : AdjoinRoot a} (hη0 : η ≠ 0) :
    supportedUnitary B x {a} ≃* sesqUnitaryGroup (H.altHermForm ha hself σ hσ η) :=
  MulEquiv.ofBijective ((blockRestrict H.squarefree {a} ⟨a, ha⟩).codRestrict
      (sesqUnitaryGroup (H.altHermForm ha hself σ hσ η))
      (H.blockRestrict_mem_altHerm ha hself σ hσ hη0))
    ⟨H.blockRestrict_injective_of_selfDual ha hself σ hσ hη0,
      H.blockRestrict_surjective_of_selfDual ha hself σ hσ hη0⟩

theorem blockApply_selfDualEquiv {η : AdjoinRoot a} (hη0 : η ≠ 0) (g : supportedUnitary B x {a})
    (v : V) (hv : v ∈ primaryComponent (x : Module.End K V) a) :
    blockApply ((H.selfDualEquiv ha hself σ hσ hη0 g :
        sesqUnitaryGroup (H.altHermForm ha hself σ hσ η)) :
      blockGL (x : Module.End K V) a) v hv =
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v := rfl

end SelfDual

end AltPrimaryData

section Fixed

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem primaryComponent_X_sub_one (y : Module.End K V) :
    primaryComponent y (X - 1) = LinearMap.ker (y - 1) := by
  rw [primaryComponent, map_sub, aeval_X, map_one]

theorem mem_primaryComponent_X_sub_one {y : Module.End K V} {v : V} :
    v ∈ primaryComponent y (X - 1) ↔ y v = v := by
  rw [primaryComponent_X_sub_one, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
    sub_eq_zero]

theorem mk_X_sub_one_eq (g : K[X]) :
    AdjoinRoot.mk (X - 1) g = algebraMap K (AdjoinRoot (X - 1 : K[X])) (g.eval 1) := by
  rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, AdjoinRoot.mk_eq_mk]
  have := Polynomial.X_sub_C_dvd_sub_C_eval (a := (1 : K)) (p := g)
  rwa [C_1] at this

@[expose] noncomputable def fixedBlockEnd (y : Module.End K V) :
    Module.End K (primaryComponent y (X - 1)) →* Module.End (AdjoinRoot (X - 1 : K[X]))
      (primaryComponent y (X - 1)) where
  toFun f :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun e v => by
        induction e using AdjoinRoot.induction_on with
        | _ g =>
          rw [RingHom.id_apply, mk_X_sub_one_eq, algebraMap_smul, algebraMap_smul, map_smul] }
  map_one' := LinearMap.ext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun _ => rfl

theorem fixedBlockEnd_apply (y : Module.End K V) (f : Module.End K (primaryComponent y (X - 1)))
    (v : primaryComponent y (X - 1)) : fixedBlockEnd y f v = f v := rfl

@[expose] noncomputable def restrictK (x : LinearMap.GeneralLinearGroup K V) (a : K[X]) :
    gl_centralizer x →* LinearMap.GeneralLinearGroup K (primaryComponent (x : Module.End K V) a)
    where
  toFun g :=
    ⟨((g : LinearMap.GeneralLinearGroup K V) : Module.End K V).restrict fun _ hv =>
        apply_mem_primaryComponent (mem_gl_centralizer.mp g.2) hv,
      (((g⁻¹ : gl_centralizer x) : LinearMap.GeneralLinearGroup K V) : Module.End K V).restrict
        fun _ hv => apply_mem_primaryComponent (mem_gl_centralizer.mp (g⁻¹).2) hv,
      LinearMap.ext fun v => Subtype.ext (by
        change ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V)
          ((((g⁻¹ : gl_centralizer x) : LinearMap.GeneralLinearGroup K V) : Module.End K V) v) = v
        rw [← Module.End.mul_apply, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
        rfl),
      LinearMap.ext fun v => Subtype.ext (by
        change (((g⁻¹ : gl_centralizer x) : LinearMap.GeneralLinearGroup K V) : Module.End K V)
          (((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v) = v
        rw [← Module.End.mul_apply, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
        rfl)⟩
  map_one' := Units.ext (LinearMap.ext fun _ => rfl)
  map_mul' _ _ := Units.ext (LinearMap.ext fun _ => rfl)

theorem coe_restrictK_apply (x : LinearMap.GeneralLinearGroup K V) (a : K[X])
    (g : gl_centralizer x) (v : primaryComponent (x : Module.End K V) a) :
    (((restrictK x a g : LinearMap.GeneralLinearGroup K (primaryComponent (x : Module.End K V) a)) :
      Module.End K (primaryComponent (x : Module.End K V) a)) v : V) =
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v := rfl

namespace AltPrimaryData

variable [FiniteDimensional K V] {B : LinearMap.BilinForm K V}
  {x : LinearMap.GeneralLinearGroup K V} (H : AltPrimaryData B x)
include H

theorem nondegenerate_restrict_fixed (h1 : (X - 1 : K[X]) ∈ primaryFactors (x : Module.End K V)) :
    (B.restrict (primaryComponent (x : Module.End K V) (X - 1))).Nondegenerate := by
  have hself : reciprocalPolynomial (X - 1 : K[X]) = X - 1 := reciprocalPolynomial_X_sub_one
  have hleft : ∀ v : primaryComponent (x : Module.End K V) (X - 1),
      (∀ w, B.restrict (primaryComponent (x : Module.End K V) (X - 1)) v w = 0) → v = 0 := by
    intro v hv
    refine Subtype.ext (H.eq_zero_of_perfect_left h1 v.2 fun w hw => ?_)
    rw [hself] at hw
    exact hv ⟨w, hw⟩
  refine ⟨hleft, fun w hw => hleft w fun v => ?_⟩
  have h2 : B (v : V) (w : V) = 0 := hw v
  change B (w : V) (v : V) = 0
  rw [H.skew, h2, neg_zero]

theorem even_finrank_fixed (h1 : (X - 1 : K[X]) ∈ primaryFactors (x : Module.End K V)) :
    Even (finrank K (primaryComponent (x : Module.End K V) (X - 1))) :=
  LinearMap.BilinForm.IsAlt.even_finrank (fun v => H.alt v) (H.nondegenerate_restrict_fixed h1)

omit [FiniteDimensional K V] H in
theorem restrictK_mem_fixed (g : supportedUnitary B x {X - 1}) :
    restrictK x (X - 1) ⟨g, supportedUnitary_le_gl_centralizer _ g.2⟩ ∈
      sesqUnitaryGroup (B.restrict (primaryComponent (x : Module.End K V) (X - 1))) := by
  rw [mem_sesqUnitaryGroup]
  intro v w
  exact mem_sesqUnitaryGroup.mp (mem_unitaryCentralizer.mp g.2.1).1 (v : V) (w : V)

omit [FiniteDimensional K V] H in
@[expose] noncomputable def fixedHom :
    supportedUnitary B x {X - 1} →*
      sesqUnitaryGroup (B.restrict (primaryComponent (x : Module.End K V) (X - 1))) :=
  ((restrictK x (X - 1)).comp
    (Subgroup.inclusion (supportedUnitary_le_gl_centralizer _))).codRestrict _ restrictK_mem_fixed

theorem fixedHom_bijective (h1 : (X - 1 : K[X]) ∈ primaryFactors (x : Module.End K V)) :
    Function.Bijective (fixedHom (B := B) (x := x)) := by
  classical
  have hsq := H.squarefree
  have hself : reciprocalPolynomial (X - 1 : K[X]) = X - 1 := reciprocalPolynomial_X_sub_one
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro g hg
    apply Subtype.ext
    refine eq_one_of_forall_apply_eq hsq fun b hb v hv => ?_
    by_cases hba : b = X - 1
    · subst hba
      have h2 := congrArg (fun γ : sesqUnitaryGroup
          (B.restrict (primaryComponent (x : Module.End K V) (X - 1))) =>
        (((γ : LinearMap.GeneralLinearGroup K (primaryComponent (x : Module.End K V) (X - 1))) :
          Module.End K (primaryComponent (x : Module.End K V) (X - 1))) ⟨v, hv⟩ : V)) hg
      exact h2
    · exact g.2.2 b hb (by simpa using hba) v hv
  · rintro ⟨γ, hγ⟩
    let i1 : primaryFactors (x : Module.End K V) := ⟨X - 1, h1⟩
    let γE : blockGL (x : Module.End K V) (X - 1) := Units.map (fixedBlockEnd _) γ
    let Γ : (b : primaryFactors (x : Module.End K V)) →
        blockGL (x : Module.End K V) (b : K[X]) := Function.update 1 i1 γE
    let g : gl_centralizer x := (glCentralizerEquivPi hsq).symm Γ
    have hga : ∀ (v : V) (hv : v ∈ primaryComponent (x : Module.End K V) (X - 1)),
        ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v =
          (((γ : LinearMap.GeneralLinearGroup K (primaryComponent (x : Module.End K V) (X - 1))) :
            Module.End K (primaryComponent (x : Module.End K V) (X - 1))) ⟨v, hv⟩ : V) :=
      fun v hv => by rw [glue_apply_of_mem hsq Γ i1 hv]; simp [Γ, i1]; rfl
    have hgo : ∀ c ∈ primaryFactors (x : Module.End K V), c ≠ X - 1 →
        ∀ v ∈ primaryComponent (x : Module.End K V) c,
        ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v := by
      intro c hc hca v hv
      rw [glue_apply_of_mem hsq Γ ⟨c, hc⟩ hv]
      have hne : (⟨c, hc⟩ : primaryFactors (x : Module.End K V)) ≠ i1 :=
        fun h => hca (congrArg Subtype.val h)
      have : Γ ⟨c, hc⟩ = 1 := by
        simp only [Γ, Function.update_of_ne hne]
        rfl
      rw [this, blockApply_one]
    have hmem : (g : LinearMap.GeneralLinearGroup K V) ∈ supportedUnitary B x {X - 1} := by
      refine ⟨(H.mem_unitaryCentralizer_iff_blocks).mpr ⟨mem_gl_centralizer.mp g.2, ?_⟩, ?_⟩
      · intro c hc v hv w hw
        by_cases hca : c = X - 1
        · subst hca
          rw [hself] at hw
          rw [hga v hv, hga w hw]
          exact mem_sesqUnitaryGroup.mp hγ ⟨v, hv⟩ ⟨w, hw⟩
        · have hc2 : reciprocalPolynomial c ≠ X - 1 := fun h => hca (by
            rw [← H.reciprocal_reciprocal hc, h, hself])
          rw [hgo c hc hca v hv, hgo (reciprocalPolynomial c) (H.reciprocal_mem hc) hc2 w hw]
      · intro c hc hcS v hv
        exact hgo c hc (fun h => hcS (by simp [h])) v hv
    refine ⟨⟨(g : LinearMap.GeneralLinearGroup K V), hmem⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact hga v v.2

@[expose] noncomputable def fixedEquiv (h1 : (X - 1 : K[X]) ∈ primaryFactors (x : Module.End K V)) :
    supportedUnitary B x {X - 1} ≃*
      sesqUnitaryGroup (B.restrict (primaryComponent (x : Module.End K V) (X - 1))) :=
  MulEquiv.ofBijective fixedHom (H.fixedHom_bijective h1)

theorem fixedEquiv_apply (h1 : (X - 1 : K[X]) ∈ primaryFactors (x : Module.End K V))
    (g : supportedUnitary B x {X - 1})
    (v : primaryComponent (x : Module.End K V) (X - 1)) :
    ((((H.fixedEquiv h1 g : sesqUnitaryGroup
        (B.restrict (primaryComponent (x : Module.End K V) (X - 1)))) :
      LinearMap.GeneralLinearGroup K (primaryComponent (x : Module.End K V) (X - 1))) :
        Module.End K (primaryComponent (x : Module.End K V) (X - 1))) v : V) =
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v := rfl

end AltPrimaryData

end Fixed

end CFSG.RankThree.Classical

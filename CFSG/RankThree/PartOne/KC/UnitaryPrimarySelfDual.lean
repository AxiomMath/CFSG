module

public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryCentralizer
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryField

public section

namespace CFSG.RankThree.PartOne.KCUnitary

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary

section TraceDual

variable {K : Type*} [Field K] [Finite K] {a : K[X]} [Fact (Irreducible a)]

theorem eq_of_trace_eq {z z' : AdjoinRoot a}
    (h : ∀ b, Algebra.trace K (AdjoinRoot a) (z * b) =
      Algebra.trace K (AdjoinRoot a) (z' * b)) : z = z' := by
  have : Finite (AdjoinRoot a) := Module.finite_of_finite K
  have hnd := traceForm_nondegenerate K (AdjoinRoot a)
  refine sub_eq_zero.mp (hnd.1 (z - z') fun y => ?_)
  rw [Algebra.traceForm_apply, sub_mul, map_sub, h y, sub_self]

theorem exists_trace_dual (φ : Module.Dual K (AdjoinRoot a)) :
    ∃ z : AdjoinRoot a, ∀ b, Algebra.trace K (AdjoinRoot a) (z * b) = φ b := by
  have : Finite (AdjoinRoot a) := Module.finite_of_finite K
  have hnd := traceForm_nondegenerate K (AdjoinRoot a)
  obtain ⟨z, hz⟩ := ((Algebra.traceForm K (AdjoinRoot a)).toDual hnd).surjective φ
  refine ⟨z, fun b => ?_⟩
  have := LinearMap.congr_fun hz b
  rw [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply] at this
  exact this

end TraceDual

section TraceValue

variable {K : Type*} [Field K] [Finite K] {σ : K →+* K} {V : Type*} [AddCommGroup V]
  [Module K V] {B : V →ₛₗ[σ] V →ₗ[K] K} {x : Module.End K V} {a : K[X]} [Fact (Irreducible a)]

@[expose] noncomputable def traceFunctional (B : V →ₛₗ[σ] V →ₗ[K] K) (x : Module.End K V)
    (a : K[X]) (v w : primaryComponent x a) : Module.Dual K (AdjoinRoot a) where
  toFun b := B (v : V) ((b • w : primaryComponent x a) : V)
  map_add' b b' := by rw [add_smul, Submodule.coe_add, map_add]
  map_smul' c b := by
    rw [smul_assoc, Submodule.coe_smul, map_smul]
    rfl

@[expose] noncomputable def selfDualVal (B : V →ₛₗ[σ] V →ₗ[K] K) (x : Module.End K V)
    (a : K[X]) [Fact (Irreducible a)] (v w : primaryComponent x a) : AdjoinRoot a :=
  (exists_trace_dual (traceFunctional B x a v w)).choose

theorem selfDualVal_spec (v w : primaryComponent x a) (b : AdjoinRoot a) :
    Algebra.trace K (AdjoinRoot a) (selfDualVal B x a v w * b) =
      B (v : V) ((b • w : primaryComponent x a) : V) :=
  (exists_trace_dual (traceFunctional B x a v w)).choose_spec b

theorem selfDualVal_eq_iff (v w : primaryComponent x a) (z : AdjoinRoot a) :
    selfDualVal B x a v w = z ↔ ∀ b : AdjoinRoot a, Algebra.trace K (AdjoinRoot a) (z * b) =
      B (v : V) ((b • w : primaryComponent x a) : V) := by
  constructor
  · rintro rfl b
    exact selfDualVal_spec v w b
  · intro h
    exact eq_of_trace_eq fun b => by rw [selfDualVal_spec v w b, h b]

theorem selfDualVal_add_left (v₁ v₂ w : primaryComponent x a) :
    selfDualVal B x a (v₁ + v₂) w = selfDualVal B x a v₁ w + selfDualVal B x a v₂ w := by
  rw [selfDualVal_eq_iff]
  intro b
  rw [add_mul, map_add, selfDualVal_spec, selfDualVal_spec, Submodule.coe_add, map_add,
    LinearMap.add_apply]

theorem selfDualVal_add_right (v w₁ w₂ : primaryComponent x a) :
    selfDualVal B x a v (w₁ + w₂) = selfDualVal B x a v w₁ + selfDualVal B x a v w₂ := by
  rw [selfDualVal_eq_iff]
  intro b
  rw [add_mul, map_add, selfDualVal_spec, selfDualVal_spec, smul_add, Submodule.coe_add, map_add]

theorem selfDualVal_smul_right (c : AdjoinRoot a) (v w : primaryComponent x a) :
    selfDualVal B x a v (c • w) = c * selfDualVal B x a v w := by
  rw [selfDualVal_eq_iff]
  intro b
  have h1 := selfDualVal_spec (B := B) v w (b * c)
  rw [mul_smul] at h1
  rw [show c * selfDualVal B x a v w * b = selfDualVal B x a v w * (b * c) by ring]
  exact h1

end TraceValue

section SelfDual

variable {ℓ f : ℕ} {K : Type*} [Field K] [Finite K] (hK : UnitaryFieldData ℓ f K)
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}
  (H : UnitaryPrimaryData hK.bar B x)
  {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V))
  (hself : dualPoly hK.bar a = a) [Fact (Irreducible a)]
include H ha hself

omit [Finite K] in
theorem smul_adjoint
    (e : AdjoinRoot a) (v w : primaryComponent (x : Module.End K V) a) :
    B ((e • v : primaryComponent (x : Module.End K V) a) : V) (w : V) =
      B (v : V) ((theta hK.bar a (coeff_zero_ne_zero_of_mem_primaryFactors H.squarefree ha) hself e
        • w : primaryComponent (x : Module.End K V) a) : V) := by
  set h0 := coeff_zero_ne_zero_of_mem_primaryFactors H.squarefree ha with hh0
  set θ := theta hK.bar a h0 hself with hθ
  let P : AdjoinRoot a → Prop := fun e => ∀ v w : primaryComponent (x : Module.End K V) a,
    B ((e • v : primaryComponent (x : Module.End K V) a) : V) (w : V) =
      B (v : V) ((θ e • w : primaryComponent (x : Module.End K V) a) : V)
  have hP_alg : ∀ c : K, P (algebraMap K (AdjoinRoot a) c) := by
    intro c v w
    rw [theta_algebraMap h0 hself, coe_algebraMap_smul_primaryComponent,
      coe_algebraMap_smul_primaryComponent, map_smulₛₗ, map_smul]
    rfl
  have hρ : (AdjoinRoot.root a) ≠ 0 := root_ne_zero h0
  have hP_root : P (AdjoinRoot.root a) := by
    intro v w
    rw [theta_root h0 hself, coe_root_smul_primaryComponent]
    have h1 : B ((x : Module.End K V) (v : V)) (w : V) =
        B (v : V) (H.adj (x : Module.End K V) (w : V)) := H.adj_spec _ _ _
    have hadj : H.adj (x : Module.End K V) =
        ((x⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) :=
      hermAdjoint_of_mem_sesqUnitaryGroup H.symm H.sep H.isom
    rw [h1, hadj]
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
  have hP_one : P 1 := by
    have := hP_alg 1
    rwa [map_one] at this
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



omit [Finite K] in
theorem smul_adjoint_bar (e : AdjoinRoot a) (v w : primaryComponent (x : Module.End K V) a) :
    B ((e • v : primaryComponent (x : Module.End K V) a) : V) (w : V) =
      B (v : V) (((unitaryFieldData_adjoinRoot hK (a := a)).bar e • w :
        primaryComponent (x : Module.End K V) a) : V) := by
  rw [smul_adjoint hK H ha hself e v w, theta_eq_bar hK _ hself e]

theorem trace_bar (z : AdjoinRoot a) :
    Algebra.trace K (AdjoinRoot a) ((unitaryFieldData_adjoinRoot hK (a := a)).bar z) =
      hK.bar (Algebra.trace K (AdjoinRoot a) z) := by
  rw [← theta_eq_bar hK (coeff_zero_ne_zero_of_mem_primaryFactors H.squarefree ha) hself]
  exact trace_theta _ hself z


theorem selfDualVal_smul_left (c : AdjoinRoot a) (v w : primaryComponent (x : Module.End K V) a) :
    selfDualVal B x a (c • v) w =
      (unitaryFieldData_adjoinRoot hK (a := a)).bar c * selfDualVal B x a v w := by
  rw [selfDualVal_eq_iff]
  intro b
  have h1 := selfDualVal_spec (B := B) v w ((unitaryFieldData_adjoinRoot hK (a := a)).bar c * b)
  rw [mul_smul, ← smul_adjoint_bar hK H ha hself c v (b • w)] at h1
  rw [show (unitaryFieldData_adjoinRoot hK (a := a)).bar c * selfDualVal B x a v w * b =
    selfDualVal B x a v w * ((unitaryFieldData_adjoinRoot hK (a := a)).bar c * b) by ring]
  exact h1

theorem selfDualVal_symm (v w : primaryComponent (x : Module.End K V) a) :
    (unitaryFieldData_adjoinRoot hK (a := a)).bar (selfDualVal B x a v w) =
      selfDualVal B x a w v := by
  symm
  rw [selfDualVal_eq_iff]
  intro b
  have h1 := H.symm.eq ((b • v : primaryComponent (x : Module.End K V) a) : V) (w : V)
  rw [← h1, smul_adjoint_bar hK H ha hself b v w,
    ← selfDualVal_spec (B := B) v w ((unitaryFieldData_adjoinRoot hK (a := a)).bar b),
    ← trace_bar hK H ha hself, RingHom.map_mul,
    (unitaryFieldData_adjoinRoot hK (a := a)).bar_bar]


@[expose] noncomputable def selfDualForm :
    primaryComponent (x : Module.End K V) a →ₛₗ[(unitaryFieldData_adjoinRoot hK (a := a)).bar]
      primaryComponent (x : Module.End K V) a →ₗ[AdjoinRoot a] AdjoinRoot a :=
  LinearMap.mk₂'ₛₗ _ (RingHom.id _) (selfDualVal B (x : Module.End K V) a)
    selfDualVal_add_left (selfDualVal_smul_left hK H ha hself) selfDualVal_add_right
    selfDualVal_smul_right

theorem selfDualForm_apply (v w : primaryComponent (x : Module.End K V) a) :
    selfDualForm hK H ha hself v w = selfDualVal B (x : Module.End K V) a v w := rfl

theorem selfDualForm_isSymm : (selfDualForm hK H ha hself).IsSymm :=
  ⟨fun v w => selfDualVal_symm hK H ha hself v w⟩

theorem trace_selfDualForm (v w : primaryComponent (x : Module.End K V) a) (b : AdjoinRoot a) :
    Algebra.trace K (AdjoinRoot a) (b * selfDualForm hK H ha hself v w) =
      B (v : V) ((b • w : primaryComponent (x : Module.End K V) a) : V) := by
  rw [mul_comm]
  exact selfDualVal_spec v w b

theorem apply_eq_trace_selfDualForm (v w : primaryComponent (x : Module.End K V) a) :
    B (v : V) (w : V) = Algebra.trace K (AdjoinRoot a) (selfDualForm hK H ha hself v w) := by
  have := trace_selfDualForm hK H ha hself v w 1
  rw [one_mul, one_smul] at this
  exact this.symm

theorem selfDualForm_separatingLeft : (selfDualForm hK H ha hself).SeparatingLeft := by
  intro v hv
  refine separatingLeft_primaryComponent_selfDual H ha hself v fun w => ?_
  change B (v : V) (w : V) = 0
  rw [apply_eq_trace_selfDualForm hK H ha hself, hv w, map_zero]


theorem mem_sesqUnitaryGroup_selfDualForm_iff (γ : blockGL (x : Module.End K V) a) :
    γ ∈ sesqUnitaryGroup (selfDualForm hK H ha hself) ↔
      ∀ v w : primaryComponent (x : Module.End K V) a,
        B (((γ : Module.End (AdjoinRoot a) (primaryComponent (x : Module.End K V) a)) v :
          primaryComponent (x : Module.End K V) a) : V)
          (((γ : Module.End (AdjoinRoot a) (primaryComponent (x : Module.End K V) a)) w :
          primaryComponent (x : Module.End K V) a) : V) = B (v : V) (w : V) := by
  rw [mem_sesqUnitaryGroup]
  constructor
  · intro h v w
    rw [apply_eq_trace_selfDualForm hK H ha hself, h v w,
      ← apply_eq_trace_selfDualForm hK H ha hself]
  · intro h v w
    change selfDualVal B (x : Module.End K V) a _ _ = selfDualVal B (x : Module.End K V) a v w
    rw [selfDualVal_eq_iff]
    intro b
    rw [← map_smul (γ : Module.End (AdjoinRoot a) (primaryComponent (x : Module.End K V) a)) b w,
      h v (b • w), selfDualVal_spec]


theorem supportedRestrict_mem_sesqUnitaryGroup (g : supportedUnitary B (x) {a}) :
    supportedRestrict H {a} ⟨a, ha⟩ g ∈ sesqUnitaryGroup (selfDualForm hK H ha hself) := by
  rw [mem_sesqUnitaryGroup_selfDualForm_iff hK H ha hself]
  intro v w
  exact (mem_unitaryCentralizer.mp g.2.1).1 (v : V) (w : V)

theorem supportedRestrict_injective_of_selfDual :
    Function.Injective ((supportedRestrict H {a} ⟨a, ha⟩).codRestrict
      (sesqUnitaryGroup (selfDualForm hK H ha hself))
      (supportedRestrict_mem_sesqUnitaryGroup hK H ha hself)) := by
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

theorem supportedRestrict_surjective_of_selfDual :
    Function.Surjective ((supportedRestrict H {a} ⟨a, ha⟩).codRestrict
      (sesqUnitaryGroup (selfDualForm hK H ha hself))
      (supportedRestrict_mem_sesqUnitaryGroup hK H ha hself)) := by
  classical
  rintro ⟨γ, hγ⟩
  have hsq := H.squarefree
  let ia : primaryFactors (x : Module.End K V) := ⟨a, ha⟩
  let Γ : (b : primaryFactors (x : Module.End K V)) → blockGL (x : Module.End K V) (b : K[X]) :=
    Function.update 1 ia γ
  let g : gl_centralizer x := (glCentralizerEquivPi hsq).symm Γ
  have hga : ∀ (v : V) (hv : v ∈ primaryComponent (x : Module.End K V) a),
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = blockApply γ v hv :=
    fun v hv => by rw [glue_apply H Γ ia hv]; simp [Γ, ia]
  have hgo : ∀ c ∈ primaryFactors (x : Module.End K V), c ≠ a →
      ∀ v ∈ primaryComponent (x : Module.End K V) c,
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v := by
    intro c hc hca v hv
    rw [glue_apply H Γ ⟨c, hc⟩ hv]
    have hne : (⟨c, hc⟩ : primaryFactors (x : Module.End K V)) ≠ ia :=
      fun h => hca (congrArg Subtype.val h)
    have : Γ ⟨c, hc⟩ = 1 := by
      simp only [Γ, Function.update_of_ne hne]
      rfl
    rw [this, blockApply_one]
  have hmem : (g : LinearMap.GeneralLinearGroup K V) ∈ supportedUnitary B x {a} := by
    refine ⟨(mem_unitaryCentralizer_iff_blocks H).mpr ⟨mem_gl_centralizer.mp g.2, ?_⟩, ?_⟩
    · intro c hc v hv w hw
      by_cases hca : c = a
      · subst hca
        rw [hself] at hw
        rw [hga v hv, hga w hw]
        exact (mem_sesqUnitaryGroup_selfDualForm_iff hK H ha hself γ).mp hγ ⟨v, hv⟩ ⟨w, hw⟩
      · have hc2 : dualPoly hK.bar c ≠ a := fun h => hca (by
          rw [← dualPoly_dualPoly_of_mem H hc, h, hself])
        rw [hgo c hc hca v hv,
          hgo (dualPoly hK.bar c) (dualPoly_mem_primaryFactors H hc) hc2 w hw]
    · intro c hc hcS v hv
      exact hgo c hc (fun h => hcS (by simp [h])) v hv
  refine ⟨⟨(g : LinearMap.GeneralLinearGroup K V), hmem⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact hga v v.2


@[expose] noncomputable def selfDualFactorEquiv :
    supportedUnitary B x {a} ≃* sesqUnitaryGroup (selfDualForm hK H ha hself) :=
  MulEquiv.ofBijective ((supportedRestrict H {a} ⟨a, ha⟩).codRestrict
      (sesqUnitaryGroup (selfDualForm hK H ha hself))
      (supportedRestrict_mem_sesqUnitaryGroup hK H ha hself))
    ⟨supportedRestrict_injective_of_selfDual hK H ha hself,
      supportedRestrict_surjective_of_selfDual hK H ha hself⟩

theorem blockApply_selfDualFactorEquiv (g : supportedUnitary B x {a}) (v : V)
    (hv : v ∈ primaryComponent (x : Module.End K V) a) :
    blockApply ((selfDualFactorEquiv hK H ha hself g :
        sesqUnitaryGroup (selfDualForm hK H ha hself)) :
      blockGL (x : Module.End K V) a) v hv =
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v := rfl

end SelfDual

end CFSG.RankThree.PartOne.KCUnitary

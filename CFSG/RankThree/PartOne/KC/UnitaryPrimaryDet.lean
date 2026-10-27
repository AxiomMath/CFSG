module

public import CFSG.RankThree.PartOne.KC.UnitaryPrimarySelfDual

public section

namespace CFSG.RankThree.PartOne.KCUnitary

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
open scoped Matrix

section DetPair

variable {K : Type*} [Field K] {σ : K →+* K} {V : Type*} [AddCommGroup V] [Module K V]
  {B : V →ₛₗ[σ] V →ₗ[K] K}

theorem det_pair {P Q : Submodule K V} [FiniteDimensional K P] [FiniteDimensional K Q]
    (hrank : Module.finrank K P = Module.finrank K Q)
    (hperf : ∀ w ∈ Q, (∀ v ∈ P, B v w = 0) → w = 0) (γ : P →ₗ[K] P) (δ : Q →ₗ[K] Q)
    (h : ∀ (v : P) (w : Q), B ((γ v : P) : V) ((δ w : Q) : V) = B (v : V) (w : V)) :
    σ (LinearMap.det γ) * LinearMap.det δ = 1 := by
  classical
  let e := Module.finBasis K P
  let Φ : Q →ₗ[K] (Fin (Module.finrank K P) → K) :=
    LinearMap.pi fun i => (B (e i : V)).comp Q.subtype
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have hi : ∀ i, B (e i : V) (w : V) = 0 := fun i => congrFun hw i
    refine Subtype.ext (hperf w w.2 fun v hv => ?_)
    have hv' : v = ∑ i, e.repr ⟨v, hv⟩ i • (e i : V) := by
      have h2 := congrArg (fun p : P => (p : V)) (e.sum_repr ⟨v, hv⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
      exact h2.symm
    rw [hv', map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smulₛₗ, LinearMap.smul_apply, hi i, smul_zero]
  have hΦb : Function.Bijective Φ :=
    ⟨hΦ, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simp [hrank])).mp hΦ⟩
  let Φe := LinearEquiv.ofBijective Φ hΦb
  let e' : Basis (Fin (Module.finrank K P)) K Q := (Pi.basisFun K _).map Φe.symm
  have he' : ∀ i j, B (e i : V) (e' j : V) = if i = j then 1 else 0 := by
    intro i j
    have := congrFun (Φe.apply_symm_apply (Pi.single j 1)) i
    change B (e i : V) ((Φe.symm (Pi.single j 1) : Q) : V) = _ at this
    have he'j : e' j = Φe.symm (Pi.single j 1) := by simp [e']
    rw [he'j, this, Pi.single_apply]
  let M := LinearMap.toMatrix e e γ
  let N := LinearMap.toMatrix e' e' δ
  have hγ : ∀ i, ((γ (e i) : P) : V) = ∑ k, M k i • (e k : V) := by
    intro i
    have h1 := congrArg (fun p : P => (p : V)) ((e.sum_repr (γ (e i))).symm)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    simpa [M, LinearMap.toMatrix_apply] using h1
  have hδ : ∀ j, ((δ (e' j) : Q) : V) = ∑ l, N l j • (e' l : V) := by
    intro j
    have h1 := congrArg (fun p : Q => (p : V)) ((e'.sum_repr (δ (e' j))).symm)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    simpa [N, LinearMap.toMatrix_apply] using h1
  have hexp : ∀ i j, B (∑ k, M k i • (e k : V)) (∑ l, N l j • (e' l : V)) =
      ∑ k, σ (M k i) * N k j := by
    intro i j
    rw [map_sum B (fun k => M k i • (e k : V)) Finset.univ, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ, LinearMap.smul_apply, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [Finset.sum_eq_single k]
    · rw [he' k k]
      simp
    · intro l _ hl
      rw [he' k l]
      simp [Ne.symm hl]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  have hMN : (M.map σ)ᵀ * N = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply, ← he' i j, ← h (e i) (e' j), hγ i, hδ j, hexp i j]
    rfl
  have h2 : (M.map σ).det = σ M.det := by rw [RingHom.map_det]; rfl
  have := congrArg Matrix.det hMN
  rw [Matrix.det_mul, Matrix.det_transpose, h2, Matrix.det_one] at this
  simpa [M, N, LinearMap.det_toMatrix] using this


end DetPair

section DetBlock

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem det_eq_mul_det_of_isCompl {P Q : Submodule K V} (hPQ : IsCompl P Q)
    (f : Module.End K V) (hP : ∀ v ∈ P, f v ∈ P) (hQ : ∀ v ∈ Q, f v ∈ Q) :
    LinearMap.det f = LinearMap.det (f.restrict hP) * LinearMap.det (f.restrict hQ) := by
  let e := Submodule.prodEquivOfIsCompl P Q hPQ
  have h1 : (e : P × Q →ₗ[K] V) ∘ₗ (LinearMap.prodMap (f.restrict hP) (f.restrict hQ)) ∘ₗ
      (e.symm : V →ₗ[K] P × Q) = f := by
    ext v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    set x := e.symm v with hx
    have hv : v = (x.1 : V) + (x.2 : V) := by
      conv_lhs => rw [← e.apply_symm_apply v]
      exact Submodule.coe_prodEquivOfIsCompl' P Q hPQ _
    rw [LinearMap.prodMap_apply]
    change ((f.restrict hP x.1 : P) : V) + ((f.restrict hQ x.2 : Q) : V) = f v
    rw [hv, map_add]
    rfl
  rw [← LinearMap.det_prodMap,
    ← LinearMap.det_conj (LinearMap.prodMap (f.restrict hP) (f.restrict hQ)) e, h1]

theorem det_eq_det_restrict_of_trivial_off {x : Module.End K V}
    (hsq : Squarefree (minpoly K x)) {a : K[X]} (ha : a ∈ primaryFactors x)
    {h : Module.End K V} (hcomm : Commute h x)
    (hid : ∀ b ∈ primaryFactors x, b ≠ a → ∀ v ∈ primaryComponent x b, h v = v) :
    LinearMap.det h = LinearMap.det (h.restrict
      (fun _ hv => apply_mem_primaryComponent hcomm hv : ∀ v ∈ primaryComponent x a,
        h v ∈ primaryComponent x a)) := by
  classical
  let π' : V →ₗ[K] primaryComponent x a :=
    (primaryProjection x a).codRestrict (primaryComponent x a) (primaryProjection_mem hsq ha)
  have hπ' : ∀ v : primaryComponent x a, π' v = v := fun v =>
    Subtype.ext (primaryProjection_of_mem hsq ha v.2)
  have hc := LinearMap.isCompl_of_proj hπ'
  have hQ : ∀ v ∈ LinearMap.ker π', h v = v := by
    intro v hv
    have hv0 : primaryProjection x a v = 0 := by
      have := LinearMap.mem_ker.mp hv
      exact congrArg Subtype.val this
    have hsum : v = ∑ b ∈ primaryFactors x, primaryProjection x b v := by
      have := LinearMap.congr_fun (sum_primaryProjection hsq) v
      rw [LinearMap.sum_apply] at this
      simpa using this.symm
    conv_lhs => rw [hsum]
    rw [map_sum]
    conv_rhs => rw [hsum]
    refine Finset.sum_congr rfl fun b hb => ?_
    by_cases hba : b = a
    · subst hba
      rw [hv0, map_zero]
    · exact hid b hb hba _ (primaryProjection_mem hsq hb v)
  have hP : ∀ v ∈ primaryComponent x a, h v ∈ primaryComponent x a :=
    fun _ hv => apply_mem_primaryComponent hcomm hv
  have hQ' : ∀ v ∈ LinearMap.ker π', h v ∈ LinearMap.ker π' := fun v hv => by
    rw [hQ v hv]; exact hv
  rw [det_eq_mul_det_of_isCompl hc h hP hQ']
  have : h.restrict hQ' = LinearMap.id := by
    ext v
    exact hQ v v.2
  rw [this, LinearMap.det_id, mul_one]


theorem det_restrictScalars_blockGL {x : Module.End K V} (a : K[X]) [Fact (Irreducible a)]
    (γ : Module.End (AdjoinRoot a) (primaryComponent x a)) :
    LinearMap.det (γ.restrictScalars K) = Algebra.norm K (LinearMap.det γ) :=
  LinearMap.det_restrictScalars

end DetBlock

section DetUnitary

variable {ℓ f : ℕ} {K : Type*} [Field K] [Finite K] (hK : UnitaryFieldData ℓ f K)
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}
  (H : UnitaryPrimaryData hK.bar B x)

theorem det_eq_one_of_selfDual {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V))
    (hself : dualPoly hK.bar a = a) [Fact (Irreducible a)]
    (g : supportedUnitary B x {a})
    (hg : ((selfDualFactorEquiv hK H ha hself g :
        sesqUnitaryGroup (selfDualForm hK H ha hself)) :
        LinearMap.GeneralLinearGroup (AdjoinRoot a)
          (primaryComponent (x : Module.End K V) a)) ∈
      sesqSpecialUnitaryGroup (selfDualForm hK H ha hself)) :
    LinearMap.det ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) = 1 := by
  have hcomm := (mem_unitaryCentralizer.mp g.2.1).2
  rw [det_eq_det_restrict_of_trivial_off H.squarefree ha hcomm
    (fun b hb hba v hv => g.2.2 b hb (by simpa using hba) v hv)]
  have h1 : (((g : LinearMap.GeneralLinearGroup K V) : Module.End K V).restrict
      (fun _ hv => apply_mem_primaryComponent hcomm hv :
        ∀ v ∈ primaryComponent (x : Module.End K V) a, ((g : LinearMap.GeneralLinearGroup K V) :
          Module.End K V) v ∈ primaryComponent (x : Module.End K V) a)) =
      ((selfDualFactorEquiv hK H ha hself g : sesqUnitaryGroup (selfDualForm hK H ha hself)) :
        LinearMap.GeneralLinearGroup (AdjoinRoot a) (primaryComponent (x : Module.End K V) a)
        ).val.restrictScalars K := rfl
  rw [h1, det_restrictScalars_blockGL]
  have := ((mem_sesqSpecialUnitaryGroup.mp hg).2)
  rw [this, map_one]


omit [Finite K] in
open scoped _root_.Classical in
theorem det_glue_update {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V))
    (γ : blockGL (x : Module.End K V) a) :
    LinearMap.det ((((glCentralizerEquivPi H.squarefree).symm
      (Function.update (1 : (b : primaryFactors (x : Module.End K V)) →
        blockGL (x : Module.End K V) (b : K[X])) ⟨a, ha⟩ γ) : gl_centralizer x) :
        LinearMap.GeneralLinearGroup K V) : Module.End K V) =
      LinearMap.det ((γ : Module.End (AdjoinRoot a) (primaryComponent (x : Module.End K V) a)
        ).restrictScalars K) := by
  classical
  set Γ : (b : primaryFactors (x : Module.End K V)) → blockGL (x : Module.End K V) (b : K[X]) :=
    Function.update 1 ⟨a, ha⟩ γ with hΓ
  set g : gl_centralizer x := (glCentralizerEquivPi H.squarefree).symm Γ with hg
  have hcomm : Commute ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V)
      (x : Module.End K V) := mem_gl_centralizer.mp g.2
  have hga : ∀ (v : V) (hv : v ∈ primaryComponent (x : Module.End K V) a),
      ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = blockApply γ v hv :=
    fun v hv => by rw [glue_apply H Γ ⟨a, ha⟩ hv]; simp [Γ]
  rw [det_eq_det_restrict_of_trivial_off H.squarefree ha hcomm]
  · congr 1
    ext v
    exact hga v v.2
  · intro b hb hba v hv
    rw [glue_apply H Γ ⟨b, hb⟩ hv]
    have hne : (⟨b, hb⟩ : primaryFactors (x : Module.End K V)) ≠ ⟨a, ha⟩ :=
      fun h => hba (congrArg Subtype.val h)
    simp only [Γ, Function.update_of_ne hne]
    rfl


omit [Finite K] in
open scoped _root_.Classical in
theorem det_eq_one_of_paired {a : K[X]} (ha : a ∈ primaryFactors (x : Module.End K V))
    (hne : a ≠ dualPoly hK.bar a) [Fact (Irreducible a)]
    (g : supportedUnitary B x {a, dualPoly hK.bar a})
    (hg : LinearMap.det ((pairedFactorEquiv H ha hne g : blockGL (x : Module.End K V) a) :
      Module.End (AdjoinRoot a) (primaryComponent (x : Module.End K V) a)) = 1) :
    LinearMap.det ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) = 1 := by
  have hsq := H.squarefree
  have hb := dualPoly_mem_primaryFactors H ha
  let ia : primaryFactors (x : Module.End K V) := ⟨a, ha⟩
  let ib : primaryFactors (x : Module.End K V) := ⟨dualPoly hK.bar a, hb⟩
  have hiab : ia ≠ ib := fun h => hne (congrArg Subtype.val h)
  let Θ := glCentralizerEquivPi hsq
  let g' : gl_centralizer x := ⟨g, supportedUnitary_le_gl_centralizer _ g.2⟩
  let γ : blockGL (x : Module.End K V) a := Θ g' ia
  let δ : blockGL (x : Module.End K V) (dualPoly hK.bar a) := Θ g' ib
  have hΘo : ∀ c : primaryFactors (x : Module.End K V), c ≠ ia → c ≠ ib → Θ g' c = 1 := by
    intro c hc1 hc2
    have hcS : (c : K[X]) ∉ ({a, dualPoly hK.bar a} : Set K[X]) := by
      rintro (h | h)
      · exact hc1 (Subtype.ext h)
      · exact hc2 (Subtype.ext h)
    apply Units.ext
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact g.2.2 c c.2 hcS v v.2
  let g₁ : gl_centralizer x := Θ.symm (Function.update 1 ia γ)
  let g₂ : gl_centralizer x := Θ.symm (Function.update 1 ib δ)
  have hmul : g' = g₁ * g₂ := by
    apply Θ.injective
    rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    funext c
    by_cases hc1 : c = ia
    · subst hc1
      simp [Function.update_of_ne hiab, γ]
    · by_cases hc2 : c = ib
      · subst hc2
        simp [Function.update_of_ne hiab.symm, δ]
      · simp [Function.update_of_ne hc1, Function.update_of_ne hc2, hΘo c hc1 hc2]
  have hdet : LinearMap.det ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) =
      LinearMap.det ((g₁ : LinearMap.GeneralLinearGroup K V) : Module.End K V) *
        LinearMap.det ((g₂ : LinearMap.GeneralLinearGroup K V) : Module.End K V) := by
    have : (g : LinearMap.GeneralLinearGroup K V) =
        (g₁ : LinearMap.GeneralLinearGroup K V) * (g₂ : LinearMap.GeneralLinearGroup K V) :=
      congrArg Subtype.val hmul
    rw [this, Units.val_mul, map_mul]
  have h1 := det_glue_update hK H ha γ
  have h2 := det_glue_update hK H hb δ
  have hγ1 : LinearMap.det ((γ : Module.End (AdjoinRoot a)
      (primaryComponent (x : Module.End K V) a)).restrictScalars K) = 1 := by
    rw [det_restrictScalars_blockGL]
    have : LinearMap.det (γ : Module.End (AdjoinRoot a)
        (primaryComponent (x : Module.End K V) a)) = 1 := hg
    rw [this, map_one]
  have hpair := det_pair (B := B) (P := primaryComponent (x : Module.End K V) a)
    (Q := primaryComponent (x : Module.End K V) (dualPoly hK.bar a))
    (finrank_primaryComponent_dualPoly H ha).symm
    (fun w hw h => eq_zero_of_perfect_right H ha hb rfl hw h)
    ((γ : Module.End (AdjoinRoot a) (primaryComponent (x : Module.End K V) a)).restrictScalars K)
    ((δ : Module.End (AdjoinRoot (dualPoly hK.bar a))
      (primaryComponent (x : Module.End K V) (dualPoly hK.bar a))).restrictScalars K)
    (fun v w => (mem_unitaryCentralizer.mp g.2.1).1 (v : V) (w : V))
  rw [hγ1, map_one, one_mul] at hpair
  rw [hdet, h1, h2, hγ1, hpair, one_mul]

end DetUnitary

end CFSG.RankThree.PartOne.KCUnitary

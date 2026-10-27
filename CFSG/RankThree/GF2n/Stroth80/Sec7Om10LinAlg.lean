module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.ClassicalGroups.Symplectic.StandardForm
public import CFSG.LieType.Universal.Spin.Forms
import CFSG.LocalAnalysis.StandardType.GGQuadChar2Isometry
import CFSG.RankThree.GF2n.Stroth80.Sec7Om4NonsingStab
import CFSG.RankThree.OrthogonalInvolutions.Dickson

public section

namespace CFSG.RankThree.GF2n.Stroth80.Om10

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Symplectic
  CFSG.LieType.Universal.Spin CFSG.Open
open scoped Matrix

theorem exists_transvection_of_defect {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
    (F : V →ₗ[K] V) (hFF : ∀ w, F (F w) = w) (hiso : ∀ w, Q (F w) = Q w)
    (hns : ∀ w, F w ≠ w → Q (F w - w) ≠ 0) (hne : ∃ w, F w ≠ w) :
    ∃ a : V, Q a = 1 ∧ ∀ v, F v = v + polar Q v a • a := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hpol : ∀ v w, polar Q (F v) (F w) = polar Q v w := fun v w => by
    simp only [polar, ← map_add, hiso]
  have hdd : ∀ v w, polar Q (F v - v) (F w - w) = 0 := fun v w => by
    have h1 : polar Q v (F w) = polar Q (F v) w := by
      rw [← hpol v (F w), hFF]
    rw [polar_sub_left, polar_sub_right, polar_sub_right, hpol, h1]
    linear_combination (polar Q v w - polar Q (F v) w) * h2
  obtain ⟨w₀, hw₀⟩ := hne
  obtain ⟨u₀, hu₀⟩ : ∃ u, u = F w₀ - w₀ := ⟨_, rfl⟩
  have hq : Q u₀ ≠ 0 := by rw [hu₀]; exact hns w₀ hw₀
  have hu₀0 : u₀ ≠ 0 := fun h => hq (by rw [h, QuadraticMap.map_zero])
  have hdu : ∀ v, polar Q (F v - v) u₀ = 0 := fun v => by rw [hu₀]; exact hdd v w₀
  have hline : ∀ v, ∃ c : K, F v - v = c • u₀ := by
    intro v
    by_contra hcon
    push Not at hcon
    obtain ⟨μ, hμ⟩ := CFSG.RankThree.GF2n.Stroth80.sec7ns_sq_surj (Q (F v - v) / Q u₀)
    have hD : F (v + μ • w₀) - (v + μ • w₀) = (F v - v) + μ • u₀ := by
      rw [map_add, map_smul, hu₀, smul_sub]
      abel
    have hne' : F (v + μ • w₀) ≠ v + μ • w₀ := by
      intro h
      apply hcon (-μ)
      have h0 : (F v - v) + μ • u₀ = 0 := by rw [← hD, h, sub_self]
      rw [neg_smul, eq_neg_iff_add_eq_zero]
      exact h0
    apply hns _ hne'
    have hμq : μ * μ * Q u₀ = Q (F v - v) := by rw [hμ, div_mul_cancel₀ _ hq]
    rw [hD, QuadraticMap.map_add (⇑Q), QuadraticMap.map_smul, polar_smul_right, hdu v,
      smul_zero, add_zero, smul_eq_mul, hμq]
    linear_combination Q (F v - v) * h2
  have hiso' : ∀ v c, F v - v = c • u₀ → c * (c * Q u₀ + polar Q v u₀) = 0 := by
    intro v c hc
    have hFv : F v = v + c • u₀ := by rw [← hc]; abel
    have h := hiso v
    rw [hFv, QuadraticMap.map_add (⇑Q), QuadraticMap.map_smul, polar_smul_right, smul_eq_mul,
      smul_eq_mul] at h
    linear_combination h
  have hw₀u : polar Q w₀ u₀ = Q u₀ := by
    have h := hiso' w₀ 1 (by rw [one_smul, hu₀])
    linear_combination h - Q u₀ * h2
  have hcoef : ∀ v, F v - v = (polar Q v u₀ / Q u₀) • u₀ := by
    intro v
    obtain ⟨c, hc⟩ := hline v
    obtain ⟨c', hc'⟩ := hline (v + w₀)
    have hcc : c' = c + 1 := by
      have h1 : c' • u₀ = (c + 1) • u₀ := by
        rw [← hc', add_smul, one_smul, ← hc, map_add, hu₀]
        abel
      exact smul_left_injective K hu₀0 h1
    have e1 := hiso' v c hc
    have e2 := hiso' (v + w₀) c' hc'
    rw [hcc, polar_add_left, hw₀u] at e2
    have key : c * Q u₀ + polar Q v u₀ = 0 := by
      linear_combination e2 - e1 - (c * Q u₀ + Q u₀) * h2
    have hc_eq : c = polar Q v u₀ / Q u₀ := by
      rw [eq_div_iff hq]
      linear_combination key - polar Q v u₀ * h2
    rw [hc, hc_eq]
  obtain ⟨μ, hμ⟩ := CFSG.RankThree.GF2n.Stroth80.sec7ns_sq_surj (Q u₀)⁻¹
  refine ⟨μ • u₀, ?_, fun v => ?_⟩
  · rw [QuadraticMap.map_smul, smul_eq_mul, hμ, inv_mul_cancel₀ hq]
  · rw [polar_smul_right, smul_eq_mul, smul_smul]
    have h1 : μ * polar Q v u₀ * μ = polar Q v u₀ / Q u₀ := by
      rw [div_eq_mul_inv, ← hμ]
      ring
    rw [h1, ← hcoef v]
    abel

theorem spForm_eq_polar_quadPlus {m : ℕ} {K : Type} [Field K] [CharP K 2]
    (x y : Fin m ⊕ Fin m → K) : spForm m K x y = polar (quadPlus m K) x y := by
  rw [spForm_apply, polar_quadPlus]
  simp only [dotProduct, Fintype.sum_sum_type, spJ_mulVec_inl, spJ_mulVec_inr, CharTwo.neg_eq,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

structure IsCoord {K : Type} [Field K] (a : Fin 5 ⊕ Fin 5 → K)
    (π : (Fin 5 ⊕ Fin 5 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K))
    (σ : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 5 ⊕ Fin 5 → K)) : Prop where
  quad_a : quadPlus 5 K a = 1
  proj_a : π a = 0
  perp_sec : ∀ y, polar (quadPlus 5 K) (σ y) a = 0
  proj_sec : ∀ y, π (σ y) = y
  sec_proj : ∀ v, polar (quadPlus 5 K) v a = 0 → ∃ c : K, v = σ (π v) + c • a
  form : ∀ v w, polar (quadPlus 5 K) v a = 0 → polar (quadPlus 5 K) w a = 0 →
    spForm 4 K (π v) (π w) = polar (quadPlus 5 K) v w
  quad_sec : ∀ y, quadPlus 5 K (σ y) = quadPlus 4 K y
  exists_one : ∃ v₁, polar (quadPlus 5 K) v₁ a = 1

section Model

variable (K : Type) [Field K]

def baseVec : Fin 5 ⊕ Fin 5 → K := Pi.single (.inl 0) 1 + Pi.single (.inr 0) 1

def baseProj : (Fin 5 ⊕ Fin 5 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K) :=
  LinearMap.funLeft K K (Sum.map Fin.succ Fin.succ)

def baseSec : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 5 ⊕ Fin 5 → K) where
  toFun y := Sum.elim (Fin.cons (0 : K) fun i => y (.inl i) : Fin 5 → K)
    (Fin.cons (0 : K) fun i => y (.inr i) : Fin 5 → K)
  map_add' y z := by
    funext x
    rcases x with i | i <;> cases i using Fin.cases <;> simp
  map_smul' c y := by
    funext x
    rcases x with i | i <;> cases i using Fin.cases <;> simp

@[simp] private theorem baseProj_apply (v : Fin 5 ⊕ Fin 5 → K) (x : Fin 4 ⊕ Fin 4) :
    baseProj K v x = v (Sum.map Fin.succ Fin.succ x) := rfl

@[simp] private theorem baseSec_inl_zero (y : Fin 4 ⊕ Fin 4 → K) :
    baseSec K y (.inl 0) = 0 := by simp [baseSec]

@[simp] private theorem baseSec_inr_zero (y : Fin 4 ⊕ Fin 4 → K) :
    baseSec K y (.inr 0) = 0 := by simp [baseSec]

@[simp] private theorem baseSec_inl_succ (y : Fin 4 ⊕ Fin 4 → K) (i : Fin 4) :
    baseSec K y (.inl i.succ) = y (.inl i) := by simp [baseSec]

@[simp] private theorem baseSec_inr_succ (y : Fin 4 ⊕ Fin 4 → K) (i : Fin 4) :
    baseSec K y (.inr i.succ) = y (.inr i) := by simp [baseSec]

variable {K}

private theorem polar_baseVec (v : Fin 5 ⊕ Fin 5 → K) :
    polar (quadPlus 5 K) v (baseVec K) = v (.inr 0) + v (.inl 0) := by
  rw [baseVec, polar_add_right, polar_quadPlus_single_inl, polar_quadPlus_single_inr]

private theorem eq_of_polar_baseVec [CharP K 2] {v : Fin 5 ⊕ Fin 5 → K}
    (hv : polar (quadPlus 5 K) v (baseVec K) = 0) : v (.inl 0) = v (.inr 0) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [polar_baseVec] at hv
  linear_combination hv - v (.inr 0) * h2

theorem isCoord_base [CharP K 2] : IsCoord (baseVec K) (baseProj K) (baseSec K) where
  quad_a := by
    rw [quadPlus_apply, Fin.sum_univ_succ]
    simp [baseVec, Pi.single_apply]
  proj_a := by
    funext x
    rcases x with i | i <;> simp [baseVec, Pi.single_apply]
  perp_sec y := by
    rw [polar_baseVec]
    simp
  proj_sec y := by
    funext x
    rcases x with i | i <;> simp
  sec_proj v hv := by
    have h0 := eq_of_polar_baseVec hv
    refine ⟨v (.inl 0), ?_⟩
    funext x
    rcases x with i | i <;> cases i using Fin.cases <;> simp [baseVec, Pi.single_apply, h0]
  form v w hv hw := by
    rw [polar_quadPlus 5 K v w, Fin.sum_univ_succ, spForm_eq_polar_quadPlus, polar_quadPlus 4 K]
    simp only [baseProj_apply, Sum.map_inl, Sum.map_inr]
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination (-w (.inr 0)) * eq_of_polar_baseVec hv +
      (-v (.inr 0)) * eq_of_polar_baseVec hw + (-(v (.inr 0) * w (.inr 0))) * h2
  quad_sec y := by
    rw [quadPlus_apply 5 K, Fin.sum_univ_succ, quadPlus_apply 4 K]
    simp
  exists_one := ⟨Pi.single (.inl 0) 1, by rw [polar_baseVec]; simp [Pi.single_apply]⟩

end Model

section Coord

variable {K : Type} [Field K] {a : Fin 5 ⊕ Fin 5 → K}
  {π : (Fin 5 ⊕ Fin 5 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)}
  {σ : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 5 ⊕ Fin 5 → K)}

private theorem polar_mulVec_of_iso {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm K (ι → K)} {M : Matrix ι ι K} (hM : ∀ v, Q (M *ᵥ v) = Q v) (v w : ι → K) :
    polar Q (M *ᵥ v) (M *ᵥ w) = polar Q v w := by
  simp only [polar, ← Matrix.mulVec_add, hM]

private theorem polar_mulVec_eq_zero {M : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K}
    (hM : ∀ v, quadPlus 5 K (M *ᵥ v) = quadPlus 5 K v) (hMa : M *ᵥ a = a)
    {u : Fin 5 ⊕ Fin 5 → K} (hu : polar (quadPlus 5 K) u a = 0) :
    polar (quadPlus 5 K) (M *ᵥ u) a = 0 := by
  calc polar (quadPlus 5 K) (M *ᵥ u) a = polar (quadPlus 5 K) (M *ᵥ u) (M *ᵥ a) := by rw [hMa]
    _ = 0 := by rw [polar_mulVec_of_iso hM, hu]

private theorem IsCoord.proj_mulVec_sec_proj (hc : IsCoord a π σ)
    {M : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K} (hMa : M *ᵥ a = a)
    {u : Fin 5 ⊕ Fin 5 → K} (hu : polar (quadPlus 5 K) u a = 0) :
    π (M *ᵥ σ (π u)) = π (M *ᵥ u) := by
  obtain ⟨c, hcu⟩ := hc.sec_proj u hu
  have h : M *ᵥ u = M *ᵥ σ (π u) + c • a :=
    calc M *ᵥ u = M *ᵥ (σ (π u) + c • a) := by rw [← hcu]
      _ = M *ᵥ σ (π u) + c • a := by rw [Matrix.mulVec_add, Matrix.mulVec_smul, hMa]
  rw [h, map_add, map_smul, hc.proj_a, smul_zero, add_zero]

theorem IsCoord.transport (hc : IsCoord a π σ) (A : GL (Fin 5 ⊕ Fin 5) K)
    (hA : ∀ v, quadPlus 5 K ((A : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ v) =
      quadPlus 5 K v) :
    IsCoord ((A : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ a)
      (π ∘ₗ Matrix.toLin' ((A⁻¹ : GL (Fin 5 ⊕ Fin 5) K) :
        Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K))
      (Matrix.toLin' (A : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) ∘ₗ σ) := by
  set M : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K :=
    (A : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) with hM
  set M' : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K :=
    ((A⁻¹ : GL (Fin 5 ⊕ Fin 5) K) : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) with hM'
  have hMM' : ∀ v, M' *ᵥ (M *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, hM, hM', ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hM'M : ∀ v, M *ᵥ (M' *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, hM, hM', ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hpA : ∀ v w, polar (quadPlus 5 K) (M *ᵥ v) (M *ᵥ w) = polar (quadPlus 5 K) v w :=
    polar_mulVec_of_iso hA
  have hpA' : ∀ v w, polar (quadPlus 5 K) (M' *ᵥ v) (M' *ᵥ w) = polar (quadPlus 5 K) v w :=
    fun v w => by rw [← hpA, hM'M, hM'M]
  have hperp : ∀ v, polar (quadPlus 5 K) v (M *ᵥ a) = 0 →
      polar (quadPlus 5 K) (M' *ᵥ v) a = 0 := fun v hv => by
    rw [← hpA, hM'M]
    exact hv
  refine ⟨?_, ?_, fun y => ?_, fun y => ?_, fun v hv => ?_, fun v w hv hw => ?_, fun y => ?_, ?_⟩
  · rw [hA, hc.quad_a]
  · simp only [LinearMap.comp_apply, Matrix.toLin'_apply]
    rw [hMM', hc.proj_a]
  · simp only [LinearMap.comp_apply, Matrix.toLin'_apply]
    rw [hpA, hc.perp_sec]
  · simp only [LinearMap.comp_apply, Matrix.toLin'_apply]
    rw [hMM', hc.proj_sec]
  · obtain ⟨c, hcv⟩ := hc.sec_proj _ (hperp v hv)
    refine ⟨c, ?_⟩
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply]
    calc v = M *ᵥ (M' *ᵥ v) := (hM'M v).symm
      _ = M *ᵥ (σ (π (M' *ᵥ v)) + c • a) := by rw [← hcv]
      _ = M *ᵥ σ (π (M' *ᵥ v)) + c • (M *ᵥ a) := by
        rw [Matrix.mulVec_add, Matrix.mulVec_smul]
  · simp only [LinearMap.comp_apply, Matrix.toLin'_apply]
    rw [hc.form _ _ (hperp v hv) (hperp w hw), hpA']
  · simp only [LinearMap.comp_apply, Matrix.toLin'_apply]
    rw [hA, hc.quad_sec]
  · obtain ⟨v₁, hv₁⟩ := hc.exists_one
    exact ⟨M *ᵥ v₁, by rw [hpA, hv₁]⟩

theorem exists_isCoord [Finite K] [CharP K 2] {a : Fin 5 ⊕ Fin 5 → K}
    (ha : quadPlus 5 K a = 1) : ∃ π σ, IsCoord a π σ := by
  have hb := isCoord_base (K := K)
  have ha0 : a ≠ 0 := fun h => by
    rw [h, QuadraticMap.map_zero] at ha
    exact zero_ne_one ha
  have hb0 : baseVec K ≠ 0 := fun h => by
    have h1 := hb.quad_a
    rw [h, QuadraticMap.map_zero] at h1
    exact zero_ne_one h1
  obtain ⟨A, hA, hAa⟩ := statedOmegaPlus_exists_mulVec_eq (by norm_num : 3 ≤ 5) hb0 ha0
    (by rw [hb.quad_a, ha])
  have hiso : ∀ v, quadPlus 5 K ((A : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ v) =
      quadPlus 5 K v := fun v => by
    rw [← (ElemMatrixIso.plus (K := K) (by norm_num : 3 ≤ 5)).app ⟨A, hA⟩ v]
    exact map_of_mem (elementaryGroup_le_orthogonalGroup _ (Subtype.prop _)) v
  subst hAa
  exact ⟨_, _, hb.transport A hiso⟩

noncomputable def rhoHom (hc : IsCoord a π σ) {Y : Type*} [Group Y]
    (f : Y →* GL (Fin 5 ⊕ Fin 5) K)
    (hf : ∀ y v, quadPlus 5 K ((f y : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ v) =
      quadPlus 5 K v)
    (hfa : ∀ y, (f y : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ a = a) :
    Y →* GL (Fin 4 ⊕ Fin 4) K :=
  MonoidHom.toHomUnits
    ({ toFun := fun y => LinearMap.toMatrix'
          (π ∘ₗ Matrix.toLin' (f y : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) ∘ₗ σ)
       map_one' := by
        rw [map_one, Units.val_one, Matrix.toLin'_one, LinearMap.id_comp,
          show π ∘ₗ σ = LinearMap.id from LinearMap.ext hc.proj_sec, LinearMap.toMatrix'_id]
       map_mul' := fun x y => by
        rw [← LinearMap.toMatrix'_comp]
        congr 1
        refine LinearMap.ext fun z => ?_
        simp only [LinearMap.comp_apply, Matrix.toLin'_apply, map_mul, Units.val_mul,
          ← Matrix.mulVec_mulVec]
        exact (hc.proj_mulVec_sec_proj (hfa x)
          (polar_mulVec_eq_zero (hf y) (hfa y) (hc.perp_sec z))).symm } :
      Y →* Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K)

theorem rhoHom_mulVec (hc : IsCoord a π σ) {Y : Type*} [Group Y]
    (f : Y →* GL (Fin 5 ⊕ Fin 5) K)
    (hf : ∀ y v, quadPlus 5 K ((f y : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ v) =
      quadPlus 5 K v)
    (hfa : ∀ y, (f y : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ a = a) (y : Y)
    (z : Fin 4 ⊕ Fin 4 → K) :
    ((rhoHom hc f hf hfa y : GL (Fin 4 ⊕ Fin 4) K) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ z =
      π ((f y : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ σ z) := by
  simp only [rhoHom, MonoidHom.coe_toHomUnits, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [LinearMap.toMatrix'_mulVec]
  simp only [LinearMap.comp_apply, Matrix.toLin'_apply]

theorem rhoHom_mem_statedSp (hc : IsCoord a π σ) {Y : Type*} [Group Y]
    (f : Y →* GL (Fin 5 ⊕ Fin 5) K)
    (hf : ∀ y v, quadPlus 5 K ((f y : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ v) =
      quadPlus 5 K v)
    (hfa : ∀ y, (f y : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ a = a) (y : Y) :
    rhoHom hc f hf hfa y ∈ StatedSp 4 K := by
  rw [mem_statedSp_iff_forall]
  intro z z'
  rw [rhoHom_mulVec, rhoHom_mulVec]
  have h1 := polar_mulVec_eq_zero (hf y) (hfa y) (hc.perp_sec z)
  have h2 := polar_mulVec_eq_zero (hf y) (hfa y) (hc.perp_sec z')
  rw [hc.form _ _ h1 h2, polar_mulVec_of_iso (hf y),
    ← hc.form _ _ (hc.perp_sec z) (hc.perp_sec z'), hc.proj_sec, hc.proj_sec]

theorem eq_or_transvection_of_trivial [CharP K 2] (hc : IsCoord a π σ)
    {h : GL (Fin 5 ⊕ Fin 5) K}
    (hiso : ∀ v, quadPlus 5 K ((h : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ v) =
      quadPlus 5 K v)
    (ha : (h : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ a = a)
    (htriv : ∀ z, π ((h : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ σ z) = z) :
    (∀ v, (h : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ v = v) ∨
      (∀ v, (h : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ v =
        v + polar (quadPlus 5 K) v a • a) := by
  have hsub : ∀ x, polar (quadPlus 5 K) x a = 0 →
      toLinEquiv (Fin 5 ⊕ Fin 5) K h x - x ∈ Submodule.span K {a} := by
    intro x hx
    rw [toLinEquiv_apply, Submodule.mem_span_singleton]
    obtain ⟨c, hcx⟩ := hc.sec_proj x hx
    obtain ⟨c', hc'⟩ := hc.sec_proj _ (polar_mulVec_eq_zero hiso ha hx)
    have hπ : π ((h : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ x) = π x := by
      rw [← hc.proj_mulVec_sec_proj ha hx, htriv]
    have e1 : (h : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ x = σ (π x) + c' • a := by
      rw [← hπ]
      exact hc'
    refine ⟨c' - c, ?_⟩
    rw [e1]
    linear_combination (norm := module) hcx
  rcases CFSG.StandardType.QuadChar2.isometry_eq_one_or_transvection
      (nondegenerate_polarBilin_quadPlus 5 K) hc.quad_a (g := toLinEquiv (Fin 5 ⊕ Fin 5) K h)
      hiso hsub with h1 | h1
  · exact Or.inl fun v => by simpa using LinearEquiv.congr_fun h1 v
  · exact Or.inr fun v => by simpa using h1 v

theorem transvection_not_mem_statedOmega [CharP K 2] (ha : quadPlus 5 K a = 1)
    {A : GL (Fin 5 ⊕ Fin 5) K}
    (hA : ∀ v, (A : Matrix (Fin 5 ⊕ Fin 5) (Fin 5 ⊕ Fin 5) K) *ᵥ v =
      v + polar (quadPlus 5 K) v a • a) :
    A ∉ StatedOmega (StatedQuadPlus 5 K) := by
  intro hmem
  have hQ := nondegenerate_polarBilin_quadPlus 5 K
  have ha0 : quadPlus 5 K a ≠ 0 := by
    rw [ha]
    exact one_ne_zero
  rw [statedOmega_eq_comap (coe_quadPlus 5 K), Subgroup.mem_comap,
    MulEquiv.coe_toMonoidHom] at hmem
  have hrefl : toLinEquiv (Fin 5 ⊕ Fin 5) K A = reflect (quadPlus 5 K) a := by
    refine LinearEquiv.ext fun v => ?_
    rw [toLinEquiv_apply, hA, reflect_apply ha0, ha, div_one, polar_comm, sub_eq_add_neg,
      ← neg_smul, CharTwo.neg_eq]
  rw [hrefl, ← Subgroup.map_subtype_commutator] at hmem
  obtain ⟨g, hg, hga⟩ := Subgroup.mem_map.mp hmem
  have hker := Abelianization.commutator_subset_ker
    (CFSG.RankThree.OrthogonalInvolutions.dicksonHom (quadPlus 5 K) hQ) hg
  rw [MonoidHom.mem_ker, CFSG.RankThree.OrthogonalInvolutions.dicksonHom_apply] at hker
  have hg' : (g : (Fin 5 ⊕ Fin 5 → K) ≃ₗ[K] (Fin 5 ⊕ Fin 5 → K)) =
      reflect (quadPlus 5 K) a := hga
  let _ : Invertible (quadPlus 5 K a) := invertibleOfNonzero ha0
  rw [hg', reflect_eq_reflection,
    CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_reflection hQ a, Nat.cast_one] at hker
  exact absurd (ofAdd_eq_one.mp hker) (by decide)

theorem proj_eichler [CharP K 2] (hc : IsCoord a π σ)
    {b w : Fin 5 ⊕ Fin 5 → K} (hb : quadPlus 5 K b = 0) (hbw : polar (quadPlus 5 K) b w = 0)
    (hba : polar (quadPlus 5 K) b a = 0) (hwa : polar (quadPlus 5 K) w a = 0)
    (z : Fin 4 ⊕ Fin 4 → K) :
    π (eichler (quadPlus 5 K) b w (σ z)) = z + spForm 4 K z (π b) • π w +
      spForm 4 K z (π w) • π b + (quadPlus 5 K w * spForm 4 K z (π b)) • π b := by
  rw [eichler_apply hb hbw, map_sub, map_add, map_smul, map_smul, hc.proj_sec,
    ← hc.form _ _ (hc.perp_sec z) hba, ← hc.form _ _ (hc.perp_sec z) hwa, hc.proj_sec,
    sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq, add_smul]
  abel

theorem exists_lift [Finite K] [CharP K 2] (hc : IsCoord a π σ)
    {b : Fin 5 ⊕ Fin 5 → K} (hba : polar (quadPlus 5 K) b a = 0) {w' : Fin 4 ⊕ Fin 4 → K}
    (hw' : spForm 4 K (π b) w' = 0) (c : K) :
    ∃ w, polar (quadPlus 5 K) b w = 0 ∧ polar (quadPlus 5 K) w a = 0 ∧ π w = w' ∧
      quadPlus 5 K w = c := by
  have haa : polar (quadPlus 5 K) a a = 0 := by
    rw [polar_self_eq_two_mul, CharTwo.two_eq_zero (R := K), zero_mul]
  obtain ⟨μ, hμ⟩ := CFSG.RankThree.GF2n.Stroth80.sec7ns_sq_surj (c - quadPlus 5 K (σ w'))
  refine ⟨σ w' + μ • a, ?_, ?_, ?_, ?_⟩
  · rw [polar_add_right, polar_smul_right, hba, smul_zero, add_zero,
      ← hc.form _ _ hba (hc.perp_sec w'), hc.proj_sec, hw']
  · rw [polar_add_left, polar_smul_left, haa, smul_zero, add_zero, hc.perp_sec]
  · rw [map_add, map_smul, hc.proj_a, smul_zero, add_zero, hc.proj_sec]
  · rw [QuadraticMap.map_add (⇑(quadPlus 5 K)), QuadraticMap.map_smul, hc.quad_a,
      polar_smul_right, hc.perp_sec, smul_zero, add_zero, smul_eq_mul, mul_one, hμ]
    ring

end Coord

end CFSG.RankThree.GF2n.Stroth80.Om10

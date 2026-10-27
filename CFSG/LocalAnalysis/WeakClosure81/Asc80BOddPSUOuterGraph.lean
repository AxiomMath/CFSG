module

public import CFSG.HardMathSupport.Timmesfeld.LinearRank.UnitaryDiagonal
import CFSG.HardMathSupport.Lang.Proving.HermitianIsotropic
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSUOuterRealForm
import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylowHom

public section

namespace CFSG.LocalAnalysis.WeakClosure81.UOuter

open Matrix CFSG.Open CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

private lemma map_mulVec {k K : Type*} [Field k] [Field K] (φ : k →+* K) {ι : Type*}
    [Fintype ι] (M : Matrix ι ι k) (x : ι → k) :
    M.map φ *ᵥ (fun i => φ (x i)) = fun i => φ ((M *ᵥ x) i) := by
  funext i
  simp only [mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

private lemma map_dotProduct {k K : Type*} [Field k] [Field K] (φ : k →+* K) {ι : Type*}
    [Fintype ι] (x y : ι → k) :
    (fun i => φ (x i)) ⬝ᵥ (fun i => φ (y i)) = φ (x ⬝ᵥ y) := by
  simp only [dotProduct, map_sum, map_mul]

theorem exists_real_isotropic_stable (h : UnitaryFieldData p f K) (hn : 5 ≤ n)
    {G X : Matrix (Fin n) (Fin n) K} (hGr : G.map h.bar = G) (hXr : X.map h.bar = X)
    (hGs : Gᵀ = G ∨ Gᵀ = -G) {m α : K} (hX : Xᵀ * G * X = m • G) (hX2 : X * X = α • 1) :
    ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ (∀ x ∈ W, ∀ y ∈ W, gramForm h G x y = 0) ∧
      (∀ w ∈ W, X *ᵥ w ∈ W) ∧ ∀ w ∈ W, (fun i => h.bar (w i)) ∈ W := by
  classical
  have hfinK : Finite K := h.finite
  have hftK : Fintype K := Fintype.ofFinite K
  have hfact : Fact p.Prime := ⟨h.prime⟩
  have hchar : CharP K p := h.charP
  let φ : h.fixedField →+* K := Subfield.subtype h.fixedField
  have hGmem : ∀ i j, h.bar (G i j) = G i j := by
    intro i j
    have := congrFun (congrFun hGr i) j
    simpa using this
  have hXmem : ∀ i j, h.bar (X i j) = X i j := by
    intro i j
    have := congrFun (congrFun hXr i) j
    simpa using this
  let G₀ : Matrix (Fin n) (Fin n) h.fixedField :=
    fun i j => ⟨G i j, h.mem_fixedField.mpr (hGmem i j)⟩
  let X₀ : Matrix (Fin n) (Fin n) h.fixedField :=
    fun i j => ⟨X i j, h.mem_fixedField.mpr (hXmem i j)⟩
  have hG₀ : G₀.map φ = G := by
    ext i j
    rfl
  have hX₀ : X₀.map φ = X := by
    ext i j
    rfl
  have hM₀ : (G₀ * X₀).map φ = G * X := by
    rw [Matrix.map_mul, hG₀, hX₀]
  let N : Fin 2 → Matrix (Fin n) (Fin n) h.fixedField :=
    fun j => if j = 0 then G₀ else G₀ * X₀
  let P : Fin 2 → MvPolynomial (Fin n) h.fixedField :=
    fun j => ∑ i, ∑ t, MvPolynomial.C (N j i t) * MvPolynomial.X i * MvPolynomial.X t
  have heval : ∀ (x : Fin n → h.fixedField) (j : Fin 2),
      MvPolynomial.eval x (P j) = x ⬝ᵥ (N j *ᵥ x) := by
    intro x j
    simp only [P, dotProduct, mulVec, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun t _ => ?_
    ring
  have hdeg : ∀ j, (P j).totalDegree ≤ 2 := by
    intro j
    have hterm : ∀ (c : h.fixedField) (i t : Fin n),
        (MvPolynomial.C c * MvPolynomial.X i * MvPolynomial.X t :
          MvPolynomial (Fin n) h.fixedField).totalDegree ≤ 2 := by
      intro c i t
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      refine (add_le_add (MvPolynomial.totalDegree_mul _ _) le_rfl).trans ?_
      simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun t _ => ?_)
    exact hterm _ i t
  have h0 : ∀ j, MvPolynomial.eval (0 : Fin n → h.fixedField) (P j) = 0 := by
    intro j
    rw [heval]
    simp
  obtain ⟨x, hx0, hxP⟩ :=
    CFSG.HardMathSupport.Lang.Proving.exists_ne_zero_of_two_quadratic (F := h.fixedField) p
      (σ := Fin n) (by rw [Fintype.card_fin]; omega) P hdeg h0
  have hx : ∀ j, x ⬝ᵥ (N j *ᵥ x) = 0 := fun j => by
    have := hxP j
    rwa [heval] at this
  have hx0' : x ⬝ᵥ (G₀ *ᵥ x) = 0 := by simpa [N] using hx 0
  have hx1 : x ⬝ᵥ ((G₀ * X₀) *ᵥ x) = 0 := by simpa [N] using hx 1
  let v : Fin n → K := fun i => φ (x i)
  let u : Fin n → K := X *ᵥ v
  have hcast : ∀ M : Matrix (Fin n) (Fin n) h.fixedField,
      v ⬝ᵥ (M.map φ *ᵥ v) = φ (x ⬝ᵥ (M *ᵥ x)) := by
    intro M
    show (fun i => φ (x i)) ⬝ᵥ (M.map φ *ᵥ fun i => φ (x i)) = φ (x ⬝ᵥ (M *ᵥ x))
    rw [map_mulVec, map_dotProduct]
  have hvne : v ≠ 0 := by
    intro hv
    apply hx0
    funext i
    have hi : φ (x i) = 0 := by
      have := congrFun hv i
      simpa [v] using this
    exact (Subfield.subtype_injective h.fixedField) (by simpa using hi)
  have hvr : ∀ i, h.bar (v i) = v i := fun i => h.mem_fixedField.mp (x i).2
  have hvbar : (fun i => h.bar (v i)) = v := funext hvr
  have hur : ∀ i, h.bar (u i) = u i := by
    intro i
    have hh := congrFun (map_mulVec h.bar X v) i
    rw [hvbar, hXr] at hh
    exact hh.symm
  have hubar : (fun i => h.bar (u i)) = u := funext hur
  have hvv : v ⬝ᵥ (G *ᵥ v) = 0 := by
    rw [← hG₀, hcast G₀, hx0', map_zero]
  have hvM : v ⬝ᵥ ((G * X) *ᵥ v) = 0 := by
    rw [← hM₀, hcast (G₀ * X₀), hx1, map_zero]
  have hvu : v ⬝ᵥ (G *ᵥ u) = 0 := by
    change v ⬝ᵥ (G *ᵥ (X *ᵥ v)) = 0
    rw [Matrix.mulVec_mulVec]
    exact hvM
  have hvMv : ∀ M : Matrix (Fin n) (Fin n) K, v ⬝ᵥ (M *ᵥ v) = v ⬝ᵥ (Mᵀ *ᵥ v) := by
    intro M
    rw [dotProduct_mulVec, ← mulVec_transpose]
    exact dotProduct_comm _ _
  have hXG : u ⬝ᵥ (G *ᵥ v) = v ⬝ᵥ ((Xᵀ * G) *ᵥ v) := by
    change (X *ᵥ v) ⬝ᵥ (G *ᵥ v) = v ⬝ᵥ ((Xᵀ * G) *ᵥ v)
    rw [dotProduct_mulVec, vecMul_mulVec, ← dotProduct_mulVec]
  have huv : u ⬝ᵥ (G *ᵥ v) = 0 := by
    rw [hXG, hvMv (Xᵀ * G), Matrix.transpose_mul, Matrix.transpose_transpose]
    rcases hGs with hGs' | hGs'
    · rw [hGs']
      exact hvM
    · rw [hGs', neg_mul, Matrix.neg_mulVec, dotProduct_neg, hvM, neg_zero]
  have huu : u ⬝ᵥ (G *ᵥ u) = 0 := by
    have h1 : u ⬝ᵥ (G *ᵥ u) = v ⬝ᵥ ((Xᵀ * G * X) *ᵥ v) := by
      change (X *ᵥ v) ⬝ᵥ (G *ᵥ (X *ᵥ v)) = v ⬝ᵥ ((Xᵀ * G * X) *ᵥ v)
      rw [Matrix.mulVec_mulVec, dotProduct_mulVec, vecMul_mulVec, ← Matrix.mul_assoc,
        ← dotProduct_mulVec]
    rw [h1, hX, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hvv, mul_zero]
  have hgvv : gramForm h G v v = 0 := by rw [gramForm_apply, hvbar, hvv]
  have hgvu : gramForm h G v u = 0 := by rw [gramForm_apply, hvbar, hvu]
  have hguv : gramForm h G u v = 0 := by
    rw [gramForm_apply, hubar]
    exact huv
  have hguu : gramForm h G u u = 0 := by rw [gramForm_apply, hubar, huu]
  refine ⟨Submodule.span K {v, u}, ?_, ?_, ?_, ?_⟩
  · intro hbot
    have hv : v ∈ (⊥ : Submodule K (Fin n → K)) := by
      rw [← hbot]
      exact Submodule.subset_span (by simp)
    rw [Submodule.mem_bot] at hv
    exact hvne hv
  · intro a ha b hb
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp ha
    obtain ⟨e, g, rfl⟩ := Submodule.mem_span_pair.mp hb
    simp only [map_add, LinearMap.map_smulₛₗ₂, map_smul, LinearMap.add_apply, smul_eq_mul,
      hgvv, hgvu, hguv, hguu, mul_zero, add_zero]
  · intro w hw
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hw
    have hXu : X *ᵥ u = α • v := by
      change X *ᵥ (X *ᵥ v) = α • v
      rw [Matrix.mulVec_mulVec, hX2, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hXu' : X *ᵥ (a • v + b • u) = (b * α) • v + a • u := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hXu, smul_smul,
        mul_comm b α, add_comm]
    rw [hXu']
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · intro w hw
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hw
    have hbar : (fun i => h.bar ((a • v + b • u) i)) = h.bar a • v + h.bar b • u := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, hvr i, hur i]
    rw [hbar]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

private abbrev unitaryOne (h : UnitaryFieldData p f K) : Subgroup (GL (Fin n) K) :=
  primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

private abbrev SD (h : UnitaryFieldData p f K) {C : GL (Fin n) K}
    (hC : IsPrimeFormGram C) : Type :=
  primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) ⋊[primeFormFieldU h hC] (K ≃+* K)

private lemma unitary_mul {h : UnitaryFieldData p f K} {A : unitaryOne (n := n) h} :
    ((((A : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
  have h := mem_primeFormUnitary.mp A.2
  simpa using h

private lemma matrix_eq_smul_one_of_psi_eq_one {h : UnitaryFieldData p f K}
    {C : GL (Fin n) K} (hC : IsPrimeFormGram C) (hn : 3 ≤ n)
    {x : SD h hC} (hx : primeFormPsi h hC x = 1) :
    ∃ c : K, (((x.left : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) = c • 1 := by
  obtain ⟨-, c, -, hc⟩ := (primeFormPsi_eq_one_iff h hC hn x).mp hx
  exact ⟨(c : K), by
    rw [hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]⟩

private lemma sq_eq_smul_one {h : UnitaryFieldData p f K} {C : GL (Fin n) K}
    (hC : IsPrimeFormGram C) (hn : 3 ≤ n)
    (A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K))
    (hAA : primeFormPsi h hC (⟨A, 1⟩ * ⟨A, 1⟩ : SD h hC) = 1) :
    ∃ c : K, (((A : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *
      (((A : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) = c • 1 := by
  have h1 : (⟨A * A, 1⟩ : SD h hC) = ⟨A, 1⟩ * ⟨A, 1⟩ := by
    rw [SemidirectProduct.mul_def, map_one, MulAut.one_apply, mul_one]
  have h2 : primeFormPsi h hC (⟨A * A, 1⟩ : SD h hC) = 1 := by
    rw [h1]
    exact hAA
  obtain ⟨c, hc⟩ := matrix_eq_smul_one_of_psi_eq_one (h := h) hC hn (x := ⟨A * A, 1⟩) h2
  exact ⟨c, by simpa using hc⟩

private lemma b_sq_eq_smul_one {h : UnitaryFieldData p f K} {C : GL (Fin n) K}
    (hC : IsPrimeFormGram C) (hn : 3 ≤ n) {φ : K ≃+* K}
    (hφ : ∀ c, φ c = h.bar c) (B : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K))
    (hBB : primeFormPsi h hC (⟨B, φ⟩ * ⟨B, φ⟩ : SD h hC) = 1) :
    ∃ c : K, (((B : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *
      ((((B : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K).map h.bar) = c • 1 := by
  have hφ2 : φ * φ = 1 := by
    ext c
    show φ (φ c) = c
    rw [hφ (φ c), hφ c, h.bar_bar]
  have h1 : (⟨B * primeFormFieldU h hC φ B, 1⟩ : SD h hC) = ⟨B, φ⟩ * ⟨B, φ⟩ := by
    rw [SemidirectProduct.mul_def, hφ2]
  have h2 : primeFormPsi h hC (⟨B * primeFormFieldU h hC φ B, 1⟩ : SD h hC) = 1 := by
    rw [h1]
    exact hBB
  obtain ⟨c, hc⟩ := matrix_eq_smul_one_of_psi_eq_one (h := h) hC hn
    (x := ⟨B * primeFormFieldU h hC φ B, 1⟩) h2
  refine ⟨c, ?_⟩
  have hgl : ((((⟨B * primeFormFieldU h hC φ B, 1⟩ : SD h hC).left :
      primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) : GL (Fin n) K)) =
      (B : GL (Fin n) K) * glAut φ (B : GL (Fin n) K) := by
    rw [Subgroup.coe_mul, coe_primeFormFieldU]
  rw [hgl, Units.val_mul,
    CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow.coe_glAut_of_bar h hφ
      (B : GL (Fin n) K)] at hc
  exact hc

private lemma comm_eq_smul {h : UnitaryFieldData p f K} {C : GL (Fin n) K}
    (hC : IsPrimeFormGram C) (hn : 3 ≤ n) {φ : K ≃+* K}
    (hφ : ∀ c, φ c = h.bar c)
    {A B : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)}
    (hcomm : primeFormPsi h hC ⟨A, 1⟩ * primeFormPsi h hC ⟨B, φ⟩ =
      primeFormPsi h hC ⟨B, φ⟩ * primeFormPsi h hC ⟨A, 1⟩) :
    ∃ c : K, (((A : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *
      (((B : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) =
      c • ((((B : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *
        ((((A : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K).map h.bar)) := by
  have hφ2 : φ * φ = 1 := by
    ext c
    show φ (φ c) = c
    rw [hφ (φ c), hφ c, h.bar_bar]
  have hker : primeFormPsi h hC
      (⟨A, 1⟩ * ⟨B, φ⟩ * (⟨B, φ⟩ * ⟨A, 1⟩)⁻¹ : SD h hC) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, hcomm, mul_inv_cancel]
  have hxy : (⟨A, 1⟩ * ⟨B, φ⟩ : SD h hC) = ⟨A * B, φ⟩ := by
    rw [SemidirectProduct.mul_def, map_one, MulAut.one_apply, one_mul]
  have hyx : (⟨B, φ⟩ * ⟨A, 1⟩ : SD h hC) =
      ⟨B * primeFormFieldU h hC φ A, φ⟩ := by
    rw [SemidirectProduct.mul_def, mul_one]
  have hinv : (⟨B * primeFormFieldU h hC φ A, φ⟩ : SD h hC)⁻¹ =
      ⟨primeFormFieldU h hC φ⁻¹ (B * primeFormFieldU h hC φ A)⁻¹, φ⁻¹⟩ := rfl
  have hφinv : primeFormFieldU h hC φ * primeFormFieldU h hC φ⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have huv : (⟨A, 1⟩ * ⟨B, φ⟩ * (⟨B, φ⟩ * ⟨A, 1⟩)⁻¹ : SD h hC) =
      ⟨(A * B) * (B * primeFormFieldU h hC φ A)⁻¹, 1⟩ := by
    rw [hxy, hyx, hinv, SemidirectProduct.mul_def, ← MulAut.mul_apply, hφinv,
      MulAut.one_apply, mul_inv_cancel]
  have hker' : primeFormPsi h hC
      (⟨(A * B) * (B * primeFormFieldU h hC φ A)⁻¹, 1⟩ : SD h hC) = 1 := by
    rw [← huv]
    exact hker
  obtain ⟨c, hc⟩ := matrix_eq_smul_one_of_psi_eq_one (h := h) hC hn
    (x := ⟨(A * B) * (B * primeFormFieldU h hC φ A)⁻¹, 1⟩) hker'
  refine ⟨c, ?_⟩
  let X : GL (Fin n) K := (A : GL (Fin n) K) * (B : GL (Fin n) K)
  let Y : GL (Fin n) K := (B : GL (Fin n) K) * glAut φ (A : GL (Fin n) K)
  have hXY : (((X * Y⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) = c • 1 := by
    simpa only [X, Y, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul,
      Units.val_inv_eq_inv_val, coe_primeFormFieldU] using hc
  have hYinv : (((Y⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *
      (Y : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hX : (X : Matrix (Fin n) (Fin n) K) = c • (Y : Matrix (Fin n) (Fin n) K) := by
    calc (X : Matrix (Fin n) (Fin n) K)
        = (X : Matrix (Fin n) (Fin n) K) * 1 := by rw [Matrix.mul_one]
      _ = (X : Matrix (Fin n) (Fin n) K) *
            ((((Y⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *
              (Y : Matrix (Fin n) (Fin n) K)) := by rw [hYinv, Matrix.mul_one]
      _ = ((X : Matrix (Fin n) (Fin n) K) *
            (((Y⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)) *
              (Y : Matrix (Fin n) (Fin n) K) := by rw [Matrix.mul_assoc]
      _ = (((X * Y⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *
              (Y : Matrix (Fin n) (Fin n) K) := by rw [← Units.val_mul]
      _ = (c • 1) * (Y : Matrix (Fin n) (Fin n) K) := by rw [hXY]
      _ = c • (Y : Matrix (Fin n) (Fin n) K) := by rw [Matrix.smul_mul, Matrix.one_mul]
  have hXm : (X : Matrix (Fin n) (Fin n) K) =
      (((A : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *
        (((B : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) := by
    simp only [X, Units.val_mul]
  have hYm : (Y : Matrix (Fin n) (Fin n) K) =
      (((B : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *
        ((((A : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K).map h.bar) := by
    rw [show (Y : Matrix (Fin n) (Fin n) K) =
        (((B : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *
          (((glAut φ (A : GL (Fin n) K) : GL (Fin n) K)) :
            Matrix (Fin n) (Fin n) K) by simp only [Y, Units.val_mul]]
    rw [CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow.coe_glAut_of_bar h hφ
      (A : GL (Fin n) K)]
  rw [hXm, hYm] at hX
  exact hX

theorem exists_graph_descent (h : UnitaryFieldData p f K) (hp : p ≠ 2) (hn : 3 ≤ n)
    {E : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))}
    (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4)
    (hED : ¬ E ≤ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ∃ (A B : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (φ : K ≃+* K)
      (P : GL (Fin n) K) (ν μ ε α : K) (G X : Matrix (Fin n) (Fin n) K),
      (∀ c, φ c = h.bar c) ∧
      primeFormPsi h CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one ⟨A, 1⟩ ∈ E ∧
      primeFormPsi h CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one ⟨A, 1⟩ ≠ 1 ∧
      primeFormPsi h CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one ⟨B, φ⟩ ∈ E ∧
      (∀ e ∈ E, e = 1 ∨
        e = primeFormPsi h CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one
          ⟨A, 1⟩ ∨
        e = primeFormPsi h CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one
          ⟨B, φ⟩ ∨
        e = primeFormPsi h CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one
          ⟨A * B, φ⟩) ∧
      ν ≠ 0 ∧ μ ≠ 0 ∧ ε ≠ 0 ∧
      ν • ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (P : Matrix (Fin n) (Fin n) K).map h.bar = P ∧
      μ • ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * P = P * X ∧
      ((P : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * P = ε • G ∧
      G.map h.bar = G ∧ (Gᵀ = G ∨ Gᵀ = -G) ∧ X.map h.bar = X ∧
      Xᵀ * G * X = h.norm μ • G ∧ X * X = α • 1 := by
  classical
  have hq : ¬(n = 3 ∧ p ^ f = 2) := by
    rintro ⟨-, hpf⟩
    have hdvd : p ∣ 2 := by
      rw [← hpf]
      exact dvd_pow_self p (by have := h.one_le; omega)
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hp2 : 2 ≤ p := h.prime.two_le
    omega
  have hC₁ : IsPrimeFormGram (1 : GL (Fin n) K) :=
    CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one
  let F := primeFormFieldFactor h hC₁ hn hq
  have hFker : F.ker = primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    ker_primeFormFieldFactor h hC₁ hn hq
  obtain ⟨b, hbE, hbF⟩ : ∃ b ∈ E, F b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hED fun x hx => by
      rw [← hFker, MonoidHom.mem_ker]
      exact hcon x hx
  have hb1 : b ≠ 1 := fun h1 => hbF (by rw [h1, map_one])
  have hbpow : b * b = 1 := by
    have := hE.2 b hbE
    simpa [pow_two] using this
  let φ : K ≃+* K := F b
  have hφ2 : φ * φ = 1 := by
    rw [show φ * φ = F (b * b) by rw [map_mul]]
    rw [hbpow, map_one]
  have hφbar : ∀ c, φ c = h.bar c := by
    rcases ringEquiv_eq_refl_or_bar h hφ2 with h1 | h1
    · exact absurd h1 hbF
    · exact h1
  have hFbar : ∀ e ∈ E, F e = 1 ∨ F e = φ := by
    intro e he
    have he2 : F e * F e = 1 := by
      have h2 : e * e = 1 := by simpa [pow_two] using hE.2 e he
      rw [← map_mul, h2, map_one]
    rcases ringEquiv_eq_refl_or_bar h he2 with h1 | h1
    · exact Or.inl h1
    · refine Or.inr (RingEquiv.ext fun c => ?_)
      rw [h1 c]
      exact (hφbar c).symm
  have hEfin : Fintype E :=
    @Fintype.ofFinite E (Nat.finite_of_card_ne_zero (α := E) (by rw [h4]; norm_num))
  have hcardE : @Fintype.card E hEfin = 4 := by
    rw [← Nat.card_eq_fintype_card, h4]
  have hex : ∃ e ∈ E, e ≠ (1 : MulAut (primeFormP h ((1 : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K))) ∧ e ≠ b := by
    by_contra hcon
    push Not at hcon
    have hsub : (@Finset.univ E hEfin) ⊆ ({1, ⟨b, hbE⟩} : Finset E) := by
      intro x _
      by_cases hx1 : (x : MulAut (primeFormP h ((1 : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K))) = 1
      · have hx : x = 1 := Subtype.ext hx1
        rw [hx]
        simp
      · have hxb : (x : MulAut (primeFormP h ((1 : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K))) = b := hcon x x.2 hx1
        have hx : x = ⟨b, hbE⟩ := Subtype.ext hxb
        rw [hx]
        simp
    have hcard := Finset.card_le_card hsub
    rw [@Finset.card_univ E hEfin, hcardE] at hcard
    have hne : ¬ (1 : E) = ⟨b, hbE⟩ := by
      intro h1
      exact hb1 (by simpa using (congrArg Subtype.val h1).symm)
    have h2 : ({1, ⟨b, hbE⟩} : Finset E).card ≤ 2 := by
      rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
    omega
  obtain ⟨e, heE, he1, heb⟩ := hex
  have haex : ∃ a : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)),
      a ∈ E ∧ a ≠ 1 ∧ F a = 1 ∧ a ≠ b := by
    rcases hFbar e heE with hFe | hFe
    · exact ⟨e, heE, he1, hFe, heb⟩
    · refine ⟨e * b, E.mul_mem heE hbE, ?_, ?_, ?_⟩
      · intro hprod
        apply heb
        have h1 : e = (e * b) * b := by rw [mul_assoc, hbpow, mul_one]
        rw [hprod, one_mul] at h1
        exact h1
      · rw [map_mul, hFe]
        exact hφ2
      · intro hprod
        apply he1
        exact mul_right_cancel (by rw [hprod, one_mul])
  obtain ⟨a, haE, ha1, haF, hab_ne⟩ := haex
  have haD : a ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [← hFker, MonoidHom.mem_ker]
    exact haF
  obtain ⟨A, hA⟩ : ∃ A, primeFormConjHom h ((1 : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) A = a := by
    rw [primeFormD] at haD
    exact MonoidHom.mem_range.mp haD
  have hAPsi : primeFormPsi h hC₁ ⟨A, 1⟩ = a := by
    rw [primeFormPsi_apply, hA, map_one, mul_one]
  obtain ⟨⟨B, ψ⟩, hBψ⟩ := primeFormPsi_surjective h hC₁ hn hq b
  have hψφ : ψ = φ := by
    have h1 : F (primeFormPsi h hC₁ ⟨B, ψ⟩) = ψ :=
      primeFormFieldFactor_psi h hC₁ hn hq ⟨B, ψ⟩
    rw [hBψ] at h1
    exact h1.symm
  have hBPsi : primeFormPsi h hC₁ ⟨B, φ⟩ = b := by
    rw [← hψφ]
    exact hBψ
  have ha2 : a * a = 1 := by
    have := hE.2 a haE
    simpa [pow_two] using this
  have hAA : primeFormPsi h hC₁ (⟨A, 1⟩ * ⟨A, 1⟩ : SD h hC₁) = 1 := by
    rw [map_mul, hAPsi, ha2]
  have hBB : primeFormPsi h hC₁ (⟨B, φ⟩ * ⟨B, φ⟩ : SD h hC₁) = 1 := by
    rw [map_mul, hBPsi, hbpow]
  obtain ⟨c₁, hA2⟩ := sq_eq_smul_one (h := h) (C := 1) hC₁ hn A hAA
  obtain ⟨c₂, hB2⟩ := b_sq_eq_smul_one (h := h) (C := 1) hC₁ hn hφbar B hBB
  have hcommE : ∀ x y : E, x * y = y * x := isMulCommutative_iff.mp hE.1
  have hab_comm : a * b = b * a := by
    have h1 := congrArg Subtype.val (hcommE ⟨a, haE⟩ ⟨b, hbE⟩)
    simpa using h1
  have hcommAB : primeFormPsi h hC₁ ⟨A, 1⟩ * primeFormPsi h hC₁ ⟨B, φ⟩ =
      primeFormPsi h hC₁ ⟨B, φ⟩ * primeFormPsi h hC₁ ⟨A, 1⟩ := by
    rw [hAPsi, hBPsi, hab_comm]
  obtain ⟨c₃, hAB⟩ := comm_eq_smul (h := h) (C := 1) hC₁ hn hφbar hcommAB
  obtain ⟨P, ν, μ, ε, α, G, X, hν, hμ, hε, hBP, hAP, hPG, hGr, hGs, hXr, hXG, hX2⟩ :=
    exists_real_form h (by omega)
      (unitary_mul (h := h) (A := A)) (unitary_mul (h := h) (A := B)) hA2 hB2 hAB
  have habE : a * b ∈ E := E.mul_mem haE hbE
  have hABpsi : primeFormPsi h hC₁ ⟨A * B, φ⟩ = a * b := by
    have h1 : (⟨A, 1⟩ * ⟨B, φ⟩ : SD h hC₁) = ⟨A * B, φ⟩ := by
      rw [SemidirectProduct.mul_def, map_one, MulAut.one_apply, one_mul]
    rw [← h1, map_mul, hAPsi, hBPsi]
  have hab1 : a * b ≠ 1 := by
    intro h1
    exact hab_ne (mul_right_cancel (by rw [h1, hbpow]))
  have haba : a * b ≠ a := by
    intro h1
    exact hb1 (mul_left_cancel (by rw [h1, mul_one]))
  have habb : a * b ≠ b := by
    intro h1
    exact ha1 (mul_right_cancel (by rw [h1, one_mul]))
  have h1a : (1 : E) ≠ ⟨a, haE⟩ := by
    intro h
    exact ha1 (by simpa using (congrArg Subtype.val h).symm)
  have h1b : (1 : E) ≠ ⟨b, hbE⟩ := by
    intro h
    exact hb1 (by simpa using (congrArg Subtype.val h).symm)
  have h1ab : (1 : E) ≠ ⟨a * b, habE⟩ := by
    intro h
    exact hab1 (by simpa using (congrArg Subtype.val h).symm)
  have hab' : (⟨a, haE⟩ : E) ≠ ⟨b, hbE⟩ := by
    intro h
    exact hab_ne (by simpa using congrArg Subtype.val h)
  have haab : (⟨a, haE⟩ : E) ≠ ⟨a * b, habE⟩ := by
    intro h
    exact haba (by simpa using (congrArg Subtype.val h).symm)
  have hbab : (⟨b, hbE⟩ : E) ≠ ⟨a * b, habE⟩ := by
    intro h
    exact habb (by simpa using (congrArg Subtype.val h).symm)
  let s1 : Finset E := {⟨a * b, habE⟩}
  let s2 : Finset E := insert ⟨b, hbE⟩ s1
  let s3 : Finset E := insert ⟨a, haE⟩ s2
  let s : Finset E := insert (1 : E) s3
  have hs1 : (1 : E) ∉ s3 := by
    simp only [s3, s2, s1, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h1a, h1b, h1ab⟩
  have hs2 : (⟨a, haE⟩ : E) ∉ s2 := by
    simp only [s2, s1, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hab', haab⟩
  have hs3 : (⟨b, hbE⟩ : E) ∉ s1 := by
    simp only [s1, Finset.mem_singleton]
    exact hbab
  have hs : s.card = 4 := by
    have e1 : s.card = s3.card + 1 := Finset.card_insert_of_notMem hs1
    have e2 : s3.card = s2.card + 1 := Finset.card_insert_of_notMem hs2
    have e3 : s2.card = s1.card + 1 := Finset.card_insert_of_notMem hs3
    have e4 : s1.card = 1 := Finset.card_singleton _
    omega
  have huniv : s = @Finset.univ E hEfin := by
    apply Finset.eq_of_subset_of_card_le
    · intro x _
      exact @Finset.mem_univ E hEfin x
    · rw [@Finset.card_univ E hEfin, hcardE, hs]
  have hcover : ∀ e ∈ E, e = 1 ∨ e = primeFormPsi h hC₁ ⟨A, 1⟩ ∨
      e = primeFormPsi h hC₁ ⟨B, φ⟩ ∨ e = primeFormPsi h hC₁ ⟨A * B, φ⟩ := by
    intro e he
    have hmem : (⟨e, he⟩ : E) ∈ s := by
      rw [huniv]
      exact @Finset.mem_univ E hEfin _
    simp only [s, s3, s2, s1, Finset.mem_insert, Finset.mem_singleton,
      Subtype.ext_iff] at hmem
    rcases hmem with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (h.trans hAPsi.symm))
    · exact Or.inr (Or.inr (Or.inl (h.trans hBPsi.symm)))
    · exact Or.inr (Or.inr (Or.inr (h.trans hABpsi.symm)))
  exact ⟨A, B, φ, P, ν, μ, ε, α, G, X, hφbar, by rw [hAPsi]; exact haE,
    by rw [hAPsi]; exact ha1, by rw [hBPsi]; exact hbE, hcover, hν, hμ, hε, hBP, hAP, hPG,
    hGr, hGs, hXr, hXG, hX2⟩

theorem exists_stable_isotropic_of_real (h : UnitaryFieldData p f K)
    {E : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))}
    {A B : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)} {φ : K ≃+* K}
    {P : GL (Fin n) K} {ν μ ε : K} {G X : Matrix (Fin n) (Fin n) K} (hφ : ∀ c, φ c = h.bar c)
    (hcover : ∀ e ∈ E, e = 1 ∨
      e = primeFormPsi h CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one ⟨A, 1⟩ ∨
      e = primeFormPsi h CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one ⟨B, φ⟩ ∨
      e = primeFormPsi h CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one
        ⟨A * B, φ⟩)
    (hν : ν ≠ 0) (hμ : μ ≠ 0)
    (hBP : ν • ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (P : Matrix (Fin n) (Fin n) K).map h.bar = P)
    (hAP : μ • ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * P = P * X)
    (hPG : ((P : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * P = ε • G)
    {W₁ : Submodule K (Fin n → K)} (hW₁ : W₁ ≠ ⊥)
    (hW₁i : ∀ x ∈ W₁, ∀ y ∈ W₁, gramForm h G x y = 0) (hW₁X : ∀ w ∈ W₁, X *ᵥ w ∈ W₁)
    (hW₁b : ∀ w ∈ W₁, (fun i => h.bar (w i)) ∈ W₁) :
    ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧
      (∀ x ∈ W, ∀ y ∈ W, gramForm h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x y = 0) ∧
      ∀ e ∈ E, ∃ (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        (φ : K ≃+* K),
        primeFormPsi h CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one
          ⟨A, φ⟩ = e ∧
        ∀ w ∈ W, ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => φ (w i)) ∈ W := by
  classical
  let C₁ : Matrix (Fin n) (Fin n) K := ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  let M : Matrix (Fin n) (Fin n) K := ((P : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  let Mi : Matrix (Fin n) (Fin n) K := ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hMiM : Mi * M = 1 := by
    show ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((P : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1
    rw [← Units.val_mul, inv_mul_cancel]
    exact Units.val_one
  let fP : (Fin n → K) →ₗ[K] (Fin n → K) := Matrix.toLin' M
  have hfP : ∀ x : Fin n → K, fP x = M *ᵥ x := fun x => rfl
  have hPbar : ∀ x : Fin n → K,
      (fun i => h.bar (fP x i)) = M.map h.bar *ᵥ (fun i => h.bar (x i)) := by
    intro x
    rw [hfP]
    exact (map_mulVec h.bar M x).symm
  have hAP' : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M = μ⁻¹ • (M * X) := by
    have hh := hAP
    rw [Matrix.smul_mul] at hh
    calc ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M
        = μ⁻¹ • (μ • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M)) := by
          rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
      _ = μ⁻¹ • (M * X) := by rw [hh]
  have hBP' : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M.map h.bar = ν⁻¹ • M := by
    have hh := hBP
    rw [Matrix.smul_mul] at hh
    calc ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M.map h.bar
        = ν⁻¹ • (ν • (((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M.map h.bar)) := by
          rw [smul_smul, inv_mul_cancel₀ hν, one_smul]
      _ = ν⁻¹ • M := by rw [hh]
  have hAstep : ∀ x : Fin n → K,
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (fP x) = fP (μ⁻¹ • (X *ᵥ x)) := by
    intro x
    rw [hfP, hfP, Matrix.mulVec_mulVec, hAP', Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_smul]
  have hBstep : ∀ x : Fin n → K,
      ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => φ (fP x i))
        = fP (ν⁻¹ • (fun i => h.bar (x i))) := by
    intro x
    have hφe : (fun i => φ (fP x i)) = (fun i => h.bar (fP x i)) := by
      funext i
      exact hφ (fP x i)
    rw [hφe, hPbar x, Matrix.mulVec_mulVec, hBP', Matrix.smul_mulVec, hfP, Matrix.mulVec_smul]
  refine ⟨W₁.map fP, ?_, ?_, ?_⟩
  · intro hbot
    obtain ⟨x, hx, hx0⟩ := W₁.exists_mem_ne_zero_of_ne_bot hW₁
    have hmem : fP x ∈ (⊥ : Submodule K (Fin n → K)) := by
      rw [← hbot]
      exact Submodule.mem_map_of_mem hx
    rw [Submodule.mem_bot] at hmem
    apply hx0
    have h1 : Mi *ᵥ (fP x) = Mi *ᵥ (0 : Fin n → K) := by rw [hmem]
    rwa [hfP, Matrix.mulVec_mulVec, hMiM, Matrix.one_mulVec, Matrix.mulVec_zero] at h1
  · intro x hx y hy
    obtain ⟨x₁, hx₁, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨y₁, hy₁, rfl⟩ := Submodule.mem_map.mp hy
    show gramForm h C₁ (fP x₁) (fP y₁) = 0
    rw [hfP, hfP, gramForm_mulVec]
    rw [show (M.map h.bar)ᵀ * C₁ * M = ε • G from by
      rw [show C₁ = 1 from rfl, Matrix.mul_one]
      exact hPG]
    rw [show gramForm h (ε • G) x₁ y₁ = ε * gramForm h G x₁ y₁ from by
      rw [gramForm_apply, gramForm_apply, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]]
    rw [hW₁i x₁ hx₁ y₁ hy₁, mul_zero]
  · intro e he
    rcases hcover e he with h1 | h2 | h3 | h4
    · rw [h1]
      refine ⟨1, 1, ?_, ?_⟩
      · simp
      · intro w hw
        simpa using hw
    · rw [h2]
      refine ⟨A, 1, ?_, ?_⟩
      · rfl
      · intro w hw
        obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hw
        have h1w : (fun i => (1 : K ≃+* K) (fP x i)) = fP x := by simp
        rw [h1w, hAstep x]
        exact Submodule.mem_map_of_mem (Submodule.smul_mem _ _ (hW₁X x hx))
    · rw [h3]
      refine ⟨B, φ, ?_, ?_⟩
      · rfl
      · intro w hw
        obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hw
        rw [hBstep x]
        exact Submodule.mem_map_of_mem (Submodule.smul_mem _ _ (hW₁b x hx))
    · rw [h4]
      refine ⟨A * B, φ, rfl, ?_⟩
      intro w hw
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hw
      have hABm : (((A * B : primeFormUnitary h C₁) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
            = ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        simp
      rw [hABm, ← Matrix.mulVec_mulVec, hBstep x,
        hAstep (ν⁻¹ • (fun i => h.bar (x i)))]
      refine Submodule.mem_map_of_mem ?_
      have hmem4 : μ⁻¹ • (X *ᵥ (ν⁻¹ • (fun i => h.bar (x i)))) ∈ W₁ :=
        Submodule.smul_mem _ _ (hW₁X _ (Submodule.smul_mem _ _ (hW₁b x hx)))
      simpa only [Matrix.smul_mulVec] using hmem4

theorem exists_stable_isotropic_of_not_le_primeFormD (h : UnitaryFieldData p f K)
    (hp : p ≠ 2) (hn : 5 ≤ n)
    {E : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))}
    (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4)
    (hED : ¬ E ≤ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧
      (∀ x ∈ W, ∀ y ∈ W, gramForm h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x y = 0) ∧
      ∀ e ∈ E, ∃ (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
        (φ : K ≃+* K),
        primeFormPsi h CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one
          ⟨A, φ⟩ = e ∧
        ∀ w ∈ W, ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => φ (w i)) ∈ W := by
  obtain ⟨A, B, φ, P, ν, μ, ε, α, G, X, hφ, -, -, -, hcover, hν, hμ, -, hBP, hAP,
    hPG, hGr, hGs, hXr, hXG, hX2⟩ := exists_graph_descent h hp (by omega) hE h4 hED
  obtain ⟨W₁, hW₁, hW₁i, hW₁X, hW₁b⟩ := exists_real_isotropic_stable h hn hGr hXr hGs hXG hX2
  exact exists_stable_isotropic_of_real h hφ hcover hν hμ hBP hAP hPG hW₁ hW₁i hW₁X hW₁b

end CFSG.LocalAnalysis.WeakClosure81.UOuter

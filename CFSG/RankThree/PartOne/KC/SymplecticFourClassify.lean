module

public import CFSG.RankThree.PartOne.KC.SymplecticAdaptedBasis
public import CFSG.RankThree.PartOne.KC.SymplecticRegularUnipotent

public section

namespace CFSG.RankThree.PartOne.KCSymplecticInner

open Matrix CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCExpLog CFSG.RankThree.PartOne.KCSymplectic
open CFSG.RankThree.PartOne.KCSymplecticAdapted

variable {K : Type} [Field K]

noncomputable abbrev omegaJ (K : Type) [Field K] :
    (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K) →ₗ[K] K :=
  Matrix.toBilin' (formJ 2 K)

theorem omegaJ_apply (x y : Fin 2 ⊕ Fin 2 → K) : omegaJ K x y = x ⬝ᵥ (formJ 2 K *ᵥ y) :=
  Matrix.toBilin'_apply' _ _ _

theorem omegaJ_self (x : Fin 2 ⊕ Fin 2 → K) : omegaJ K x x = 0 := by
  rw [omegaJ_apply]
  simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, formJ, mul_comm]
  ring

theorem omegaJ_nondeg (x : Fin 2 ⊕ Fin 2 → K) (h : ∀ y, omegaJ K x y = 0) : x = 0 := by
  have h1 : x ᵥ* formJ 2 K = 0 := by
    refine dotProduct_eq_zero _ fun w => ?_
    rw [← Matrix.dotProduct_mulVec]
    exact (omegaJ_apply x w).symm.trans (h w)
  calc x = x ᵥ* (formJ 2 K * -(formJ 2 K)) := by rw [formJ_mul_neg, Matrix.vecMul_one]
    _ = 0 := by rw [← Matrix.vecMul_vecMul, h1, Matrix.zero_vecMul]

theorem dotProduct_mulVec_transpose (N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (x w : Fin 2 ⊕ Fin 2 → K) : (N *ᵥ x) ⬝ᵥ w = x ⬝ᵥ (Nᵀ *ᵥ w) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem omegaJ_skew {N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hNJ : Nᵀ * formJ 2 K + formJ 2 K * N = 0) (x y : Fin 2 ⊕ Fin 2 → K) :
    omegaJ K (N *ᵥ x) y = - omegaJ K x (N *ᵥ y) := by
  rw [omegaJ_apply, omegaJ_apply]
  have h1 : Nᵀ * formJ 2 K = -(formJ 2 K * N) := eq_neg_of_add_eq_zero_left hNJ
  rw [dotProduct_mulVec_transpose, Matrix.mulVec_mulVec, h1, Matrix.neg_mulVec,
    ← Matrix.mulVec_mulVec, dotProduct_neg]

theorem omegaJ_comm (x y : Fin 2 ⊕ Fin 2 → K) : omegaJ K x y = - omegaJ K y x := by
  have h := omegaJ_self (K := K) (x + y)
  simp only [map_add, LinearMap.add_apply, omegaJ_self x, omegaJ_self y, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

theorem setup_of_chain {N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hNJ : Nᵀ * formJ 2 K + formJ 2 K * N = 0) {c : Fin 4 → (Fin 2 ⊕ Fin 2 → K)}
    (hli : LinearIndependent K c) : Setup (omegaJ K) (Matrix.toLin' N) c where
  alt := omegaJ_self
  nondeg := omegaJ_nondeg
  skew x y := by simpa only [Matrix.toLin'_apply] using omegaJ_skew hNJ x y
  li := hli
  span := by
    apply hli.span_eq_top_of_card_eq_finrank'
    rw [Module.finrank_fintype_fun_eq_card]
    simp

@[expose] def symBasisMat {α : Type*} (e f : Fin 2 → (Fin 2 ⊕ Fin 2 → α)) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) α :=
  Matrix.of fun r k => Sum.elim e f k r

theorem symBasisMat_apply {α : Type*} (e f : Fin 2 → (Fin 2 ⊕ Fin 2 → α)) (r k : Fin 2 ⊕ Fin 2) :
    symBasisMat e f r k = Sum.elim e f k r :=
  rfl

theorem transpose_mul_mul_apply {ι : Type*} [Fintype ι] (A J : Matrix ι ι K) (k l : ι) :
    (Aᵀ * J * A) k l = (fun r => A r k) ⬝ᵥ (J *ᵥ fun s => A s l) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem symBasisMat_gram {e f : Fin 2 → (Fin 2 ⊕ Fin 2 → K)}
    (hee : ∀ i j, omegaJ K (e i) (e j) = 0) (hff : ∀ i j, omegaJ K (f i) (f j) = 0)
    (hef : ∀ i j, omegaJ K (e i) (f j) = if i = j then 1 else 0) :
    (symBasisMat e f)ᵀ * formJ 2 K * symBasisMat e f = formJ 2 K := by
  ext k l
  rw [transpose_mul_mul_apply]
  have key : ∀ k l, ((fun r => symBasisMat e f r k) ⬝ᵥ
      (formJ 2 K *ᵥ fun s => symBasisMat e f s l)) = omegaJ K (Sum.elim e f k) (Sum.elim e f l) :=
    fun k l => (omegaJ_apply _ _).symm
  rw [key]
  rcases k with i | i <;> rcases l with j | j
  · simp [formJ, hee]
  · simp [formJ, hef, Matrix.one_apply]
  · rw [omegaJ_comm]
    simp [formJ, hef, Matrix.one_apply, eq_comm]
  · simp [formJ, hff]

theorem symBasisMat_mulVec (e f : Fin 2 → (Fin 2 ⊕ Fin 2 → K)) (v : Fin 2 ⊕ Fin 2 → K) :
    symBasisMat e f *ᵥ v = ∑ i, v (Sum.inl i) • e i + ∑ j, v (Sum.inr j) • f j := by
  ext r
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, symBasisMat_apply, mul_comm]

theorem mul_eq_of_mulVec_col {ι : Type*} [Fintype ι] {N A N' : Matrix ι ι K}
    (h : ∀ k, N *ᵥ (fun r => A r k) = A *ᵥ (fun s => N' s k)) : N * A = A * N' := by
  ext r k
  have := congrFun (h k) r
  simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this

theorem exists_isometry_of_chain_transvection {N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hNJ : Nᵀ * formJ 2 K + formJ 2 K * N = 0) {c : Fin 4 → (Fin 2 ⊕ Fin 2 → K)}
    (hli : LinearIndependent K c)
    (h0 : N *ᵥ c 0 = 0) (h1 : N *ᵥ c 1 = 0) (h2 : N *ᵥ c 2 = 0) (h3 : N *ᵥ c 3 = c 0) :
    ∃ (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (γ : K), γ ≠ 0 ∧
      Aᵀ * formJ 2 K * A = formJ 2 K ∧
      N * A = A * (γ • Matrix.single (Sum.inl 0) (Sum.inr 0) (1 : K)) := by
  have S := setup_of_chain hNJ hli
  simp only [← Matrix.toLin'_apply] at h0 h1 h2 h3
  obtain ⟨e, f, γ, hγ, hee, hff, hef, he0, he1, hf1, hf0⟩ := S.exists_adapted_transvection
    h0 h1 h2 h3
  simp only [Matrix.toLin'_apply] at he0 he1 hf1 hf0
  refine ⟨symBasisMat e f, γ, hγ, symBasisMat_gram hee hff hef, ?_⟩
  apply mul_eq_of_mulVec_col
  intro k
  rw [symBasisMat_mulVec]
  rcases k with i | j
  · fin_cases i
    · simp [symBasisMat_apply, he0]
    · simp [symBasisMat_apply, he1]
  · fin_cases j
    · simp [symBasisMat_apply, hf0, Matrix.single_apply]
    · simp [symBasisMat_apply, hf1]

theorem exists_isometry_of_chain_square_zero {N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hNJ : Nᵀ * formJ 2 K + formJ 2 K * N = 0) (h2 : (2 : K) ≠ 0)
    {c : Fin 4 → (Fin 2 ⊕ Fin 2 → K)} (hli : LinearIndependent K c)
    (h0 : N *ᵥ c 0 = 0) (h1 : N *ᵥ c 1 = 0) (h2' : N *ᵥ c 2 = c 0) (h3 : N *ᵥ c 3 = c 1) :
    ∃ (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (D : Matrix (Fin 2) (Fin 2) K),
      Aᵀ * formJ 2 K * A = formJ 2 K ∧ Dᵀ = D ∧ IsUnit D ∧
      N * A = A * Matrix.fromBlocks 0 D 0 0 := by
  have S := setup_of_chain hNJ hli
  simp only [← Matrix.toLin'_apply] at h0 h1 h2' h3
  obtain ⟨e, f, D, hee, hff, hef, he, hf, hD, hDu⟩ := S.exists_adapted_square_zero h2 h0 h1 h2'
    h3
  simp only [Matrix.toLin'_apply] at he hf
  refine ⟨symBasisMat e f, D, symBasisMat_gram hee hff hef, hD, hDu, ?_⟩
  apply mul_eq_of_mulVec_col
  intro k
  rw [symBasisMat_mulVec]
  rcases k with i | j
  · simp [symBasisMat_apply, he]
  · simp [symBasisMat_apply, hf]

theorem not_chain_three_one_mat {N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hNJ : Nᵀ * formJ 2 K + formJ 2 K * N = 0) (h2 : (2 : K) ≠ 0)
    {c : Fin 4 → (Fin 2 ⊕ Fin 2 → K)} (hli : LinearIndependent K c)
    (h0 : N *ᵥ c 0 = 0) (h1 : N *ᵥ c 1 = c 0) (h2' : N *ᵥ c 2 = c 1) (h3 : N *ᵥ c 3 = 0) :
    False := by
  have S := setup_of_chain hNJ hli
  simp only [← Matrix.toLin'_apply] at h0 h1 h2' h3
  exact S.not_chain_three_one h2 h0 h1 h2' h3

theorem exists_statedSp_eq_of_isometry {r : ℕ}
    {A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (hA : Aᵀ * formJ r K * A = formJ r K) :
    ∃ g : StatedSp r K, spMat g = A := by
  have hL : (-(formJ r K) * Aᵀ * formJ r K) * A = 1 := by
    calc (-(formJ r K) * Aᵀ * formJ r K) * A = -(formJ r K) * (Aᵀ * formJ r K * A) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hA]; exact neg_formJ_mul r K
  have hR : A * (-(formJ r K) * Aᵀ * formJ r K) = 1 := mul_eq_one_comm.mp hL
  exact ⟨⟨⟨A, _, hR, hL⟩, SymplecticTorusWeyl.mem_statedSp_iff.mpr hA⟩, rfl⟩

theorem expMat_mul_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {N A N' : Matrix ι ι K} (d : ℕ)
    (h : N * A = A * N') : expMat d N * A = A * expMat d N' := by
  have hp : ∀ j : ℕ, N ^ j * A = A * N' ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]
  simp only [expMat, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, hp]

theorem expMat_eq_one_add_of_mul_self_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N' : Matrix ι ι K} (h : N' * N' = 0) : expMat (2 * 2) N' = 1 + N' := by
  have h2 : N' ^ 2 = 0 := by rw [pow_two]; exact h
  have h3 : N' ^ 3 = 0 := by rw [pow_succ, h2, zero_mul]
  simp [expMat, Finset.sum_range_succ, h2, h3, Nat.factorial]

theorem exists_conj_of_isometry_mul_eq {u : StatedSp 2 K}
    {N N' A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hu : spMat u = expMat (2 * 2) N) (hA : Aᵀ * formJ 2 K * A = formJ 2 K)
    (hNA : N * A = A * N') (hN'2 : N' * N' = 0) :
    ∃ s w : StatedSp 2 K, u = s * w * s⁻¹ ∧ spMat w = 1 + N' := by
  obtain ⟨s, hs⟩ := exists_statedSp_eq_of_isometry hA
  refine ⟨s, s⁻¹ * u * s, by group, ?_⟩
  have h1 : spMat u * A = A * (1 + N') := by
    rw [hu, ← expMat_eq_one_add_of_mul_self_eq_zero hN'2]
    exact expMat_mul_eq _ hNA
  calc spMat (s⁻¹ * u * s) = spMat s⁻¹ * (spMat u * spMat s) := by
        rw [spMat_mul, spMat_mul, Matrix.mul_assoc]
    _ = spMat s⁻¹ * (A * (1 + N')) := by rw [hs, h1]
    _ = 1 + N' := by rw [← Matrix.mul_assoc, ← hs, spMat_inv_mul, Matrix.one_mul]

theorem _root_.CFSG.RankThree.PartOne.NormalPrimeComplementsTrivial.of_conj_mul
    {T : Type*} [Group T] {p : ℕ} (s t : T)
    (h : NormalPrimeComplementsTrivial p (MulAut.conj t)) :
    NormalPrimeComplementsTrivial p (MulAut.conj (s * t * s⁻¹)) := by
  have h' := h.map_mulEquiv (MulAut.conj s)
  rwa [CFSG.RankThree.PartOne.KCUnitaryDefining.mulAutCongr_conj] at h'

end CFSG.RankThree.PartOne.KCSymplecticInner

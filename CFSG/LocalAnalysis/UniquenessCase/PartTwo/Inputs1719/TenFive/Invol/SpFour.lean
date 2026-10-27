module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SpFourOrbit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SpCases
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SpQv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (formJ gsp conjAut fieldAut conjSp
  coe_conjSp conjAut_proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour (tau tau_mul_tau tau_congr coe_tau)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

variable {K : Type} [Field K]

private lemma two_ne_zero_of_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p] :
    (2 : K) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h)
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hge : 2 ≤ p := hp.two_le
  omega

private lemma transpose_mul_formJ (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) {d : K}
    (hA : Mᵀ * formJ 2 K * M = d • formJ 2 K) (hd : M * M = d • 1) (hd0 : d ≠ 0) :
    Mᵀ * formJ 2 K = formJ 2 K * M := by
  have h : d • (Mᵀ * formJ 2 K) = d • (formJ 2 K * M) :=
    calc d • (Mᵀ * formJ 2 K) = Mᵀ * formJ 2 K * (d • 1) := by
          rw [Matrix.mul_smul, Matrix.mul_one]
      _ = Mᵀ * formJ 2 K * (M * M) := by rw [hd]
      _ = (Mᵀ * formJ 2 K * M) * M := (Matrix.mul_assoc _ _ _).symm
      _ = (d • formJ 2 K) * M := by rw [hA]
      _ = d • (formJ 2 K * M) := Matrix.smul_mul _ _ _
  have hzero : d • (Mᵀ * formJ 2 K - formJ 2 K * M) = 0 := by
    rw [smul_sub, h, sub_self]
  rcases smul_eq_zero.mp hzero with h' | h'
  · exact absurd h' hd0
  · exact sub_eq_zero.mp h'

private lemma spForm_mulVec_self (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (hM : Mᵀ * formJ 2 K = formJ 2 K * M) (h2 : (2 : K) ≠ 0) (y : Fin 2 ⊕ Fin 2 → K) :
    spForm y (M *ᵥ y) = 0 := by
  have h1 : spForm y (M *ᵥ y) = spForm (M *ᵥ y) y := by
    show y ⬝ᵥ (formJ 2 K *ᵥ (M *ᵥ y)) = (M *ᵥ y) ⬝ᵥ (formJ 2 K *ᵥ y)
    rw [Matrix.mulVec_mulVec, ← hM, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec,
      dotProduct_comm]
  have h2' : spForm (M *ᵥ y) y = -spForm y (M *ᵥ y) := spForm_swap y (M *ᵥ y)
  have hb : (2 : K) * spForm y (M *ᵥ y) = 0 := by
    rw [two_mul]
    nth_rewrite 1 [h1.trans h2']
    exact neg_add_cancel _
  exact (mul_eq_zero.mp hb).resolve_left h2

private lemma spForm_mulVec_adjoint (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (hM : Mᵀ * formJ 2 K = formJ 2 K * M) (y z : Fin 2 ⊕ Fin 2 → K) :
    spForm y (M *ᵥ z) = spForm (M *ᵥ y) z := by
  show y ⬝ᵥ (formJ 2 K *ᵥ (M *ᵥ z)) = (M *ᵥ y) ⬝ᵥ (formJ 2 K *ᵥ z)
  rw [Matrix.mulVec_mulVec, ← hM, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec,
    dotProduct_comm]

private lemma no_eigenvector (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) {d : K}
    (hd : M * M = d • 1) (hdsq : ¬ IsSquare d) {a : K} {y : Fin 2 ⊕ Fin 2 → K}
    (hy : y ≠ 0) (heig : M *ᵥ y = a • y) : False := by
  have h1 : M *ᵥ (M *ᵥ y) = d • y := by
    rw [Matrix.mulVec_mulVec, hd, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [heig, Matrix.mulVec_smul, heig, smul_smul] at h1
  have h2 : (a * a - d) • y = 0 := by
    rw [sub_smul, h1, sub_self]
  have h3 : a * a = d := by
    rcases smul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hy
  exact hdsq ⟨a, h3.symm⟩

private lemma single_notMem_span (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) {d : K}
    (hd : M * M = d • 1) (hdsq : ¬ IsSquare d) :
    (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K) ∉
      Submodule.span K {M *ᵥ (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K)} := by
  intro hmem
  have hv0 : (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K) ≠ 0 := by
    intro h
    have := congrFun h (Sum.inl 0)
    simp at this
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hMu : M *ᵥ (M *ᵥ (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K)) =
      d • (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K) := by
    rw [Matrix.mulVec_mulVec, hd, Matrix.smul_mulVec, Matrix.one_mulVec]
  have heig : M *ᵥ (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K) =
      (c * d) • (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K) := by
    calc M *ᵥ (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K)
        = M *ᵥ (c • (M *ᵥ (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K))) := by rw [hc]
      _ = c • (M *ᵥ (M *ᵥ (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K))) := by
          rw [Matrix.mulVec_smul]
      _ = c • (d • (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K)) := by rw [hMu]
      _ = (c * d) • (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K) := by rw [smul_smul]
  exact no_eigenvector M hd hdsq hv0 heig

private noncomputable def frameMat (c₀ c₁ c₂ c₃ : Fin 2 ⊕ Fin 2 → K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.of fun i j =>
    Sum.elim (fun a : Fin 2 => (![c₀, c₁] a) i) (fun a : Fin 2 => (![c₂, c₃] a) i) j

omit [Field K] in
private lemma frameMat_col_zero (c₀ c₁ c₂ c₃ : Fin 2 ⊕ Fin 2 → K) :
    (frameMat c₀ c₁ c₂ c₃).col (Sum.inl 0) = c₀ := by
  funext i
  simp [frameMat, Matrix.col]

omit [Field K] in
private lemma frameMat_col_one (c₀ c₁ c₂ c₃ : Fin 2 ⊕ Fin 2 → K) :
    (frameMat c₀ c₁ c₂ c₃).col (Sum.inl 1) = c₁ := by
  funext i
  simp [frameMat, Matrix.col]

omit [Field K] in
private lemma frameMat_col_two (c₀ c₁ c₂ c₃ : Fin 2 ⊕ Fin 2 → K) :
    (frameMat c₀ c₁ c₂ c₃).col (Sum.inr 0) = c₂ := by
  funext i
  simp [frameMat, Matrix.col]

omit [Field K] in
private lemma frameMat_col_three (c₀ c₁ c₂ c₃ : Fin 2 ⊕ Fin 2 → K) :
    (frameMat c₀ c₁ c₂ c₃).col (Sum.inr 1) = c₃ := by
  funext i
  simp [frameMat, Matrix.col]

private lemma frameMat_entry (c₀ c₁ c₂ c₃ : Fin 2 ⊕ Fin 2 → K) (i k : Fin 2 ⊕ Fin 2) :
    ((frameMat c₀ c₁ c₂ c₃)ᵀ * formJ 2 K * frameMat c₀ c₁ c₂ c₃) i k =
      spForm ((frameMat c₀ c₁ c₂ c₃).col i) ((frameMat c₀ c₁ c₂ c₃).col k) := by
  simp [Matrix.mul_apply, spForm, Matrix.mulVec, dotProduct,
    Matrix.col]
  ring

private lemma spForm_smul_right (y : Fin 2 ⊕ Fin 2 → K) (c : K) (z : Fin 2 ⊕ Fin 2 → K) :
    spForm y (c • z) = c * spForm y z := by
  simp [spForm, Matrix.mulVec_smul]

private lemma spT_smul_smul (c : K) (x y : Fin 2 ⊕ Fin 2 → K) :
    spT (c • x) (c • y) = (c * c) • spT x y := by
  rw [spT, spT, Matrix.mulVec_smul, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul]

private lemma isSp_spT (h2 : (2 : K) ≠ 0) (c : Fin 2 ⊕ Fin 2 → K) :
    (spT c c)ᵀ * formJ 2 K + formJ 2 K * spT c c = 0 := by
  have h : (2 : K) • spT c c = spN c c := by rw [spN, two_smul]
  have hsp := isSp_spN c c
  rw [← h, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add] at hsp
  rcases smul_eq_zero.mp hsp with h' | h'
  · exact absurd h' h2
  · exact h'

private lemma frameN_mulVec (d : K) (v u y : Fin 2 ⊕ Fin 2 → K) :
    (d • spT v v - spT u u) *ᵥ y = (d * spForm y v) • v - spForm y u • u := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, spT_mulVec, spT_mulVec, smul_smul]

private noncomputable def skewS (d : K) : Matrix (Fin 2) (Fin 2) K := !![ -d, 0; 0, 1]

private lemma skewS_transpose (d : K) : (skewS d)ᵀ = skewS d := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skewS]

private lemma skewS_aniso {d : K} (hdsq : ¬ IsSquare d) :
    ∀ v : Fin 2 → K, v ≠ 0 → v ⬝ᵥ (skewS d *ᵥ v) ≠ 0 := by
  intro v hv h
  simp only [skewS, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h
  rw [show (!![-d, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) 0 0 = -d from by simp,
    show (!![-d, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 from by simp,
    show (!![-d, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 from by simp,
    show (!![-d, 0; 0, 1] : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 from by simp] at h
  have h1 : v 1 * v 1 = d * (v 0 * v 0) := by
    have h' : v 0 * (-d * v 0 + 0 * v 1) + v 1 * (0 * v 0 + 1 * v 1) =
        v 1 * v 1 - d * (v 0 * v 0) := by ring
    rw [h'] at h
    exact sub_eq_zero.mp h
  by_cases hv0 : v 0 = 0
  · have hv1 : v 1 = 0 := by
      rw [hv0, mul_zero, mul_zero] at h1
      rcases mul_eq_zero.mp h1 with h' | h'
      · exact h'
      · exact h'
    apply hv
    funext i
    fin_cases i
    · exact hv0
    · exact hv1
  · have h3 : v 0 * v 0 ≠ 0 := mul_ne_zero hv0 hv0
    have hx : (v 1 * (v 0)⁻¹) * (v 1 * (v 0)⁻¹) = d := by
      have h4 : (v 1 * (v 0)⁻¹) * (v 1 * (v 0)⁻¹) = (v 1 * v 1) * (v 0 * v 0)⁻¹ := by
        rw [_root_.mul_inv_rev]
        ring
      rw [h4, h1, mul_assoc, mul_inv_cancel₀ h3, mul_one]
    exact hdsq ⟨v 1 * (v 0)⁻¹, hx.symm⟩

private lemma tau_zero : tau (C := (0 : Matrix (Fin 2) (Fin 2) K)) (transpose_zero) = 1 := by
  apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
  rw [coe_tau]
  simp

private lemma tau_pow {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) (n : ℕ) :
    tau hC ^ n = tau (C := n • C) (by
      induction n with
      | zero => rw [zero_nsmul, transpose_zero]
      | succ n ih => rw [succ_nsmul, Matrix.transpose_add, ih, hC]) := by
  induction n with
  | zero => rw [pow_zero]; simpa using tau_zero.symm
  | succ n ih =>
      rw [pow_succ, ih, tau_mul_tau]
      exact tau_congr _ _ (by rw [succ_nsmul])

theorem exists_inv_sp_four [Finite K] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p]
    (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) (A : gsp 2 K) {d : K}
    (hA : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * formJ 2 K *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • formJ 2 K)
    (hd : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • 1)
    (hdsq : ¬ IsSquare d) :
    ∃ x : StatedProj (StatedSp 2 K), orderOf x = p ∧
      (conjAut 2 K A * fieldAut 2 K 1) x = x⁻¹ ∧ (IsSpecialGood p x ∨ IsOrbitGood p x) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_ne_two hp hp2
  set M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
    ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hM
  have hA' : Mᵀ * formJ 2 K * M = d • formJ 2 K := by rw [hM]; exact hA
  have hd' : M * M = d • 1 := by rw [hM]; exact hd
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hdsq ⟨0, by rw [mul_zero]⟩
  have hMs : Mᵀ * formJ 2 K = formJ 2 K * M := transpose_mul_formJ M hA' hd' hd0
  set v : Fin 2 ⊕ Fin 2 → K := (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K) with hv
  set u : Fin 2 ⊕ Fin 2 → K := M *ᵥ v with hu
  have hnotmem : v ∉ Submodule.span K ({u} : Set (Fin 2 ⊕ Fin 2 → K)) := by
    rw [hu, hv]
    exact single_notMem_span M hd' hdsq
  obtain ⟨w, hw_sep, hvw⟩ :=
    exists_spForm_sep (r := 2) (S := ({u} : Set (Fin 2 ⊕ Fin 2 → K))) (c := v) hnotmem
  have huw : spForm u w = 0 := hw_sep u (Set.mem_singleton u)
  set z : Fin 2 ⊕ Fin 2 → K := d⁻¹ • (M *ᵥ w) with hz
  have hvv : spForm v v = 0 := spForm_self v
  have huu : spForm u u = 0 := spForm_self u
  have hww : spForm w w = 0 := spForm_self w
  have hzz : spForm z z = 0 := spForm_self z
  have hvu : spForm v u = 0 := by rw [hu]; exact spForm_mulVec_self M hMs h2 v
  have hvz : spForm v z = 0 := by
    rw [hz, spForm_smul_right, spForm_mulVec_adjoint M hMs v w, ← hu, huw, mul_zero]
  have hwz : spForm w z = 0 := by
    rw [hz, spForm_smul_right, spForm_mulVec_self M hMs h2 w, mul_zero]
  have huz : spForm u z = 1 := by
    rw [hu, hz, spForm_smul_right, spForm_mulVec hA', hvw, mul_one, inv_mul_cancel₀ hd0]
  have huv : spForm u v = 0 := by rw [spForm_swap v u, hvu, neg_zero]
  have hwv : spForm w v = -1 := by rw [spForm_swap v w, hvw]
  have hzv : spForm z v = 0 := by rw [spForm_swap v z, hvz, neg_zero]
  have hwu : spForm w u = 0 := by rw [spForm_swap u w, huw, neg_zero]
  have hzu : spForm z u = -1 := by rw [spForm_swap u z, huz]
  have hzw : spForm z w = 0 := by rw [spForm_swap w z, hwz, neg_zero]
  set N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := d • spT v v - spT u u with hN
  have hsN : Nᵀ * formJ 2 K + formJ 2 K * N = 0 := by
    have h1 : (d • spT v v)ᵀ * formJ 2 K + formJ 2 K * (d • spT v v) = 0 := by
      rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add,
        isSp_spT h2 v, smul_zero]
    have h2' : (spT u u)ᵀ * formJ 2 K + formJ 2 K * spT u u = 0 := isSp_spT h2 u
    calc (d • spT v v - spT u u)ᵀ * formJ 2 K + formJ 2 K * (d • spT v v - spT u u)
        = ((d • spT v v)ᵀ * formJ 2 K + formJ 2 K * (d • spT v v)) -
          ((spT u u)ᵀ * formJ 2 K + formJ 2 K * spT u u) := by
          rw [Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub]
          abel
      _ = 0 := by rw [h1, h2', sub_zero]
  have hNN : N * N = 0 := by
    rw [hN, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_smul, spT_mul_spT, spT_mul_spT, spT_mul_spT, spT_mul_spT]
    simp [hvv, huu, hvu, huv]
  have hMu : M *ᵥ u = d • v := by
    rw [hu, Matrix.mulVec_mulVec, hd', Matrix.smul_mulVec, Matrix.one_mulVec]
  have hconjT : ∀ c : Fin 2 ⊕ Fin 2 → K,
      M * spT c c * ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d⁻¹ • spT (M *ᵥ c) (M *ᵥ c) := by
    intro c
    have h := conj_spT (A : GL (Fin 2 ⊕ Fin 2) K) (μ := d) hA c c
    rwa [← hM] at h
  have hconjN : M * N * ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -N := by
    have hu' : M * spT u u * ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • spT v v := by
      have h := hconjT u
      rw [hMu, spT_smul_smul, smul_smul,
        show d⁻¹ * (d * d) = d from by rw [← mul_assoc, inv_mul_cancel₀ hd0, one_mul]] at h
      exact h
    rw [hN, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hconjT v, hu',
      smul_smul, show d * d⁻¹ = 1 from mul_inv_cancel₀ hd0, one_smul]
    abel
  set P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := frameMat v u w z with hP
  have hPJ : Pᵀ * formJ 2 K * P = formJ 2 K := by
    ext i k
    rw [hP, frameMat_entry]
    rcases i with a | a <;> rcases k with b | b <;> fin_cases a <;> fin_cases b <;>
      simp [frameMat_col_zero, frameMat_col_one, frameMat_col_two, frameMat_col_three,
        hvv, hvu, hvw, hvz, huv, huu, huw, huz, hwv, hwu, hww, hwz, hzv, hzu, hzw, hzz,
        formJ]
  have hJunit : IsUnit (formJ 2 K) := by
    have h1 : formJ 2 K * formJ 2 K = fromBlocks (-1) 0 0 (-1) := by
      rw [formJ, Matrix.fromBlocks_multiply]
      simp
    have h2 : (fromBlocks (-1 : Matrix (Fin 2) (Fin 2) K) 0 0 (-1) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -1 := by
      ext i j
      rcases i with a | a <;> rcases j with b | b <;> fin_cases a <;> fin_cases b <;>
        simp
    have h : formJ 2 K * formJ 2 K = -1 := by
      rw [h1, h2]
    have h' : IsUnit (formJ 2 K * formJ 2 K) := by rw [h]; exact isUnit_one.neg
    exact (IsUnit.mul_iff.mp h').1
  have hPunit : IsUnit P := by
    have h : IsUnit ((Pᵀ * formJ 2 K) * P) := by rw [hPJ]; exact hJunit
    exact (IsUnit.mul_iff.mp h).2
  let Pgl : GL (Fin 2 ⊕ Fin 2) K := hPunit.unit
  have hPgl : (Pgl : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = P := hPunit.unit_spec
  have hPmem : Pgl ∈ StatedSp 2 K :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mpr
      (by rw [hPgl]; exact hPJ)
  let P₀ : gsp 2 K :=
    ⟨Pgl, CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.statedSp_le_gsp hPmem⟩
  have hNv : N *ᵥ v = 0 := by rw [hN, frameN_mulVec]; simp [hvv, hvu]
  have hNu : N *ᵥ u = 0 := by rw [hN, frameN_mulVec]; simp [huv, huu]
  have hNw : N *ᵥ w = -(d • v) := by rw [hN, frameN_mulVec]; simp [hwv, hwu]
  have hNz : N *ᵥ z = u := by rw [hN, frameN_mulVec]; simp [hzv, hzu]
  have h1Nv : (1 + N) *ᵥ v = v := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec, hNv, add_zero]
  have h1Nu : (1 + N) *ᵥ u = u := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec, hNu, add_zero]
  have h1Nw : (1 + N) *ᵥ w = w - d • v := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec, hNw, sub_eq_add_neg]
  have h1Nz : (1 + N) *ᵥ z = z + u := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec, hNz]
  have hPc0 : P.col (Sum.inl 0) = v := by rw [hP, frameMat_col_zero]
  have hPc1 : P.col (Sum.inl 1) = u := by rw [hP, frameMat_col_one]
  have hPc2 : P.col (Sum.inr 0) = w := by rw [hP, frameMat_col_two]
  have hPc3 : P.col (Sum.inr 1) = z := by rw [hP, frameMat_col_three]
  have hP0 : P *ᵥ (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K) = v := by
    rw [Matrix.mulVec_single_one, hPc0]
  have hP1 : P *ᵥ (Pi.single (Sum.inl 1) (1 : K) : Fin 2 ⊕ Fin 2 → K) = u := by
    rw [Matrix.mulVec_single_one, hPc1]
  have hP2 : P *ᵥ (Pi.single (Sum.inr 0) (1 : K) : Fin 2 ⊕ Fin 2 → K) = w := by
    rw [Matrix.mulVec_single_one, hPc2]
  have hP3 : P *ᵥ (Pi.single (Sum.inr 1) (1 : K) : Fin 2 ⊕ Fin 2 → K) = z := by
    rw [Matrix.mulVec_single_one, hPc3]
  have hTc0 : (fromBlocks 1 (skewS d) 0 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).col
      (Sum.inl 0) = (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K) := by
    funext i
    rcases i with a | a <;> fin_cases a <;>
      simp [Matrix.col, Matrix.fromBlocks]
  have hTc1 : (fromBlocks 1 (skewS d) 0 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).col
      (Sum.inl 1) = (Pi.single (Sum.inl 1) (1 : K) : Fin 2 ⊕ Fin 2 → K) := by
    funext i
    rcases i with a | a <;> fin_cases a <;>
      simp [Matrix.col, Matrix.fromBlocks]
  have hTc2 : (fromBlocks 1 (skewS d) 0 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).col
      (Sum.inr 0) = -(d • (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K)) +
        (Pi.single (Sum.inr 0) (1 : K) : Fin 2 ⊕ Fin 2 → K) := by
    funext i
    rcases i with a | a <;> fin_cases a <;>
      simp [Matrix.col, Matrix.fromBlocks, skewS]
  have hTc3 : (fromBlocks 1 (skewS d) 0 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).col
      (Sum.inr 1) = (Pi.single (Sum.inl 1) (1 : K) : Fin 2 ⊕ Fin 2 → K) +
        (Pi.single (Sum.inr 1) (1 : K) : Fin 2 ⊕ Fin 2 → K) := by
    funext i
    rcases i with a | a <;> fin_cases a <;>
      simp [Matrix.col, Matrix.fromBlocks, skewS]
  have hT0 : (fromBlocks 1 (skewS d) 0 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K) =
      (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K) :=
    (Matrix.mulVec_single_one _ (Sum.inl 0)).trans hTc0
  have hT1 : (fromBlocks 1 (skewS d) 0 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      (Pi.single (Sum.inl 1) (1 : K) : Fin 2 ⊕ Fin 2 → K) =
      (Pi.single (Sum.inl 1) (1 : K) : Fin 2 ⊕ Fin 2 → K) :=
    (Matrix.mulVec_single_one _ (Sum.inl 1)).trans hTc1
  have hT2 : (fromBlocks 1 (skewS d) 0 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      (Pi.single (Sum.inr 0) (1 : K) : Fin 2 ⊕ Fin 2 → K) =
      -(d • (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K)) +
        (Pi.single (Sum.inr 0) (1 : K) : Fin 2 ⊕ Fin 2 → K) :=
    (Matrix.mulVec_single_one _ (Sum.inr 0)).trans hTc2
  have hT3 : (fromBlocks 1 (skewS d) 0 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      (Pi.single (Sum.inr 1) (1 : K) : Fin 2 ⊕ Fin 2 → K) =
      (Pi.single (Sum.inl 1) (1 : K) : Fin 2 ⊕ Fin 2 → K) +
        (Pi.single (Sum.inr 1) (1 : K) : Fin 2 ⊕ Fin 2 → K) :=
    (Matrix.mulVec_single_one _ (Sum.inr 1)).trans hTc3
  have hEq0 : (1 + N) *ᵥ (P *ᵥ (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K)) =
      P *ᵥ ((fromBlocks 1 (skewS d) 0 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        (Pi.single (Sum.inl 0) (1 : K) : Fin 2 ⊕ Fin 2 → K)) := by
    rw [hP0, hT0, h1Nv, hP0]
  have hEq1 : (1 + N) *ᵥ (P *ᵥ (Pi.single (Sum.inl 1) (1 : K) : Fin 2 ⊕ Fin 2 → K)) =
      P *ᵥ ((fromBlocks 1 (skewS d) 0 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        (Pi.single (Sum.inl 1) (1 : K) : Fin 2 ⊕ Fin 2 → K)) := by
    rw [hP1, hT1, h1Nu, hP1]
  have hEq2 : (1 + N) *ᵥ (P *ᵥ (Pi.single (Sum.inr 0) (1 : K) : Fin 2 ⊕ Fin 2 → K)) =
      P *ᵥ ((fromBlocks 1 (skewS d) 0 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        (Pi.single (Sum.inr 0) (1 : K) : Fin 2 ⊕ Fin 2 → K)) := by
    rw [hP2, hT2, h1Nw, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_smul, hP0, hP2]
    abel
  have hEq3 : (1 + N) *ᵥ (P *ᵥ (Pi.single (Sum.inr 1) (1 : K) : Fin 2 ⊕ Fin 2 → K)) =
      P *ᵥ ((fromBlocks 1 (skewS d) 0 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        (Pi.single (Sum.inr 1) (1 : K) : Fin 2 ⊕ Fin 2 → K)) := by
    rw [hP3, hT3, h1Nz, Matrix.mulVec_add, hP1, hP3]
    abel
  have hPtau : (1 + N) * P = P * fromBlocks 1 (skewS d) 0 1 := by
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rcases j with a | a
    · fin_cases a
      · exact hEq0
      · exact hEq1
    · fin_cases a
      · exact hEq2
      · exact hEq3
  have hPinv : (Pgl : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((Pgl⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
    simp
  have hPinv' : ((Pgl⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (Pgl : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
    simp
  have hPtau' : (1 + N) * (Pgl : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      (Pgl : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * fromBlocks 1 (skewS d) 0 1 := by
    rw [hPgl]
    exact hPtau
  have hconjP : ((Pgl⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (1 + N) * (Pgl : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks 1 (skewS d) 0 1 := by
    calc ((Pgl⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
          (1 + N) * (Pgl : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
        = ((Pgl⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
            ((1 + N) * (Pgl : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
          rw [Matrix.mul_assoc]
      _ = ((Pgl⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
            ((Pgl : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
              fromBlocks 1 (skewS d) 0 1) := by rw [hPtau']
      _ = (((Pgl⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
            (Pgl : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) *
            fromBlocks 1 (skewS d) 0 1 := by rw [Matrix.mul_assoc]
      _ = 1 * fromBlocks 1 (skewS d) 0 1 := by rw [hPinv']
      _ = fromBlocks 1 (skewS d) 0 1 := Matrix.one_mul _
  have hUgl : ((unipSp N hsN hNN : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) =
      Pgl * (tau (skewS_transpose d) : GL (Fin 2 ⊕ Fin 2) K) * Pgl⁻¹ := by
    apply Units.ext
    rw [coe_unipSp, Units.val_mul, Units.val_mul, coe_tau]
    calc (1 + N)
        = ((Pgl : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
            ((Pgl⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) *
            (1 + N) * ((Pgl : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
            ((Pgl⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
          rw [hPinv, one_mul, mul_one]
      _ = (Pgl : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
            (((Pgl⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
              (1 + N) * (Pgl : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) *
            ((Pgl⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
          simp only [Matrix.mul_assoc]
      _ = (Pgl : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * fromBlocks 1 (skewS d) 0 1 *
            ((Pgl⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
          rw [hconjP]
  have hUD : (unipSp N hsN hNN : StatedSp 2 K) = conjSp 2 K P₀ (tau (skewS_transpose d)) := by
    apply Subtype.ext
    rw [coe_conjSp]
    exact hUgl
  have hS₀ : (skewS d)ᵀ = skewS d := skewS_transpose d
  have hgood : IsOrbitGood p (proj 2 K (tau hS₀)) :=
    isOrbitGood_tau hp hp2 hK h3 hS₀ (skewS_aniso hdsq)
  have hmemOrb : IsOrbitGood p (conjAut 2 K P₀ (proj 2 K (tau hS₀))) :=
    IsOrbitGood.map (p := p) (f := (conjAut 2 K P₀).toMonoidHom)
      (MulEquiv.injective (conjAut 2 K P₀)) hgood
  have hx_eq : proj 2 K (unipSp N hsN hNN) = conjAut 2 K P₀ (proj 2 K (tau hS₀)) := by
    rw [conjAut_proj, ← hUD]
  have horbit : IsOrbitGood p (proj 2 K (unipSp N hsN hNN)) := by
    rw [hx_eq]
    exact hmemOrb
  have hp0 : (p : K) = 0 := (CharP.cast_eq_zero_iff K p p).mpr (dvd_refl p)
  have hSpow : p • (skewS d) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (R := K) p (skewS d), hp0, zero_smul]
  have htaupow : (tau hS₀ : StatedSp 2 K) ^ p = 1 := by
    rw [tau_pow hS₀ p]
    exact (tau_congr _ _ hSpow).trans tau_zero
  have hxpow : (proj 2 K (tau hS₀)) ^ p = 1 := by
    rw [← map_pow, htaupow, map_one]
  have hxne : proj 2 K (tau hS₀) ≠ 1 := by
    intro h
    have hmem : tau hS₀ ∈ (proj 2 K).ker := MonoidHom.mem_ker.mpr h
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj] at hmem
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hentry := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) K =>
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl 0) (Sum.inr 0)) hc
    simp [Matrix.GeneralLinearGroup.coe_scalar, coe_tau, skewS,
      Matrix.fromBlocks] at hentry
    exact hd0 hentry
  have horder : orderOf (proj 2 K (tau hS₀)) = p := orderOf_eq_prime hxpow hxne
  have horderx : orderOf (proj 2 K (unipSp N hsN hNN)) = p := by
    rw [hx_eq, MulEquiv.orderOf_eq (conjAut 2 K P₀), horder]
  have hcoe_conjSp_mat : ∀ (A' : gsp 2 K) (g : StatedSp 2 K),
      (((conjSp 2 K A' g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((A' : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((A'⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    intro A' g
    simp only [coe_conjSp, Units.val_mul]
  have hMinv : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
    simp
  have hconjN' : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * N *
      ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -N := by
    rw [← hM]
    exact hconjN
  have hinvSp : conjSp 2 K A (unipSp N hsN hNN) =
      unipSp (-N) (isSp_neg hsN) (neg_mul_self_neg hNN) := by
    apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
    rw [hcoe_conjSp_mat, coe_unipSp, coe_unipSp, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      hMinv, hconjN']
  have hinv : (conjAut 2 K A * fieldAut 2 K 1) (proj 2 K (unipSp N hsN hNN)) =
      (proj 2 K (unipSp N hsN hNN))⁻¹ := by
    rw [map_one, mul_one, conjAut_proj, ← map_inv, unipSp_inv, hinvSp]
  exact ⟨proj 2 K (unipSp N hsN hNN), horderx, hinv, Or.inr horbit⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

module

public import CFSG.Mathlib.LinearAlgebra.Matrix.BlockFrame
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.LinFrame
public import CFSG.HardMathSupport.Lang.Proving.CubeClassField

public section

namespace CFSG.StandardType.FF81.CatQ1

open Matrix

@[expose] def dualRows {n : ℕ} {F : Type*} [Field F] (B : Matrix (Fin n) (Fin n) F)
    (ψ : Fin n → F) : Matrix (Fin 3) (Fin n) F :=
  Matrix.of fun i k => (ψ ᵥ* (B ^ (2 - (i : ℕ)))) k

private theorem cq1_pow_eq_smul {n : ℕ} {F : Type*} [Field F]
    {B : Matrix (Fin n) (Fin n) F} {c : F}
    (hB3 : B ^ 3 = c • (1 : Matrix (Fin n) (Fin n) F)) (k : ℕ) :
    B ^ k = c ^ (k / 3) • B ^ (k % 3) := by
  have hcpow : ∀ m : ℕ, (c • (1 : Matrix (Fin n) (Fin n) F)) ^ m = c ^ m • 1 := by
    intro m
    rw [← Algebra.algebraMap_eq_smul_one (R := F) c, ← map_pow,
      Algebra.algebraMap_eq_smul_one (R := F) (c ^ m)]
  conv_lhs => rw [← Nat.div_add_mod k 3]
  rw [pow_add, pow_mul B 3 (k / 3), hB3, hcpow (k / 3), Matrix.smul_mul, Matrix.one_mul]

private theorem cq1_dotProduct_pow_mulVec {n : ℕ} {F : Type*} [Field F]
    {B : Matrix (Fin n) (Fin n) F} {c : F}
    (hB3 : B ^ 3 = c • (1 : Matrix (Fin n) (Fin n) F)) (ψ u : Fin n → F) (k : ℕ) :
    ψ ⬝ᵥ ((B ^ k) *ᵥ u) = c ^ (k / 3) * (ψ ⬝ᵥ ((B ^ (k % 3)) *ᵥ u)) := by
  rw [cq1_pow_eq_smul hB3 k, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

private theorem cq1_dualRows_orbit_apply {n : ℕ} {F : Type*} [Field F]
    (B : Matrix (Fin n) (Fin n) F) (ψ u : Fin n → F) (i j : Fin 3) :
    (dualRows B ψ * orbitMatrix B u) i j =
      ψ ⬝ᵥ (B ^ ((2 - (i : ℕ)) + (j : ℕ)) *ᵥ u) := by
  show (ψ ᵥ* B ^ (2 - (i : ℕ))) ⬝ᵥ ((B ^ (j : ℕ)) *ᵥ u) =
    ψ ⬝ᵥ (B ^ ((2 - (i : ℕ)) + (j : ℕ)) *ᵥ u)
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← pow_add]

private theorem cq1_dualRows_mul_orbitMatrix_self {n : ℕ} {F : Type*} [Field F]
    {B : Matrix (Fin n) (Fin n) F} {c : F}
    (hB3 : B ^ 3 = c • (1 : Matrix (Fin n) (Fin n) F))
    {ψ u : Fin n → F} (h0 : ψ ⬝ᵥ u = 0) (h1 : ψ ⬝ᵥ (B *ᵥ u) = 0)
    (h2 : ψ ⬝ᵥ ((B ^ 2) *ᵥ u) = 1) : dualRows B ψ * orbitMatrix B u = 1 := by
  ext i j
  rw [cq1_dualRows_orbit_apply, cq1_dotProduct_pow_mulVec hB3]
  fin_cases i <;> fin_cases j <;> simp [h0, h1, h2]

private theorem cq1_dualRows_mul_orbitMatrix_other {n : ℕ} {F : Type*} [Field F]
    {B : Matrix (Fin n) (Fin n) F} {c : F}
    (hB3 : B ^ 3 = c • (1 : Matrix (Fin n) (Fin n) F))
    {ψ u' : Fin n → F} (h : ∀ i : Fin 3, ψ ⬝ᵥ ((B ^ (i : ℕ)) *ᵥ u') = 0) :
    dualRows B ψ * orbitMatrix B u' = 0 := by
  ext i j
  rw [cq1_dualRows_orbit_apply, cq1_dotProduct_pow_mulVec hB3,
    h ⟨(2 - (i : ℕ) + (j : ℕ)) % 3, Nat.mod_lt _ (by norm_num)⟩]
  simp

private theorem cq1_dualRows_mul_row {n : ℕ} {F : Type*} [Field F]
    (B : Matrix (Fin n) (Fin n) F) (ψ : Fin n → F) (i : Fin 3) :
    (dualRows B ψ * B) i = ψ ᵥ* B ^ (3 - (i : ℕ)) := by
  change (ψ ᵥ* B ^ (2 - (i : ℕ))) ᵥ* B = ψ ᵥ* B ^ (3 - (i : ℕ))
  rw [Matrix.vecMul_vecMul, ← pow_succ]
  rw [show (2 - (i : ℕ)) + 1 = 3 - (i : ℕ) from by omega]

private theorem cq1_cc_mul_dualRows_row {n : ℕ} {F : Type*} [Field F]
    {B : Matrix (Fin n) (Fin n) F} {c : F}
    (hB3 : B ^ 3 = c • (1 : Matrix (Fin n) (Fin n) F)) (ψ : Fin n → F) (i : Fin 3) :
    (cubicCompanion c * dualRows B ψ) i = ψ ᵥ* B ^ (3 - (i : ℕ)) := by
  ext k
  fin_cases i <;>
    simp [cubicCompanion, Matrix.mul_apply, Fin.sum_univ_three, dualRows, hB3,
      Matrix.vecMul_smul, Matrix.vecMul_one]

private theorem cq1_dualRows_mul_self {n : ℕ} {F : Type*} [Field F]
    {B : Matrix (Fin n) (Fin n) F} {c : F}
    (hB3 : B ^ 3 = c • (1 : Matrix (Fin n) (Fin n) F)) (ψ : Fin n → F) :
    dualRows B ψ * B = cubicCompanion c * dualRows B ψ := by
  funext i
  rw [cq1_dualRows_mul_row, cq1_cc_mul_dualRows_row hB3]

private theorem cq1_exists_dotProduct_eq {K : Type*} [Field K] {n : ℕ} {ι : Type} [Fintype ι]
    [DecidableEq ι] (v : ι → Fin n → K) (hv : LinearIndependent K v) (t : ι → K) :
    ∃ ψ : Fin n → K, ∀ i, ψ ⬝ᵥ v i = t i := by
  classical
  let M : Matrix ι (Fin n) K := Matrix.of v
  have hrank : M.rank = Fintype.card ι := by
    rw [Matrix.rank_eq_finrank_span_row,
      finrank_span_eq_card (show LinearIndependent K M.row from hv)]
  have hrange : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, hrank]
    simp
  have : t ∈ LinearMap.range M.mulVecLin := by
    rw [hrange]; trivial
  obtain ⟨ψ, hψ⟩ := this
  refine ⟨ψ, fun i => ?_⟩
  have := congrFun hψ i
  simp only [Matrix.mulVecLin_apply] at this
  rw [dotProduct_comm]
  exact this

private theorem cq1_aeval_mulVec_mem {K : Type*} [Field K] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) K) (S : Submodule K (Fin n → K))
    (hS : ∀ x ∈ S, B *ᵥ x ∈ S) (q : Polynomial K) :
    ∀ x ∈ S, (Polynomial.aeval B q) *ᵥ x ∈ S := by
  induction q using Polynomial.induction_on with
  | C a =>
    intro x hx
    rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact S.smul_mem _ hx
  | add p q hp hq =>
    intro x hx
    rw [map_add, Matrix.add_mulVec]
    exact S.add_mem (hp x hx) (hq x hx)
  | monomial m a ih =>
    intro x hx
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, ← Matrix.mulVec_mulVec]
    exact ih _ (hS x hx)

private theorem cq1_exists_poly_inv {K : Type*} [Field K] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) K) {l : K}
    (hB3 : B ^ 3 = l • (1 : Matrix (Fin n) (Fin n) K)) (hl : ∀ x : K, x ^ 3 ≠ l)
    (c : Fin 3 → K) (hc : c ≠ 0) :
    ∃ b : Polynomial K, Polynomial.aeval B b *
      (c 0 • (1 : Matrix (Fin n) (Fin n) K) + c 1 • B + c 2 • B ^ 2) = 1 := by
  classical
  have hirr := CFSG.HardMathSupport.Lang.Proving.irreducible_X_pow_three_sub_C hl
  set g : Polynomial K := Polynomial.C (c 2) * Polynomial.X ^ 2 +
    Polynomial.C (c 1) * Polynomial.X + Polynomial.C (c 0) with hg
  have hcoef : ∀ k, g.coeff k = if k = 0 then c 0 else if k = 1 then c 1 else if k = 2 then c 2
      else 0 := by
    intro k
    simp only [hg, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]
    rcases k with _ | _ | _ | k <;> simp
  have hg0 : g ≠ 0 := by
    intro h0
    apply hc
    ext i
    have := hcoef i
    rw [h0, Polynomial.coeff_zero] at this
    fin_cases i <;> simpa using this.symm
  have hdeg : g.natDegree < 3 := by
    have : g.natDegree ≤ 2 := Polynomial.natDegree_quadratic_le
    omega
  have hndvd : ¬ (Polynomial.X ^ 3 - Polynomial.C l : Polynomial K) ∣ g := fun hd => by
    have := Polynomial.natDegree_le_of_dvd hd hg0
    rw [Polynomial.natDegree_X_pow_sub_C] at this
    omega
  obtain ⟨a, b, hab⟩ := hirr.coprime_iff_not_dvd.mpr hndvd
  have hp0 : Polynomial.aeval B (Polynomial.X ^ 3 - Polynomial.C l : Polynomial K) = 0 := by
    simp [hB3, Algebra.algebraMap_eq_smul_one]
  have hgB : Polynomial.aeval B g =
      c 0 • (1 : Matrix (Fin n) (Fin n) K) + c 1 • B + c 2 • B ^ 2 := by
    simp [hg, Algebra.algebraMap_eq_smul_one]
    abel
  have h1 := congrArg (Polynomial.aeval B) hab
  rw [map_add, map_mul, map_mul, hp0, mul_zero, zero_add, map_one] at h1
  rw [hgB] at h1
  exact ⟨b, h1⟩

private theorem cq1_pow_three_mulVec {K : Type*} [Field K] {n : ℕ}
    {B : Matrix (Fin n) (Fin n) K} {l : K}
    (hB3 : B ^ 3 = l • (1 : Matrix (Fin n) (Fin n) K)) (x : Fin n → K) :
    (B ^ 3) *ᵥ x = l • x := by
  rw [hB3, Matrix.smul_mulVec, Matrix.one_mulVec]

private theorem cq1_cyc_linearIndependent {K : Type*} [Field K] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) K) {l : K}
    (hB3 : B ^ 3 = l • (1 : Matrix (Fin n) (Fin n) K)) (hl : ∀ x : K, x ^ 3 ≠ l)
    {w : Fin n → K} (hw : w ≠ 0) :
    LinearIndependent K ![w, B *ᵥ w, (B ^ 2) *ᵥ w] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push Not at hne
  have hc0 : c ≠ 0 := fun h0 => by obtain ⟨i, hi⟩ := hne; exact hi (by simp [h0])
  obtain ⟨U, hU⟩ := cq1_exists_poly_inv B hB3 hl c hc0
  apply hw
  have h1 : (c 0 • (1 : Matrix (Fin n) (Fin n) K) + c 1 • B + c 2 • B ^ 2) *ᵥ w = 0 := by
    simpa [Fin.sum_univ_three, Matrix.add_mulVec, Matrix.smul_mulVec] using hc
  calc w = ((Polynomial.aeval B U) *
        (c 0 • (1 : Matrix (Fin n) (Fin n) K) + c 1 • B + c 2 • B ^ 2)) *ᵥ w := by
        rw [hU, one_mulVec]
    _ = 0 := by rw [← mulVec_mulVec, h1, mulVec_zero]

private theorem cq1_orbit_span_stable {K : Type*} [Field K] {n : ℕ}
    {B : Matrix (Fin n) (Fin n) K} {l : K}
    (hB3 : B ^ 3 = l • (1 : Matrix (Fin n) (Fin n) K)) (u : Fin n → K) :
    ∀ x ∈ Submodule.span K (Set.range ![u, B *ᵥ u, (B ^ 2) *ᵥ u]),
      B *ᵥ x ∈ Submodule.span K (Set.range ![u, B *ᵥ u, (B ^ 2) *ᵥ u]) := by
  change Submodule.span K (Set.range ![u, B *ᵥ u, (B ^ 2) *ᵥ u]) ≤
    (Submodule.span K (Set.range ![u, B *ᵥ u, (B ^ 2) *ᵥ u])).comap B.mulVecLin
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  change B *ᵥ ![u, B *ᵥ u, (B ^ 2) *ᵥ u] i ∈
    Submodule.span K (Set.range ![u, B *ᵥ u, (B ^ 2) *ᵥ u])
  fin_cases i
  · exact Submodule.subset_span ⟨1, rfl⟩
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val]
    rw [Matrix.mulVec_mulVec, ← pow_two]
    exact Submodule.subset_span ⟨2, rfl⟩
  · simp only [Fin.reduceFinMk, Matrix.cons_val]
    rw [Matrix.mulVec_mulVec, ← pow_succ', cq1_pow_three_mulVec hB3]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)

private theorem cq1_exists_u'_notMem_span {K : Type*} [Field K] {n : ℕ} (hn : 6 ≤ n)
    (B : Matrix (Fin n) (Fin n) K) :
    ∃ u u' : Fin n → K, u ≠ 0 ∧
      u' ∉ Submodule.span K (Set.range ![u, B *ᵥ u, (B ^ 2) *ᵥ u]) := by
  classical
  have hn0 : 0 < n := by omega
  let u : Fin n → K := Pi.single ⟨0, hn0⟩ 1
  have hu : u ≠ 0 := by
    intro h0
    have := congrFun h0 ⟨0, hn0⟩
    simp [u] at this
  let S : Submodule K (Fin n → K) := Submodule.span K (Set.range ![u, B *ᵥ u, (B ^ 2) *ᵥ u])
  obtain ⟨u', hu'⟩ : ∃ u', u' ∉ S := by
    by_contra hall
    push Not at hall
    have htop : S = ⊤ := eq_top_iff.2 fun x _ => hall x
    have h1 : Module.finrank K S ≤ 3 := by
      refine (finrank_range_le_card (R := K) ![u, B *ᵥ u, (B ^ 2) *ᵥ u]).trans ?_
      simp
    rw [htop, finrank_top, Module.finrank_fin_fun] at h1
    omega
  exact ⟨u, u', hu, hu'⟩

private theorem cq1_poly_block_eq_zero {K : Type*} [Field K] {n : ℕ}
    {B : Matrix (Fin n) (Fin n) K} {l : K}
    (hB3 : B ^ 3 = l • (1 : Matrix (Fin n) (Fin n) K)) (hl : ∀ x : K, x ^ 3 ≠ l)
    {u u' : Fin n → K}
    (hu' : u' ∉ Submodule.span K (Set.range ![u, B *ᵥ u, (B ^ 2) *ᵥ u])) (g : Fin 3 → K)
    (hmem : (g 0 • (1 : Matrix (Fin n) (Fin n) K) + g 1 • B + g 2 • B ^ 2) *ᵥ u' ∈
      Submodule.span K (Set.range ![u, B *ᵥ u, (B ^ 2) *ᵥ u])) :
    g = 0 := by
  by_contra hg0
  obtain ⟨b, hb⟩ := cq1_exists_poly_inv B hB3 hl g hg0
  apply hu'
  have h2 := cq1_aeval_mulVec_mem B _ (cq1_orbit_span_stable (B := B) hB3 u) b _ hmem
  rw [Matrix.mulVec_mulVec, hb, Matrix.one_mulVec] at h2
  exact h2

private theorem cq1_six_linearIndependent {K : Type*} [Field K] {n : ℕ}
    {B : Matrix (Fin n) (Fin n) K} {l : K}
    (hB3 : B ^ 3 = l • (1 : Matrix (Fin n) (Fin n) K)) (hl : ∀ x : K, x ^ 3 ≠ l)
    {u u' : Fin n → K} (hu : u ≠ 0)
    (hu' : u' ∉ Submodule.span K (Set.range ![u, B *ᵥ u, (B ^ 2) *ᵥ u])) :
    LinearIndependent K (fun p : Fin 2 × Fin 3 => (B ^ (p.2 : ℕ)) *ᵥ (![u, u'] p.1)) := by
  classical
  let S : Submodule K (Fin n → K) := Submodule.span K (Set.range ![u, B *ᵥ u, (B ^ 2) *ᵥ u])
  have hSu : u ∈ S := Submodule.subset_span ⟨0, rfl⟩
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fintype.sum_prod_type, Fin.sum_univ_two] at hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
    Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, Matrix.one_mulVec, pow_one] at hg
  have hrel : (g (0, 0) • (1 : Matrix (Fin n) (Fin n) K) + g (0, 1) • B + g (0, 2) • B ^ 2) *ᵥ u +
      (g (1, 0) • (1 : Matrix (Fin n) (Fin n) K) + g (1, 1) • B + g (1, 2) • B ^ 2) *ᵥ u' = 0 := by
    simpa [Matrix.add_mulVec, Matrix.smul_mulVec, add_assoc, add_left_comm, add_comm] using hg
  have hmem : (g (1, 0) • (1 : Matrix (Fin n) (Fin n) K) + g (1, 1) • B + g (1, 2) • B ^ 2) *ᵥ u'
      ∈ S := by
    rw [eq_neg_of_add_eq_zero_right hrel]
    apply S.neg_mem
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec]
    refine S.add_mem (S.add_mem (S.smul_mem _ hSu) (S.smul_mem _ ?_)) (S.smul_mem _ ?_)
    · exact Submodule.subset_span ⟨1, rfl⟩
    · exact Submodule.subset_span ⟨2, rfl⟩
  have hc : (fun k : Fin 3 => g (1, k)) = 0 :=
    cq1_poly_block_eq_zero hB3 hl hu' (fun k => g (1, k)) hmem
  have hc' : ∀ k : Fin 3, g (1, k) = 0 := fun k => congrFun hc k
  have hA : ∑ i : Fin 3, g (0, i) • ![u, B *ᵥ u, (B ^ 2) *ᵥ u] i = 0 := by
    rw [hc' 0, hc' 1, hc' 2] at hg
    simpa [Fin.sum_univ_three] using hg
  have hind := cq1_cyc_linearIndependent B hB3 hl hu
  rw [Fintype.linearIndependent_iff] at hind
  have ha := hind (fun k => g (0, k)) hA
  intro ⟨j, k⟩
  fin_cases j
  · exact ha k
  · exact hc' k

private theorem cq1_exists_six_independent {K : Type*} [Field K] {n : ℕ} (hn : 6 ≤ n)
    (B : Matrix (Fin n) (Fin n) K) {l : K} (hB3 : B ^ 3 = l • (1 : Matrix (Fin n) (Fin n) K))
    (hl : ∀ x : K, x ^ 3 ≠ l) :
    ∃ u u' : Fin n → K, LinearIndependent K
      (fun p : Fin 2 × Fin 3 => (B ^ (p.2 : ℕ)) *ᵥ (![u, u'] p.1)) := by
  obtain ⟨u, u', hu, hu'⟩ := cq1_exists_u'_notMem_span hn B
  exact ⟨u, u', cq1_six_linearIndependent hB3 hl hu hu'⟩

theorem exists_blockFrame_of_nonCube {n : ℕ} {F : Type*} [Field F] (hn : 6 ≤ n)
    {B : Matrix (Fin n) (Fin n) F} {c : F} (hB3 : B ^ 3 = c • (1 : Matrix (Fin n) (Fin n) F))
    (hc : ∀ x : F, x ^ 3 ≠ c) :
    ∃ (U₁ U₂ : Matrix (Fin n) (Fin 3) F) (V₁ V₂ : Matrix (Fin 3) (Fin n) F),
      BlockFrame B (cubicCompanion c) U₁ U₂ V₁ V₂ := by
  obtain ⟨u, u', hind⟩ := cq1_exists_six_independent hn B hB3 hc
  let v : Fin 2 × Fin 3 → Fin n → F := fun p => (B ^ (p.2 : ℕ)) *ᵥ (![u, u'] p.1)
  obtain ⟨ψ₁, hψ₁⟩ := cq1_exists_dotProduct_eq v hind (Pi.single ((0 : Fin 2), (2 : Fin 3)) 1)
  obtain ⟨ψ₂, hψ₂⟩ := cq1_exists_dotProduct_eq v hind (Pi.single ((1 : Fin 2), (2 : Fin 3)) 1)
  have hψ₁u : ψ₁ ⬝ᵥ u = 0 := by simpa [v] using hψ₁ ((0 : Fin 2), (0 : Fin 3))
  have hψ₁Bu : ψ₁ ⬝ᵥ (B *ᵥ u) = 0 := by simpa [v] using hψ₁ ((0 : Fin 2), (1 : Fin 3))
  have hψ₁B2u : ψ₁ ⬝ᵥ ((B ^ 2) *ᵥ u) = 1 := by
    simpa [v] using hψ₁ ((0 : Fin 2), (2 : Fin 3))
  have hψ₁u' : ∀ i : Fin 3, ψ₁ ⬝ᵥ ((B ^ (i : ℕ)) *ᵥ u') = 0 := by
    intro i; simpa [v] using hψ₁ ((1 : Fin 2), i)
  have hψ₂u' : ψ₂ ⬝ᵥ u' = 0 := by simpa [v] using hψ₂ ((1 : Fin 2), (0 : Fin 3))
  have hψ₂Bu' : ψ₂ ⬝ᵥ (B *ᵥ u') = 0 := by simpa [v] using hψ₂ ((1 : Fin 2), (1 : Fin 3))
  have hψ₂B2u' : ψ₂ ⬝ᵥ ((B ^ 2) *ᵥ u') = 1 := by
    simpa [v] using hψ₂ ((1 : Fin 2), (2 : Fin 3))
  have hψ₂u : ∀ i : Fin 3, ψ₂ ⬝ᵥ ((B ^ (i : ℕ)) *ᵥ u) = 0 := by
    intro i; simpa [v] using hψ₂ ((0 : Fin 2), i)
  refine ⟨orbitMatrix B u, orbitMatrix B u', dualRows B ψ₁, dualRows B ψ₂, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · exact cq1_dualRows_mul_orbitMatrix_self hB3 hψ₁u hψ₁Bu hψ₁B2u
  · exact cq1_dualRows_mul_orbitMatrix_self hB3 hψ₂u' hψ₂Bu' hψ₂B2u'
  · exact cq1_dualRows_mul_orbitMatrix_other hB3 hψ₁u'
  · exact cq1_dualRows_mul_orbitMatrix_other hB3 hψ₂u
  · exact mul_orbitMatrix hB3 u
  · exact mul_orbitMatrix hB3 u'
  · exact cq1_dualRows_mul_self hB3 ψ₁
  · exact cq1_dualRows_mul_self hB3 ψ₂

theorem exists_isOrthogonalFrame_of_nonCube {n : ℕ} {F : Type*} [Field F] (hn : 6 ≤ n)
    {B : Matrix (Fin n) (Fin n) F} {c : F} (hB3 : B ^ 3 = c • (1 : Matrix (Fin n) (Fin n) F))
    (hc : ∀ x : F, x ^ 3 ≠ c) :
    ∃ P₁ P₂ S : Matrix (Fin n) (Fin n) F, IsOrthogonalFrame B P₁ P₂ S := by
  obtain ⟨U₁, U₂, V₁, V₂, hF⟩ := exists_blockFrame_of_nonCube hn hB3 hc
  exact ⟨_, _, _, hF.isOrthogonalFrame⟩

end CFSG.StandardType.FF81.CatQ1

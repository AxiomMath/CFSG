module

public import CFSG.RepresentationTheory.SL2NatSum.TorusPoly

public section

namespace CFSG.RepresentationTheory.SL2NatSum

open Polynomial CFSG.LocalAnalysis.UniquenessCase.UCK.Higman
open scoped Matrix MatrixGroups

variable {K : Type} [Field K] [CharP K 2]

private lemma eval₂_torusPoly {n : ℕ} (p₀ : (ZMod 2)[X]) {a b : ℕ → K}
    (hp : p₀.map (ZMod.castHom (dvd_refl 2) K) =
      ∏ i ∈ Finset.range n, (X - C (a i)) * (X - C (b i)))
    {j : ℕ} (hj : j < n) :
    p₀.eval₂ (ZMod.castHom (dvd_refl 2) K) (a j) = 0 ∧
      p₀.eval₂ (ZMod.castHom (dvd_refl 2) K) (b j) = 0 := by
  have hleft := congrArg (Polynomial.eval (a j)) hp
  have hright := congrArg (Polynomial.eval (b j)) hp
  rw [Polynomial.eval_map, Polynomial.eval_prod] at hleft hright
  constructor
  · rw [hleft]
    refine Finset.prod_eq_zero (Finset.mem_range.mpr hj) ?_
    simp
  · rw [hright]
    refine Finset.prod_eq_zero (Finset.mem_range.mpr hj) ?_
    simp

private lemma map_aeval_mapMatrix {m : ℕ}
    (M : Matrix (Fin m) (Fin m) (ZMod 2)) (p : (ZMod 2)[X]) :
    (aeval M p).map (ZMod.castHom (dvd_refl 2) K) =
      aeval (M.map (ZMod.castHom (dvd_refl 2) K))
        (p.map (ZMod.castHom (dvd_refl 2) K)) := by
  letI : Algebra (ZMod 2) K := ZMod.algebra' K 2 (dvd_refl 2)
  let ι : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  have hcomp : (algebraMap K (Matrix (Fin m) (Fin m) K)).comp ι =
      (RingHom.mapMatrix ι).comp
        (algebraMap (ZMod 2) (Matrix (Fin m) (Fin m) (ZMod 2))) := by
    ext a i j
    simp only [RingHom.comp_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.algebraMap_matrix_apply]
    rcases eq_or_ne i j with rfl | hij
    · simp [ι]
    · simp [hij]
  simpa [ι] using
    Polynomial.map_aeval_eq_aeval_map (φ := ι) (ψ := RingHom.mapMatrix ι) hcomp p M

private lemma mul_sum_pow_eq_sum_pow_of_pow_eq_one {R : Type*} [Ring R] {T : R} {N : ℕ}
    (hN : 0 < N) (hT : T ^ N = 1) :
    T * (∑ k ∈ Finset.range N, T ^ k) = ∑ k ∈ Finset.range N, T ^ k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  calc
    T * ∑ k ∈ Finset.range (m + 1), T ^ k
        = ∑ k ∈ Finset.range (m + 1), T * T ^ k := by rw [Finset.mul_sum]
    _ = ∑ k ∈ Finset.range (m + 1), T ^ (k + 1) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← pow_succ']
    _ = (∑ k ∈ Finset.range m, T ^ (k + 1)) + T ^ (m + 1) := by
          rw [Finset.sum_range_succ]
    _ = (∑ k ∈ Finset.range m, T ^ (k + 1)) + 1 := by rw [hT]
    _ = (∑ k ∈ Finset.range m, T ^ (k + 1)) + T ^ 0 := by rw [pow_zero]
    _ = ∑ k ∈ Finset.range (m + 1), T ^ k := by rw [Finset.sum_range_succ']

private lemma aeval_mul_eq_smul_of_mul_eq_smul {R : Type*} [CommRing R] {m : ℕ}
    {A P : Matrix (Fin m) (Fin m) R} {μ : R} (h : A * P = μ • P) (q : R[X]) :
    aeval A q * P = q.eval μ • P := by
  have hpow : ∀ k, A ^ k * P = μ ^ k • P := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, mul_assoc, h, Algebra.mul_smul_comm, ih, smul_smul, ← pow_succ']
  refine Polynomial.induction_on' q ?_ ?_
  · intro p q hp hq
    rw [Polynomial.aeval_add, Polynomial.eval_add, add_mul, add_smul, hp, hq]
  · intro n a
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, mul_assoc, hpow n,
      Algebra.mul_smul_comm, ← Algebra.smul_def, smul_smul, mul_comm]

private lemma aeval_map_pow_eq_zero {m : ℕ} {M : Matrix (Fin m) (Fin m) (ZMod 2)}
    (p₀ : (ZMod 2)[X]) {k₀ : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2, K) V) (g : SL(2, K))
    (c : V ≃ₗ[ZMod 2] (Fin m → ZMod 2))
    (hc : ∀ v : V, c (ρ g v) = M *ᵥ c v)
    (hk : aeval (ρ g) p₀ ^ k₀ = 0) :
    (aeval (M.map (ZMod.castHom (dvd_refl 2) K))
      (p₀.map (ZMod.castHom (dvd_refl 2) K))) ^ k₀ = 0 := by
  let ι : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  let B : Module.End (ZMod 2) (Fin m → ZMod 2) := Matrix.toLinAlgEquiv' M
  have hB : ∀ x : V, c (ρ g x) = B (c x) := by
    intro x
    exact hc x
  have hBpow : aeval B p₀ ^ k₀ = 0 := by
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := c.surjective w
    have h := aeval_comp_apply c.toLinearMap (ρ g) B hB (p₀ ^ k₀) v
    have h' : c (aeval (ρ g) (p₀ ^ k₀) v) = aeval B (p₀ ^ k₀) (c v) := h
    have hzero : aeval B (p₀ ^ k₀) (c v) = 0 := by
      rw [← h']
      simp [map_pow, hk]
    simpa [map_pow] using hzero
  have hMpow : (aeval M p₀) ^ k₀ = 0 := by
    apply (Matrix.toLinAlgEquiv' (R := ZMod 2) (n := Fin m)).injective
    rw [map_pow, ← Polynomial.aeval_algHom_apply
      (Matrix.toLinAlgEquiv' (R := ZMod 2) (n := Fin m)) M p₀, hBpow]
    simp
  have hmap : (aeval M p₀).map ι = aeval (M.map ι) (p₀.map ι) := by
    simpa [ι] using map_aeval_mapMatrix M p₀
  have hzeroMap : ((0 : Matrix (Fin m) (Fin m) (ZMod 2)).map ι) = 0 := by
    ext i j
    simp
  change (aeval (M.map ι) (p₀.map ι)) ^ k₀ = 0
  rw [← hmap, ← Matrix.map_pow, hMpow, hzeroMap]

private lemma map_hMat_pow_eq_one {m : ℕ}
    (Rm : SL(2, K) →* Matrix (Fin m) (Fin m) (ZMod 2)) {N : ℕ} {t : Kˣ}
    (htN : t ^ N = 1) :
    ((Rm (hMat t)).map (ZMod.castHom (dvd_refl 2) K)) ^ N = 1 := by
  let ι : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  have hmat_pow : ∀ k : ℕ, (hMat t) ^ k = hMat (t ^ k) := by
    intro k
    induction k with
    | zero => simp [hMat_one]
    | succ k ih => rw [pow_succ, ih, hMat_mul, pow_succ]
  have hMpow : (Rm (hMat t)) ^ N = 1 := by
    rw [← map_pow, hmat_pow N, htN, hMat_one, map_one]
  have h := map_pow (RingHom.mapMatrix ι) (Rm (hMat t)) N
  rw [hMpow, map_one] at h
  simpa [ι] using h.symm

private lemma torusProj_eigenvector {m : ℕ} {A : Matrix (Fin m) (Fin m) K}
    {N : ℕ} (hNpos : 0 < N) (hA : A ^ N = 1) {μ : K} (hμ : μ ^ N = 1) :
    A * (∑ k ∈ Finset.range N, (μ⁻¹) ^ k • A ^ k) =
      μ • ∑ k ∈ Finset.range N, (μ⁻¹) ^ k • A ^ k := by
  let T : Matrix (Fin m) (Fin m) K := μ⁻¹ • A
  have hμ_ne : μ ≠ 0 := by
    intro h
    rw [h, zero_pow hNpos.ne'] at hμ
    exact zero_ne_one hμ
  have hμinvN : (μ⁻¹) ^ N = 1 := by
    rw [inv_pow, hμ, inv_one]
  have hTpow : T ^ N = 1 := by
    rw [show T = μ⁻¹ • A from rfl, smul_pow, hA, hμinvN, one_smul]
  have hπT : (∑ k ∈ Finset.range N, (μ⁻¹) ^ k • A ^ k) =
      ∑ k ∈ Finset.range N, T ^ k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show T = μ⁻¹ • A from rfl, smul_pow]
  have hTpi : T * (∑ k ∈ Finset.range N, (μ⁻¹) ^ k • A ^ k) =
      ∑ k ∈ Finset.range N, (μ⁻¹) ^ k • A ^ k := by
    rw [hπT]
    exact mul_sum_pow_eq_sum_pow_of_pow_eq_one hNpos hTpow
  have hAeq : A = μ • T := by
    rw [show T = μ⁻¹ • A from rfl, smul_smul, mul_inv_cancel₀ hμ_ne, one_smul]
  nth_rw 1 [hAeq]
  rw [smul_mul_assoc, hTpi]

private lemma eval_torusPoly_ne_zero {n : ℕ} (t : Kˣ)
    (ht : orderOf t = 2 ^ n - 1) (p : K[X])
    (hp : p = ∏ i ∈ Finset.range n,
      (X - C ((t : K) ^ 2 ^ i)) * (X - C (((t : K)⁻¹) ^ 2 ^ i)))
    (e : ℕ)
    (he : ∀ i : ℕ, (e : ZMod (2 ^ n - 1)) ≠ 2 ^ i ∧
      (e : ZMod (2 ^ n - 1)) ≠ -2 ^ i) :
    p.eval ((t : K) ^ e) ≠ 0 := by
  let N : ℕ := 2 ^ n - 1
  have hfac_left : ∀ i < n, (t : K) ^ e - (t : K) ^ 2 ^ i ≠ 0 := by
    intro i hi h
    have hμ_eq : (t : K) ^ e = (t : K) ^ 2 ^ i := sub_eq_zero.mp h
    have hunit : t ^ e = t ^ 2 ^ i := by
      apply Units.ext
      simpa using hμ_eq
    have hmod : e ≡ 2 ^ i [MOD N] := by
      have := (pow_eq_pow_iff_modEq (x := t)).1 hunit
      simpa [N, ht] using this
    have hZ' : (e : ZMod N) = ((2 ^ i : ℕ) : ZMod N) := by
      rw [ZMod.natCast_eq_natCast_iff]
      exact hmod
    have hZ : (e : ZMod N) = (2 : ZMod N) ^ i := by
      simpa [Nat.cast_pow] using hZ'
    exact (he i).1 (by simpa [N] using hZ)
  have hfac_right : ∀ i < n, (t : K) ^ e - ((t : K)⁻¹) ^ 2 ^ i ≠ 0 := by
    intro i hi h
    have hμ_eq : (t : K) ^ e = ((t : K)⁻¹) ^ 2 ^ i := sub_eq_zero.mp h
    have hunit : t ^ e = (t⁻¹) ^ 2 ^ i := by
      apply Units.ext
      simpa [Units.val_inv_eq_inv_val] using hμ_eq
    have hplus : t ^ (e + 2 ^ i) = 1 := by
      rw [pow_add, hunit, inv_pow, inv_mul_cancel]
    have hdvd : N ∣ e + 2 ^ i := by
      rw [show N = orderOf t from ht.symm]
      exact orderOf_dvd_iff_pow_eq_one.mpr hplus
    have hzero : ((e + 2 ^ i : ℕ) : ZMod N) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact hdvd
    have hZ : (e : ZMod N) = -((2 : ZMod N) ^ i) := by
      have h1 : (e : ZMod N) + (2 : ZMod N) ^ i = 0 := by
        simpa [Nat.cast_add, Nat.cast_pow] using hzero
      exact eq_neg_of_add_eq_zero_left h1
    exact (he i).2 (by simpa [N] using hZ)
  rw [hp, Polynomial.eval_prod, Finset.prod_ne_zero_iff]
  intro i hi
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C]
  exact mul_ne_zero (hfac_left i (Finset.mem_range.mp hi))
    (hfac_right i (Finset.mem_range.mp hi))

theorem torusProj_eq_zero {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : Nat.card K = 2 ^ n) (t : Kˣ) (ht : orderOf t = 2 ^ n - 1)
    (d : SL(2, K)) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) SL(2, K) V) (hdV : ∀ v : V, ρ d (ρ d v) + ρ d v + v = 0)
    {m : ℕ} (Rm : SL(2, K) →* Matrix (Fin m) (Fin m) (ZMod 2))
    (c : V ≃ₗ[ZMod 2] (Fin m → ZMod 2)) (hc : ∀ (g : SL(2, K)) (v : V), c (ρ g v) = Rm g *ᵥ c v)
    (e : ℕ) (he : ∀ i : ℕ, (e : ZMod (2 ^ n - 1)) ≠ 2 ^ i ∧ (e : ZMod (2 ^ n - 1)) ≠ -2 ^ i) :
    ∑ k ∈ Finset.range (2 ^ n - 1), (((t : K) ^ e)⁻¹) ^ k •
      ((Rm (hMat t)).map (ZMod.castHom (dvd_refl 2) K)) ^ k = 0 := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  let ι : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  let N : ℕ := 2 ^ n - 1
  let M : Matrix (Fin m) (Fin m) (ZMod 2) := Rm (hMat t)
  let A : Matrix (Fin m) (Fin m) K := M.map ι
  let μ : K := (t : K) ^ e
  let π : Matrix (Fin m) (Fin m) K :=
    ∑ k ∈ Finset.range N, (μ⁻¹) ^ k • A ^ k
  change π = 0
  have hcard : Fintype.card K = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact hn
  obtain ⟨p₀, hp₀⟩ := exists_torusPoly hcard (t : K)
  let p : K[X] := p₀.map ι
  have hp₀_eval : ∀ i < n,
      p₀.eval₂ ι ((t : K) ^ 2 ^ i) = 0 ∧
        p₀.eval₂ ι (((t : K)⁻¹) ^ 2 ^ i) = 0 := by
    intro i hi
    exact eval₂_torusPoly p₀ hp₀ hi
  obtain ⟨k₀, hk₀⟩ := exists_pow_aeval_eq_zero hn t p₀ hp₀_eval d hd3 hd1 ρ hdV
  have hApow : (aeval A p) ^ k₀ = 0 :=
    aeval_map_pow_eq_zero p₀ ρ (hMat t) c (fun v => hc (hMat t) v) hk₀
  have hNpos : 0 < N := by
    rw [show N = orderOf t from ht.symm]
    exact (isOfFinOrder_of_finite t).orderOf_pos
  have htN : t ^ N = 1 := by
    rw [show N = orderOf t from ht.symm]
    exact pow_orderOf_eq_one t
  have htN_K : (t : K) ^ N = 1 := by
    simpa using congrArg (fun u : Kˣ => (u : K)) htN
  have hApow' : A ^ N = 1 := map_hMat_pow_eq_one Rm htN
  have hμN : μ ^ N = 1 := by
    show ((t : K) ^ e) ^ N = 1
    rw [← pow_mul, mul_comm e N, pow_mul, htN_K, one_pow]
  have hAπ : A * π = μ • π := by
    simpa [π] using torusProj_eigenvector (A := A) (μ := μ) hNpos hApow' hμN
  have hpk : (aeval A p) ^ k₀ * π = (p.eval μ) ^ k₀ • π := by
    simpa [map_pow, Polynomial.eval_pow] using
      aeval_mul_eq_smul_of_mul_eq_smul hAπ (p ^ k₀)
  have hpeval_ne : p.eval μ ≠ 0 := eval_torusPoly_ne_zero t ht p hp₀ e he
  have hzero : (p.eval μ) ^ k₀ • π = 0 := by
    rw [← hpk, hApow, zero_mul]
  exact (smul_eq_zero.mp hzero).resolve_left (pow_ne_zero k₀ hpeval_ne)

end CFSG.RepresentationTheory.SL2NatSum

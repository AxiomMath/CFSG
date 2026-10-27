module

public import CFSG.RankThree.GF2n.Smith81.OrthModel
public import CFSG.RankThree.GF2n.Smith81.Orth213LemmaQOdd

public section

namespace CFSG.RankThree.GF2n.Smith81.Orth213.LemmaQ

open CFSG.RankThree.GF2n.Smith81
open scoped Matrix

section Basics

variable {K : Type} [Field K] [CharP K 2] {ι : Type}

@[expose] def pureT (c : Fin 2 → K) (u : ι → K) : (ι → K) × (ι → K) := (c 0 • u, c 1 • u)

theorem orthTensor_id_pureT (g : Matrix (Fin 2) (Fin 2) K) (c : Fin 2 → K) (u : ι → K) :
    orthTensor g id (pureT c u) = pureT (g *ᵥ c) u := by
  simp only [orthTensor, pureT, id_eq, Matrix.mulVec, dotProduct, Fin.sum_univ_two, add_smul,
    smul_smul]

theorem exists_mulVec_ne_zero {N : Matrix (Fin 2) (Fin 2) K} (hN : N ≠ 0) :
    ∃ e : Fin 2 → K, N *ᵥ e ≠ 0 := by
  by_contra h
  push Not at h
  apply hN
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  fin_cases i <;> fin_cases j <;>
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply] using this

theorem pairTypeA_pureT {qU : QuadraticForm K (ι → K)} {c : Fin 2 → K} {u : ι → K} (hc : c ≠ 0)
    (hu : u ≠ 0) (hq : qU u = 0) : PairTypeA qU (pureT c u) := by
  refine ⟨c 0, c 1, u, ?_, hu, hq, rfl⟩
  by_contra h
  push Not at h
  apply hc
  funext i
  fin_cases i
  · exact h.1
  · exact h.2

theorem mem_range_sub_one_iff {V : Type*} [AddCommGroup V] [Module K V] (X : V ≃ₗ[K] V)
    (v : V) : v ∈ LinearMap.range ((X : V →ₗ[K] V) - 1) ↔ ∃ w, X w - w = v := by
  simp [LinearMap.mem_range]

theorem orthTensor_id_comp (g g' : Matrix (Fin 2) (Fin 2) K) (p : (ι → K) × (ι → K)) :
    orthTensor g id (orthTensor g' id p) = orthTensor (g * g') id p := by
  simp only [orthTensor, id_eq, Matrix.mul_apply, Fin.sum_univ_two, smul_add, smul_smul,
    add_smul, Prod.mk.injEq]
  constructor <;> module

theorem orthTensor_add_left (g g' : Matrix (Fin 2) (Fin 2) K) (o : (ι → K) → (ι → K))
    (p : (ι → K) × (ι → K)) :
    orthTensor (g + g') o p = orthTensor g o p + orthTensor g' o p := by
  simp only [orthTensor, Matrix.add_apply, Prod.mk_add_mk, add_smul]
  congr 1 <;> abel

theorem orthTensor_smul_left (c : K) (g : Matrix (Fin 2) (Fin 2) K) (o : (ι → K) → (ι → K))
    (p : (ι → K) × (ι → K)) : orthTensor (c • g) o p = c • orthTensor g o p := by
  simp only [orthTensor, Matrix.smul_apply, smul_eq_mul, Prod.smul_mk, mul_smul, smul_add]

theorem orthTensor_zero_left (o : (ι → K) → (ι → K)) (p : (ι → K) × (ι → K)) :
    orthTensor (0 : Matrix (Fin 2) (Fin 2) K) o p = 0 := by
  simp [orthTensor]

theorem orthTensor_one_id' (p : (ι → K) × (ι → K)) :
    orthTensor (1 : Matrix (Fin 2) (Fin 2) K) id p = p := by
  simp [orthTensor, Matrix.one_apply]

theorem orthTensor_one_apply' (o : (ι → K) → (ι → K)) (p : (ι → K) × (ι → K)) :
    orthTensor (1 : Matrix (Fin 2) (Fin 2) K) o p = (o p.1, o p.2) := by
  simp [orthTensor, Matrix.one_apply]

theorem orthTensor_one_add (N : Matrix (Fin 2) (Fin 2) K) (p : (ι → K) × (ι → K)) :
    orthTensor (1 + N) id p = p + orthTensor N id p := by
  rw [orthTensor_add_left, orthTensor_one_id']

theorem sqZero_sq {N : Matrix (Fin 2) (Fin 2) K} (h : N * N = 0) :
    N 0 0 * N 0 0 = N 0 1 * N 1 0 := by
  have h00 := congrFun (congrFun h 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply] at h00
  linear_combination h00 - N 0 1 * N 1 0 * (CharTwo.two_eq_zero : (2 : K) = 0)

theorem sqZero_diag {N : Matrix (Fin 2) (Fin 2) K} (h : N * N = 0) : N 1 1 = N 0 0 := by
  have h00 := congrFun (congrFun h 0) 0
  have h11 := congrFun (congrFun h 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply] at h00 h11
  have hsq : N 1 1 ^ 2 = N 0 0 ^ 2 := by linear_combination h11 - h00
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h' | h'
  · exact h'
  · rwa [CharTwo.neg_eq] at h'

@[expose] def anticommScalar (N N' : Matrix (Fin 2) (Fin 2) K) : K :=
  N 0 1 * N' 1 0 + N 1 0 * N' 0 1

theorem anticomm_eq {N N' : Matrix (Fin 2) (Fin 2) K} (hN : N * N = 0) (hN' : N' * N' = 0) :
    (1 + N) * (1 + N') + (1 + N') * (1 + N) =
      anticommScalar N N' • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have hd := sqZero_diag hN
  have hd' := sqZero_diag hN'
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  unfold anticommScalar
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, hd, hd', add_mul, mul_add]
  · linear_combination (1 + N 0 0 + N' 0 0 + N 0 0 * N' 0 0) * h2
  · linear_combination (N 0 1 + N' 0 1 + N 0 0 * N' 0 1 + N 0 1 * N' 0 0) * h2
  · linear_combination (N 1 0 + N' 1 0 + N 1 0 * N' 0 0 + N 0 0 * N' 1 0) * h2
  · linear_combination (1 + N 0 0 + N' 0 0 + N 0 0 * N' 0 0) * h2

theorem anticommScalar_ne_zero {N N' : Matrix (Fin 2) (Fin 2) K} (hN : N * N = 0)
    (hN' : N' * N' = 0) (hM : N' * N ≠ 0) : anticommScalar N N' ≠ 0 := by
  intro ht
  apply hM
  have hd := sqZero_diag hN
  have hd' := sqZero_diag hN'
  have ha := sqZero_sq hN
  have ha' := sqZero_sq hN'
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  unfold anticommScalar at ht
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two, hd, hd',
    Matrix.zero_apply, Fin.zero_eta, Fin.mk_one] <;> rw [← pow_eq_zero_iff two_ne_zero]
  · linear_combination (N' 0 0) ^ 2 * ha + N 0 1 * N 1 0 * ha' + N' 0 1 * N 1 0 * ht +
      N' 0 0 * N 0 0 * N' 0 1 * N 1 0 * h2
  · linear_combination (N 0 1) ^ 2 * ha' + (N' 0 1) ^ 2 * ha + N 0 1 * N' 0 1 * ht +
      N' 0 0 * N 0 1 * N' 0 1 * N 0 0 * h2
  · linear_combination (N' 1 0) ^ 2 * ha + (N 1 0) ^ 2 * ha' + N 1 0 * N' 1 0 * ht +
      N' 1 0 * N 0 0 * N' 0 0 * N 1 0 * h2
  · linear_combination (N' 0 0) ^ 2 * ha + N 0 1 * N 1 0 * ha' + N 0 1 * N' 1 0 * ht +
      N' 1 0 * N 0 1 * N' 0 0 * N 0 0 * h2

theorem inter_aux {N N' : Matrix (Fin 2) (Fin 2) K} (hN : N * N = 0) (hN' : N' * N' = 0)
    (hM : N' * N ≠ 0) (r : (ι → K) × (ι → K)) (h1 : orthTensor N id r = 0)
    (h2 : orthTensor N' id r = 0) : r = 0 := by
  have hd := sqZero_diag hN
  have hd' := sqZero_diag hN'
  simp only [orthTensor, id_eq, Prod.mk_eq_zero, hd, hd'] at h1 h2
  obtain ⟨e1, e2⟩ := h1
  obtain ⟨e3, e4⟩ := h2
  have h2r1 : (2 : K) • r.1 = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
  have h2r2 : (2 : K) • r.2 = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
  have m00a : (N' 0 0 * N 0 0 + N' 0 1 * N 1 0) • r.1 = 0 := by
    linear_combination (norm := module) N' 0 1 • e2 + N 0 0 • e3 - (N 0 0 * N' 0 1) • h2r2
  have m00b : (N' 0 0 * N 0 0 + N' 0 1 * N 1 0) • r.2 = 0 := by
    linear_combination (norm := module) N' 0 0 • e2 + N 1 0 • e3 - (N' 0 0 * N 1 0) • h2r1
  have m01a : (N' 0 0 * N 0 1 + N' 0 1 * N 0 0) • r.1 = 0 := by
    linear_combination (norm := module) N' 0 1 • e1 + N 0 1 • e3 - (N 0 1 * N' 0 1) • h2r2
  have m01b : (N' 0 0 * N 0 1 + N' 0 1 * N 0 0) • r.2 = 0 := by
    linear_combination (norm := module) N' 0 0 • e1 + N 0 0 • e3 - (N 0 0 * N' 0 0) • h2r1
  have m10a : (N' 1 0 * N 0 0 + N' 0 0 * N 1 0) • r.1 = 0 := by
    linear_combination (norm := module) N' 0 0 • e2 + N 0 0 • e4 - (N 0 0 * N' 0 0) • h2r2
  have m10b : (N' 1 0 * N 0 0 + N' 0 0 * N 1 0) • r.2 = 0 := by
    linear_combination (norm := module) N 1 0 • e4 + N' 1 0 • e2 - (N 1 0 * N' 1 0) • h2r1
  have m11a : (N' 1 0 * N 0 1 + N' 0 0 * N 0 0) • r.1 = 0 := by
    linear_combination (norm := module) N' 0 0 • e1 + N 0 1 • e4 - (N' 0 0 * N 0 1) • h2r2
  have m11b : (N' 1 0 * N 0 1 + N' 0 0 * N 0 0) • r.2 = 0 := by
    linear_combination (norm := module) N 0 0 • e4 + N' 1 0 • e1 - (N 0 0 * N' 1 0) • h2r1
  by_contra hr
  apply hM
  have hr' : r.1 ≠ 0 ∨ r.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hr (Prod.ext h.1 h.2)
  have key : ∀ m : K, m • r.1 = 0 → m • r.2 = 0 → m = 0 := by
    intro m ha hb
    rcases hr' with h | h
    · exact (smul_eq_zero.mp ha).resolve_right h
    · exact (smul_eq_zero.mp hb).resolve_right h
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two, hd, hd',
    Matrix.zero_apply, Fin.zero_eta, Fin.mk_one]
  · exact key _ m00a m00b
  · exact key _ m01a m01b
  · exact key _ m10a m10b
  · exact key _ m11a m11b

theorem one_add_mul_self (K : Type*) [Field K] [CharP K 2] {A : Type*} [Ring A] [Algebra K A]
    {N : A} (h : N * N = 0) : (1 + N) * (1 + N) = 1 := by
  have h2 : (2 : A) = 0 := two_eq_zero_alg K
  calc (1 + N) * (1 + N) = 1 + 2 * N + N * N := by noncomm_ring
    _ = 1 := by rw [h, h2]; simp

theorem mul_fix_iff {V : Type*} [AddCommGroup V] [Module K V] (X Y : V ≃ₗ[K] V)
    (hX : ∀ v, X (X v) = v) {v : V} (hv : v ∈ LinearMap.range ((X : V →ₗ[K] V) - 1)) :
    (X * Y) v = v ↔ Y v = v := by
  obtain ⟨w, rfl⟩ := (mem_range_sub_one_iff X v).mp hv
  have hXv : X (X w - w) = X w - w := by
    rw [map_sub, hX, ← neg_sub, neg_eq_self_mod K]
  constructor
  · intro h
    have h' : X (Y (X w - w)) = X (X w - w) := by rw [← LinearEquiv.mul_apply, h, hXv]
    exact X.injective h'
  · intro h
    rw [LinearEquiv.mul_apply, h, hXv]

theorem ap_cubic {V : Type*} [AddCommGroup V] [Module K V] (X Y : V ≃ₗ[K] V)
    (hX : ∀ v, X (X v) = v) (hY : ∀ v, Y (Y v) = v) {t : K} {z : V}
    (hz : X (Y z) + Y (X z) = t • z) :
    (X * Y) ((X * Y) z) + t • (X * Y) z + z = 0 := by
  have h1 : (X * Y) (Y (X z)) = z := by simp [hY, hX]
  have h2 : (X * Y) (X (Y z) + Y (X z)) = t • (X * Y) z := by
    rw [hz, map_smul]
  rw [map_add, h1] at h2
  have h3 : (X * Y) ((X * Y) z) = t • (X * Y) z + z := by
    have h4 : (X * Y) ((X * Y) z) + z = t • (X * Y) z := h2
    rw [← h4, add_assoc, add_self_eq_zero_mod K z, add_zero]
  rw [h3]
  have e1 := add_self_eq_zero_mod K (t • (X * Y) z)
  have e2 := add_self_eq_zero_mod K z
  calc t • (X * Y) z + z + t • (X * Y) z + z = (t • (X * Y) z + t • (X * Y) z) + (z + z) := by
        abel
    _ = 0 := by rw [e1, e2, add_zero]

section Cases

variable [Finite K] [Fintype ι] {qU : QuadraticForm K (ι → K)}

theorem EE_left (hsing : ∃ p : ι → K, p ≠ 0 ∧ qU p = 0) {N N' : Matrix (Fin 2) (Fin 2) K}
    (hN0 : N ≠ 0) (hM : N' * N = 0)
    (X Y : ((ι → K) × (ι → K)) ≃ₗ[K] ((ι → K) × (ι → K)))
    (hX : ∀ p, X p = orthTensor (1 + N) id p) (hY : ∀ p, Y p = orthTensor (1 + N') id p) :
    ∃ v, v ∈ LinearMap.range ((X : ((ι → K) × (ι → K)) →ₗ[K] ((ι → K) × (ι → K))) - 1) ∧
      Y v = v ∧ PairTypeA qU v := by
  obtain ⟨p, hp0, hpq⟩ := hsing
  obtain ⟨e, he⟩ := exists_mulVec_ne_zero hN0
  refine ⟨pureT (N *ᵥ e) p, ?_, ?_, pairTypeA_pureT he hp0 hpq⟩
  · rw [mem_range_sub_one_iff]
    refine ⟨pureT e p, ?_⟩
    rw [hX, orthTensor_one_add, orthTensor_id_pureT, add_sub_cancel_left]
  · rw [hY, orthTensor_one_add, orthTensor_id_pureT, Matrix.mulVec_mulVec, hM,
      Matrix.zero_mulVec]
    simp [pureT]

theorem EA_left {N : Matrix (Fin 2) (Fin 2) K} (hN0 : N ≠ 0) {u : ι → K} (hu0 : u ≠ 0)
    (hqu : qU u = 0) (E : (ι → K) ≃ₗ[K] (ι → K)) (hEu : E u = u)
    (X Y : ((ι → K) × (ι → K)) ≃ₗ[K] ((ι → K) × (ι → K)))
    (hX : ∀ p, X p = orthTensor (1 + N) id p) (hY : ∀ p, Y p = (E p.1, E p.2)) :
    ∃ v, v ∈ LinearMap.range ((X : ((ι → K) × (ι → K)) →ₗ[K] ((ι → K) × (ι → K))) - 1) ∧
      Y v = v ∧ PairTypeA qU v := by
  obtain ⟨e, he⟩ := exists_mulVec_ne_zero hN0
  refine ⟨pureT (N *ᵥ e) u, ?_, ?_, pairTypeA_pureT he hu0 hqu⟩
  · rw [mem_range_sub_one_iff]
    refine ⟨pureT e u, ?_⟩
    rw [hX, orthTensor_one_add, orthTensor_id_pureT, add_sub_cancel_left]
  · rw [hY]
    simp [pureT, hEu]

theorem AE_left {N : Matrix (Fin 2) (Fin 2) K} (hNN : N * N = 0) (hN0 : N ≠ 0) {u : ι → K}
    (hu0 : u ≠ 0) (hqu : qU u = 0) (E : (ι → K) ≃ₗ[K] (ι → K)) {s : ι → K} (hs : E s - s = u)
    (X Y : ((ι → K) × (ι → K)) ≃ₗ[K] ((ι → K) × (ι → K)))
    (hX : ∀ p, X p = (E p.1, E p.2)) (hY : ∀ p, Y p = orthTensor (1 + N) id p) :
    ∃ v, v ∈ LinearMap.range ((X : ((ι → K) × (ι → K)) →ₗ[K] ((ι → K) × (ι → K))) - 1) ∧
      Y v = v ∧ PairTypeA qU v := by
  obtain ⟨e, he⟩ := exists_mulVec_ne_zero hN0
  refine ⟨pureT (N *ᵥ e) u, ?_, ?_, pairTypeA_pureT he hu0 hqu⟩
  · rw [mem_range_sub_one_iff]
    refine ⟨pureT (N *ᵥ e) s, ?_⟩
    rw [hX]
    simp only [pureT, map_smul, Prod.mk_sub_mk, ← smul_sub, hs]
  · rw [hY, orthTensor_one_add, orthTensor_id_pureT, Matrix.mulVec_mulVec, hNN,
      Matrix.zero_mulVec]
    simp [pureT]

theorem EE_right {N N' : Matrix (Fin 2) (Fin 2) K} (hN : N * N = 0) (hN' : N' * N' = 0)
    (hM : N' * N ≠ 0) (X Y : ((ι → K) × (ι → K)) ≃ₗ[K] ((ι → K) × (ι → K)))
    (hX : ∀ p, X p = orthTensor (1 + N) id p) (hY : ∀ p, Y p = orthTensor (1 + N') id p) :
    ∃ k : ℕ, Odd k ∧ (X * Y) ^ k = 1 ∧
      ∀ v ∈ LinearMap.range ((X : ((ι → K) × (ι → K)) →ₗ[K] ((ι → K) × (ι → K))) - 1),
        (X * Y) v = v → v = 0 := by
  have hXX : ∀ w, X (X w) = w := by
    intro w
    rw [hX, hX, orthTensor_id_comp, one_add_mul_self K hN, orthTensor_one_id']
  have hYY : ∀ w, Y (Y w) = w := by
    intro w
    rw [hY, hY, orthTensor_id_comp, one_add_mul_self K hN', orthTensor_one_id']
  have ht : anticommScalar N N' ≠ 0 := anticommScalar_ne_zero hN hN' hM
  have hz : ∀ z, X (Y z) + Y (X z) = anticommScalar N N' • z := by
    intro z
    rw [hX, hY, hX, hY, orthTensor_id_comp, orthTensor_id_comp, ← orthTensor_add_left,
      anticomm_eq hN hN', orthTensor_smul_left, orthTensor_one_id']
  obtain ⟨k, hk, hSk⟩ := exists_odd_pow_eq_one_of_cubic K (X * Y) ht
    (fun v => ap_cubic X Y hXX hYY (hz _))
  refine ⟨k, hk, hSk, ?_⟩
  intro v hv hfix
  rw [mul_fix_iff X Y hXX hv] at hfix
  obtain ⟨w, rfl⟩ := (mem_range_sub_one_iff X v).mp hv
  have hw : X w - w = orthTensor N id w := by
    rw [hX, orthTensor_one_add, add_sub_cancel_left]
  rw [hw] at hfix ⊢
  apply inter_aux hN hN' hM
  · rw [orthTensor_id_comp, hN, orthTensor_zero_left]
  · rw [hY, orthTensor_one_add] at hfix
    exact add_eq_left.mp hfix

end Cases

end Basics

end CFSG.RankThree.GF2n.Smith81.Orth213.LemmaQ

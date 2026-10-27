module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.Heis
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Open Subgroup Matrix
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3 (Heis)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  (projectiveSL proj scalars mem_scalars proj_eq_one_iff)

variable {K : Type*} [Field K] {n : ℕ}

private theorem det_one_add_of_isNilpotent {M : Matrix (Fin n) (Fin n) K}
    (hM : IsNilpotent M) : (1 + M).det = 1 := by
  have hR : IsNilpotent (-M) := hM.neg
  have h1 : (-M).charpoly = Polynomial.X ^ Fintype.card (Fin n) :=
    sub_eq_zero.mp (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hR).eq_zero
  have h2 := Matrix.eval_charpoly (-M) 1
  rw [h1, Polynomial.eval_pow, Polynomial.eval_X, one_pow, map_one] at h2
  rw [sub_neg_eq_add] at h2
  exact h2.symm

theorem det_one_add_of_sq_eq_zero {N : Matrix (Fin n) (Fin n) K} (hN : N * N = 0) :
    (1 + N).det = 1 :=
  det_one_add_of_isNilpotent ⟨2, by rw [pow_two]; exact hN⟩

@[expose] def unipSL (N : Matrix (Fin n) (Fin n) K) (hN : N * N = 0) :
    SpecialLinearGroup (Fin n) K :=
  ⟨1 + N, det_one_add_of_sq_eq_zero hN⟩

@[simp] theorem coe_unipSL (N : Matrix (Fin n) (Fin n) K) (hN : N * N = 0) :
    ((unipSL N hN : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + N :=
  rfl

theorem unipSL_inv (N : Matrix (Fin n) (Fin n) K) (hN : N * N = 0) :
    (unipSL N hN)⁻¹ = unipSL (-N) (by rw [neg_mul_neg, hN]) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_unipSL, coe_unipSL,
    Matrix.SpecialLinearGroup.coe_one]
  have h : (1 + N) * (1 + -N) = 1 := by
    simp only [mul_add, mul_neg, mul_one, add_mul, one_mul, hN, add_zero]
    abel
  exact h

private def heisM (N₁ N₂ : Matrix (Fin n) (Fin n) K) (x : Heis K) :
    Matrix (Fin n) (Fin n) K :=
  x.a • N₁ + x.b • N₂ + x.c • (N₁ * N₂)

private def heisMat (N₁ N₂ : Matrix (Fin n) (Fin n) K) (x : Heis K) :
    Matrix (Fin n) (Fin n) K :=
  1 + heisM N₁ N₂ x

private theorem heisM_mul {N₁ N₂ : Matrix (Fin n) (Fin n) K}
    (h1 : N₁ * N₁ = 0) (h2 : N₂ * N₂ = 0) (h21 : N₂ * N₁ = 0) (x y : Heis K) :
    heisM N₁ N₂ x * heisM N₁ N₂ y = (x.a * y.b) • (N₁ * N₂) := by
  have hP1 : (N₁ * N₂) * N₁ = 0 := by rw [Matrix.mul_assoc, h21, Matrix.mul_zero]
  have hP2 : (N₁ * N₂) * N₂ = 0 := by rw [Matrix.mul_assoc, h2, Matrix.mul_zero]
  have h1P : N₁ * (N₁ * N₂) = 0 := by rw [← Matrix.mul_assoc, h1, Matrix.zero_mul]
  have h2P : N₂ * (N₁ * N₂) = 0 := by rw [← Matrix.mul_assoc, h21, Matrix.zero_mul]
  have hPP : (N₁ * N₂) * (N₁ * N₂) = 0 := by
    calc (N₁ * N₂) * (N₁ * N₂) = N₁ * (N₂ * (N₁ * N₂)) := Matrix.mul_assoc _ _ _
      _ = N₁ * ((N₂ * N₁) * N₂) := by rw [Matrix.mul_assoc N₂ N₁ N₂]
      _ = 0 := by rw [h21, Matrix.zero_mul, Matrix.mul_zero]
  simp only [heisM, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, h1, h2, h21, hP1, hP2, h1P, h2P, hPP, smul_zero,
    add_zero, zero_add]
  module

private theorem heisM_cube {N₁ N₂ : Matrix (Fin n) (Fin n) K}
    (h1 : N₁ * N₁ = 0) (h2 : N₂ * N₂ = 0) (h21 : N₂ * N₁ = 0) (x : Heis K) :
    heisM N₁ N₂ x ^ 3 = 0 := by
  have hmul := heisM_mul h1 h2 h21 x x
  have hP1 : (N₁ * N₂) * N₁ = 0 := by rw [Matrix.mul_assoc, h21, Matrix.mul_zero]
  have hP2 : (N₁ * N₂) * N₂ = 0 := by rw [Matrix.mul_assoc, h2, Matrix.mul_zero]
  have hPP : (N₁ * N₂) * (N₁ * N₂) = 0 := by
    calc (N₁ * N₂) * (N₁ * N₂) = N₁ * (N₂ * (N₁ * N₂)) := Matrix.mul_assoc _ _ _
      _ = N₁ * ((N₂ * N₁) * N₂) := by rw [Matrix.mul_assoc N₂ N₁ N₂]
      _ = 0 := by rw [h21, Matrix.zero_mul, Matrix.mul_zero]
  have hPM : (N₁ * N₂) * heisM N₁ N₂ x = 0 := by
    simp only [heisM, Matrix.mul_add, Matrix.mul_smul, hP1, hP2, hPP, smul_zero, add_zero]
  have h3 : heisM N₁ N₂ x ^ 3 = heisM N₁ N₂ x * heisM N₁ N₂ x * heisM N₁ N₂ x := by
    rw [pow_succ, pow_succ, pow_one]
  rw [h3, hmul, Matrix.smul_mul, hPM, smul_zero]

private theorem heisM_add {N₁ N₂ : Matrix (Fin n) (Fin n) K} (x y : Heis K) :
    heisM N₁ N₂ x + heisM N₁ N₂ y + (x.a * y.b) • (N₁ * N₂) = heisM N₁ N₂ (x * y) := by
  simp only [heisM, Heis.mul_a, Heis.mul_b, Heis.mul_c]
  module

private theorem heisMat_mul {N₁ N₂ : Matrix (Fin n) (Fin n) K}
    (h1 : N₁ * N₁ = 0) (h2 : N₂ * N₂ = 0) (h21 : N₂ * N₁ = 0) (x y : Heis K) :
    heisMat N₁ N₂ (x * y) = heisMat N₁ N₂ x * heisMat N₁ N₂ y := by
  rw [heisMat, heisMat, heisMat]
  have hm := heisM_mul h1 h2 h21 x y
  have ha := heisM_add (N₁ := N₁) (N₂ := N₂) x y
  rw [← ha, ← hm]
  noncomm_ring

private theorem heisMat_det {N₁ N₂ : Matrix (Fin n) (Fin n) K}
    (h1 : N₁ * N₁ = 0) (h2 : N₂ * N₂ = 0) (h21 : N₂ * N₁ = 0) (x : Heis K) :
    (heisMat N₁ N₂ x).det = 1 := by
  rw [heisMat]
  exact det_one_add_of_isNilpotent ⟨3, heisM_cube h1 h2 h21 x⟩

private def heisSL (N₁ N₂ : Matrix (Fin n) (Fin n) K)
    (h1 : N₁ * N₁ = 0) (h2 : N₂ * N₂ = 0) (h21 : N₂ * N₁ = 0) (x : Heis K) :
    SpecialLinearGroup (Fin n) K :=
  ⟨heisMat N₁ N₂ x, heisMat_det h1 h2 h21 x⟩

private def heisSLHom (N₁ N₂ : Matrix (Fin n) (Fin n) K)
    (h1 : N₁ * N₁ = 0) (h2 : N₂ * N₂ = 0) (h21 : N₂ * N₁ = 0) :
    Heis K →* SpecialLinearGroup (Fin n) K where
  toFun := heisSL N₁ N₂ h1 h2 h21
  map_one' := by
    apply Subtype.ext
    change heisMat N₁ N₂ 1 = 1
    simp [heisMat, heisM]
  map_mul' x y := by
    apply Subtype.ext
    exact heisMat_mul h1 h2 h21 x y

theorem exists_heisSL (N₁ N₂ : Matrix (Fin n) (Fin n) K) (h1 : N₁ * N₁ = 0)
    (h2 : N₂ * N₂ = 0) (h21 : N₂ * N₁ = 0) :
    ∃ φ : Heis K →* SpecialLinearGroup (Fin n) K,
      (∀ x : Heis K, (φ x : Matrix (Fin n) (Fin n) K) =
        1 + (x.a • N₁ + x.b • N₂ + x.c • (N₁ * N₂))) ∧
      (N₁ * N₂ ≠ 0 → Function.Injective ((proj n K).comp φ)) := by
  let φ := heisSLHom N₁ N₂ h1 h2 h21
  refine ⟨φ, fun x => rfl, fun h12 => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    have hscal : φ x ∈ scalars n K := (proj_eq_one_iff).mp hx
    have hφx : φ x = heisSL N₁ N₂ h1 h2 h21 x := rfl
    rw [hφx, mem_scalars] at hscal
    obtain ⟨d, _hdn, hd⟩ := hscal
    have hdm : heisMat N₁ N₂ x = scalar (Fin n) (d : K) := by
      simpa [heisSL] using hd
    have hn0 : n ≠ 0 := by
      rintro rfl
      apply h12
      ext i
      exact i.elim0
    have hMscalar : heisM N₁ N₂ x = ((d : K) - 1) • 1 := by
      have h' : (1 : Matrix (Fin n) (Fin n) K) + heisM N₁ N₂ x = (d : K) • 1 := by
        rw [← heisMat, hdm, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
      calc heisM N₁ N₂ x = (1 + heisM N₁ N₂ x) - 1 := by abel
        _ = (d : K) • 1 - 1 := by rw [h']
        _ = ((d : K) - 1) • 1 := by rw [sub_smul, one_smul]
    have hcube : heisM N₁ N₂ x ^ 3 = 0 := heisM_cube h1 h2 h21 x
    have hpow : (((d : K) - 1) • (1 : Matrix (Fin n) (Fin n) K)) ^ 3 =
        (((d : K) - 1) ^ 3) • 1 := by
      simp [Matrix.smul_one_eq_diagonal, Matrix.diagonal_pow]
    have hcz : ((d : K) - 1) ^ 3 = 0 := by
      rw [hMscalar, hpow] at hcube
      have := congrFun (congrFun hcube ⟨0, Nat.pos_of_ne_zero hn0⟩)
        ⟨0, Nat.pos_of_ne_zero hn0⟩
      simpa using this
    have hd1 : (d : K) = 1 := by
      exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hcz)
    have hM0 : heisM N₁ N₂ x = 0 := by
      rw [hMscalar, hd1, sub_self, zero_smul]
    have hP2 : (N₁ * N₂) * N₂ = 0 := by rw [Matrix.mul_assoc, h2, Matrix.mul_zero]
    have haP : x.a • (N₁ * N₂) = 0 := by
      have h := congrArg (fun M => M * N₂) hM0
      simpa [heisM, Matrix.add_mul, Matrix.smul_mul, h2, hP2] using h
    have ha0 : x.a = 0 := by
      rcases smul_eq_zero.mp haP with h | h
      · exact h
      · exact absurd h h12
    have h1P : N₁ * (N₁ * N₂) = 0 := by rw [← Matrix.mul_assoc, h1, Matrix.zero_mul]
    have hbP : x.b • (N₁ * N₂) = 0 := by
      have h := congrArg (fun M => N₁ * M) hM0
      simpa [heisM, Matrix.mul_add, Matrix.mul_smul, h1, h1P] using h
    have hb0 : x.b = 0 := by
      rcases smul_eq_zero.mp hbP with h | h
      · exact h
      · exact absurd h h12
    have hcP : x.c • (N₁ * N₂) = 0 := by
      simpa [heisM, ha0, hb0, zero_smul, zero_add] using hM0
    have hc0 : x.c = 0 := by
      rcases smul_eq_zero.mp hcP with h | h
      · exact h
      · exact absurd h h12
    ext <;> simp [ha0, hb0, hc0]

theorem exists_heis_projectiveSL (N₁ N₂ : Matrix (Fin n) (Fin n) K) (h1 : N₁ * N₁ = 0)
    (h2 : N₂ * N₂ = 0) (h21 : N₂ * N₁ = 0) (h12 : N₁ * N₂ ≠ 0) :
    ∃ ι : Heis K →* projectiveSL n K, Function.Injective ι ∧
      ι ⟨1, 0, 0⟩ = proj n K (unipSL N₁ h1) := by
  obtain ⟨φ, hφ, hinj⟩ := exists_heisSL N₁ N₂ h1 h2 h21
  refine ⟨(proj n K).comp φ, hinj h12, ?_⟩
  show proj n K (φ ⟨1, 0, 0⟩) = proj n K (unipSL N₁ h1)
  congr 1
  apply Subtype.ext
  rw [hφ, coe_unipSL]
  simp

theorem exists_heis_partner (hn : 3 ≤ n) {N : Matrix (Fin n) (Fin n) K} (hN : N ≠ 0)
    (hN2 : N * N = 0) :
    ∃ N₂ : Matrix (Fin n) (Fin n) K, N₂ * N₂ = 0 ∧ N₂ * N = 0 ∧ N * N₂ ≠ 0 := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, N i j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hN (by ext i j; exact h i j)
  let u : Fin n → K := Pi.single j 1
  have hu : N *ᵥ u ≠ 0 := by
    intro h
    apply hij
    have := congrFun h i
    simpa [u, Matrix.mulVec_single_one] using this
  have hu0 : u ≠ 0 := by
    intro h
    exact hu (by rw [h, Matrix.mulVec_zero])
  let M : (Fin n → K) →ₗ[K] (Fin n → K) := Matrix.mulVecLin N
  have hrange : LinearMap.range M ≤ LinearMap.ker M := by
    rintro v ⟨w, rfl⟩
    rw [LinearMap.mem_ker]
    calc M (M w) = (N * N) *ᵥ w := by
          rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
      _ = 0 := by rw [hN2, Matrix.zero_mulVec]
  have h2r : 2 * Module.finrank K (LinearMap.range M) ≤ n := by
    have hrn := LinearMap.finrank_range_add_finrank_ker M
    have hle := Submodule.finrank_mono hrange
    have htop : Module.finrank K (Fin n → K) = n := by simp
    omega
  have hr1 : Module.finrank K (LinearMap.range M) + 1 < n := by omega
  have hspan1 : Module.finrank K (Submodule.span K {u}) = 1 := by
    rw [finrank_span_singleton hu0]
  have hfin : Module.finrank K
      ((LinearMap.range M ⊔ Submodule.span K {u} : Submodule K (Fin n → K))) <
      Module.finrank K (Fin n → K) := by
    have hle := Submodule.finrank_add_le_finrank_add_finrank
      (LinearMap.range M) (Submodule.span K {u})
    rw [hspan1] at hle
    have htop : Module.finrank K (Fin n → K) = n := by simp
    omega
  have hlt : LinearMap.range M ⊔ Submodule.span K {u} < ⊤ :=
    Submodule.lt_top_of_finrank_lt_finrank hfin
  obtain ⟨f, hfne, hf⟩ := Submodule.exists_le_ker_of_lt_top
    (LinearMap.range M ⊔ Submodule.span K {u}) hlt
  let ψ : Fin n → K := fun i => f (fun j => if i = j then 1 else 0)
  have hf_dot : ∀ v : Fin n → K, f v = ψ ⬝ᵥ v := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ f v]
    simp [ψ, dotProduct, mul_comm]
  have hψ : ψ ≠ 0 := by
    intro hψ0
    apply hfne
    apply LinearMap.ext
    intro v
    rw [hf_dot v, hψ0]
    simp
  have hku : u ∈ LinearMap.ker f :=
    hf (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton u)))
  have hψu : ψ ⬝ᵥ u = 0 := by
    rw [← hf_dot u, LinearMap.mem_ker.mp hku]
  have hψN : ψ ᵥ* N = 0 := by
    ext k
    rw [Matrix.vecMul_apply, ← Matrix.mulVec_single_one N k, ← hf_dot]
    exact LinearMap.mem_ker.mp (hf (Submodule.mem_sup_left ⟨Pi.single k 1, by
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]⟩))
  have hN₂sq : Matrix.vecMulVec u ψ * Matrix.vecMulVec u ψ = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hψu]
    simp
  have hN₂N : Matrix.vecMulVec u ψ * N = 0 := by
    rw [Matrix.vecMulVec_mul, hψN]
    simp
  have hNN₂ : N * Matrix.vecMulVec u ψ ≠ 0 := by
    rw [Matrix.mul_vecMulVec]
    obtain ⟨i, hi⟩ : ∃ i, (N *ᵥ u) i ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hu (by ext k; exact h k)
    obtain ⟨k, hk⟩ : ∃ k, ψ k ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hψ (by ext k; exact h k)
    intro hzero
    have hentry := congrFun (congrFun hzero i) k
    rw [Matrix.vecMulVec_apply, Matrix.zero_apply] at hentry
    exact mul_ne_zero hi hk hentry
  exact ⟨Matrix.vecMulVec u ψ, hN₂sq, hN₂N, hNN₂⟩

theorem good_unipSL [Finite K] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p]
    (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) (hn : 3 ≤ n) {N : Matrix (Fin n) (Fin n) K}
    (hN : N ≠ 0) (hN2 : N * N = 0) :
    orderOf (proj n K (unipSL N hN2)) = p ∧ IsSpecialGood p (proj n K (unipSL N hN2)) := by
  obtain ⟨N₂, hN₂2, hN₂N, hNN₂⟩ := exists_heis_partner hn hN hN2
  obtain ⟨ι, hι, hι1⟩ := exists_heis_projectiveSL N N₂ hN2 hN₂2 hN₂N hNN₂
  constructor
  · rw [← hι1, orderOf_injective ι hι]
    have : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime (Heis.pow_prime_eq_one hp hp2 ⟨1, 0, 0⟩) (by
      intro h
      have ha : (1 : K) = 0 := by simpa using congrArg Heis.a h
      exact one_ne_zero ha)
  · rw [← hι1]
    exact isSpecialGood_of_heis hp hp2 hK h3 hι ⟨1, 0, 0⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

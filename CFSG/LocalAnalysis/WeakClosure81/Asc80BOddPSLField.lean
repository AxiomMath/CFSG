module

public import CFSG.LieType.SeitzGeneration.LinearOuterLocal
import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSL
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankBoundField
public import CFSG.LieType.SeitzGeneration.QuasiHigh2Linear

public section

namespace CFSG.LocalAnalysis.WeakClosure81.PSLOuter

open Subgroup Matrix CFSG.Open CFSG.GroupTheory CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.QuasiHigh CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private lemma exists_indep_of_not_scalar {K : Type*} [Field K] {n : ℕ}
    {A : Matrix (Fin n) (Fin n) K} (hA : ∀ d : K, A ≠ d • 1) :
    ∃ v : Fin n → K, LinearIndependent K ![v, A *ᵥ v] := by
  by_contra h
  push Not at h
  obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (f := A.mulVecLin) h
  apply hA a
  apply Matrix.ext_of_mulVec_single
  intro i
  have hx := DFunLike.congr_fun ha (Pi.single i 1)
  have hx' : A *ᵥ Pi.single i (1 : K) = a • Pi.single i 1 := by
    simpa [Matrix.mulVecLin_apply, Matrix.smul_mulVec, Matrix.one_mulVec] using hx
  rw [hx']
  ext j
  by_cases h : i = j <;> simp [Matrix.col, Matrix.smul_apply, h]

private lemma pair_span_lt_top {K : Type*} [Field K] {n : ℕ} (hn : 3 ≤ n) (v u : Fin n → K) :
    Submodule.span K ({v, u} : Set (Fin n → K)) < ⊤ := by
  classical
  have h := finrank_span_finset_le_card (R := K) ({v, u} : Finset (Fin n → K))
  have hcard : ({v, u} : Finset (Fin n → K)).card ≤ 2 := by
    simpa using Finset.card_insert_le v ({u} : Finset (Fin n → K))
  have hle : Set.finrank K ({v, u} : Set (Fin n → K)) ≤ 2 := by
    rw [← Finset.coe_pair]
    exact le_trans h hcard
  rw [lt_top_iff_ne_top]
  intro htop
  have h2 : Module.finrank K (⊤ : Submodule K (Fin n → K)) ≤ 2 := htop ▸ hle
  rw [finrank_top K (Fin n → K), Module.finrank_fin_fun] at h2
  omega

private lemma functional_dotProduct {K : Type*} [Field K] {n : ℕ}
    (f : (Fin n → K) →ₗ[K] K) (x ψ : Fin n → K)
    (hψ : ∀ j, ψ j = f (Pi.single j 1)) : f x = ψ ⬝ᵥ x := by
  rw [LinearMap.pi_apply_eq_sum_univ f x]
  simp only [dotProduct, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (fun j => if i = j then (1 : K) else 0) = Pi.single i 1 from by
    funext j
    rw [Pi.single_apply]
    exact if_congr eq_comm rfl rfl]
  rw [← hψ i]
  exact mul_comm _ _

theorem exists_sq_zero_commute_of_sq_scalar {k : Type*} [Field k] {n : ℕ} (hn : 3 ≤ n)
    {A : Matrix (Fin n) (Fin n) k} {μ : k} (hA2 : A * A = μ • 1) (hA : ∀ c : k, A ≠ c • 1) :
    ∃ N : Matrix (Fin n) (Fin n) k, N ≠ 0 ∧ N * N = 0 ∧ A * N = N * A := by
  obtain ⟨v, hLI⟩ := exists_indep_of_not_scalar hA
  let u := A *ᵥ v
  have hAu : A *ᵥ u = μ • v := by
    simp only [u, Matrix.mulVec_mulVec, hA2, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hv0 : v ≠ 0 := by simpa using hLI.ne_zero (0 : Fin 2)
  have hpair : ∀ a : k, a • v ≠ u := (LinearIndependent.pair_iff' hv0).mp hLI
  have hW : Submodule.span k ({v, u} : Set (Fin n → k)) < ⊤ := pair_span_lt_top hn v u
  obtain ⟨f, hf, hker⟩ := Submodule.exists_le_ker_of_lt_top _ hW
  have hfv : f v = 0 := LinearMap.mem_ker.mp (hker (Submodule.subset_span (by simp)))
  have hfu : f u = 0 := LinearMap.mem_ker.mp (hker (Submodule.subset_span (by simp)))
  let ψ : Fin n → k := fun j => f (Pi.single j 1)
  have hψ : ∀ x : Fin n → k, f x = ψ ⬝ᵥ x :=
    fun x => functional_dotProduct f x ψ (fun _ => rfl)
  have hψv : ψ ⬝ᵥ v = 0 := by rw [← hψ v]; exact hfv
  have hψu : ψ ⬝ᵥ u = 0 := by rw [← hψ u]; exact hfu
  let φ : Fin n → k := ψ ᵥ* A
  have hφu : φ ⬝ᵥ u = 0 := by
    simp only [φ]
    rw [← Matrix.dotProduct_mulVec, hAu, dotProduct_smul, hψv, smul_zero]
  have hφv : φ ⬝ᵥ v = 0 := by
    simp only [φ]
    rw [← Matrix.dotProduct_mulVec]
    exact hψu
  have hφA : φ ᵥ* A = μ • ψ := by
    simp only [φ, Matrix.vecMul_vecMul, hA2, Matrix.vecMul_smul, Matrix.vecMul_one]
  let N := vecMulVec v φ + vecMulVec u ψ
  refine ⟨N, ?_, ?_, ?_⟩
  · intro hN
    obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hf
    have hx' : ψ ⬝ᵥ x ≠ 0 := by simpa [hψ x] using hx
    have hNx : N *ᵥ x = (φ ⬝ᵥ x) • v + (ψ ⬝ᵥ x) • u := by
      simp only [N, Matrix.add_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
    have hne : N *ᵥ x ≠ 0 := by
      rw [hNx]
      intro h
      have hu : (ψ ⬝ᵥ x) • u = -((φ ⬝ᵥ x) • v) := by
        rw [add_comm] at h
        exact eq_neg_of_add_eq_zero_left h
      have h2 : u = ((ψ ⬝ᵥ x)⁻¹ * (-(φ ⬝ᵥ x))) • v := by
        have h3 : u = (ψ ⬝ᵥ x)⁻¹ • ((ψ ⬝ᵥ x) • u) := by
          rw [smul_smul, inv_mul_cancel₀ hx', one_smul]
        rw [h3, hu, smul_neg, smul_smul, mul_neg, neg_smul]
      exact hpair _ h2.symm
    rw [hN, Matrix.zero_mulVec] at hne
    exact hne rfl
  · have hNN : N * N = 0 := by
      simp only [N]
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
        Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec,
        Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec,
        hφv, hφu, hψv, hψu]
      simp
    exact hNN
  · have hAN : A * N = vecMulVec u φ + μ • vecMulVec v ψ := by
      simp only [N]
      rw [Matrix.mul_add, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, hAu,
        Matrix.smul_vecMulVec]
    have hNA : N * A = μ • vecMulVec v ψ + vecMulVec u φ := by
      simp only [N]
      rw [Matrix.add_mul, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul, hφA]
      rw [Matrix.vecMulVec_smul]
    rw [hAN, hNA, add_comm]

theorem exists_unipotent_isometry {k : Type*} [Field k] [Finite k] (hk : ringChar k ≠ 2)
    {n : ℕ} (hn : 3 ≤ n) {Φ : Matrix (Fin n) (Fin n) k} (hΦ : IsUnit Φ.det)
    (hsym : Φᵀ = Φ ∨ Φᵀ = -Φ) :
    ∃ X : Matrix (Fin n) (Fin n) k, X ≠ 1 ∧ (X - 1) ^ 3 = 0 ∧ Xᵀ * Φ * X = Φ := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  have hΦu : IsUnit Φ := (Matrix.isUnit_iff_isUnit_det Φ).mpr hΦ
  have hvecinj := Matrix.vecMul_injective_of_isUnit hΦu
  obtain hsym | hsym := hsym
  ·
    let B : LinearMap.BilinForm k (Fin n → k) := Matrix.toBilin' Φ
    have hBapp : ∀ x y, B x y = x ⬝ᵥ (Φ *ᵥ y) := fun x y => Matrix.toBilin'_apply' _ _ _
    have hBsym : ∀ x y, B x y = B y x := by
      intro x y
      calc B x y = x ⬝ᵥ (Φ *ᵥ y) := hBapp x y
        _ = (x ᵥ* Φ) ⬝ᵥ y := Matrix.dotProduct_mulVec x Φ y
        _ = (Φ *ᵥ x) ⬝ᵥ y := by
            have h : x ᵥ* Φ = Φ *ᵥ x := by
              conv_lhs => rw [← hsym]
              exact Matrix.vecMul_transpose Φ x
            rw [h]
        _ = y ⬝ᵥ (Φ *ᵥ x) := dotProduct_comm _ _
        _ = B y x := (hBapp y x).symm
    have hBnd : B.Nondegenerate :=
      Matrix.nondegenerate_toBilin'_iff.mpr
        (Matrix.nondegenerate_of_det_ne_zero hΦ.ne_zero)
    let Q : QuadraticForm k (Fin n → k) := B.toQuadraticMap
    have hQnd : Q.polarBilin.Nondegenerate := by
      refine ⟨fun x hx => ?_, fun y hy => ?_⟩
      · apply hBnd.1
        intro z
        have h := hx z
        rw [LinearMap.BilinMap.polarBilin_toQuadraticMap] at h
        have h' : B x z + B z x = 0 := by
          simpa [LinearMap.add_apply, LinearMap.flip_apply] using h
        rw [hBsym z x] at h'
        have h2xz : (2 : k) * B x z = 0 := by rw [two_mul]; exact h'
        exact (mul_eq_zero.mp h2xz).resolve_left h2
      · apply hBnd.2
        intro z
        have h := hy z
        rw [LinearMap.BilinMap.polarBilin_toQuadraticMap] at h
        have h' : B z y + B y z = 0 := by
          simpa [LinearMap.add_apply, LinearMap.flip_apply] using h
        rw [hBsym y z] at h'
        have h2xz : (2 : k) * B z y = 0 := by rw [two_mul]; exact h'
        exact (mul_eq_zero.mp h2xz).resolve_left h2
    have hodd : Odd (Nat.card k) := by
      rw [Nat.card_eq_fintype_card, Nat.odd_iff]
      exact FiniteField.odd_card_of_char_ne_two hk
    obtain ⟨u, hu0, huQ⟩ :=
      CFSG.ComponentClassification.CatalogueBOddQuadratic.exists_isotropic_of_three_le
        hodd Q hQnd (by simpa using hn)
    have hBuu : B u u = 0 := by
      rw [← LinearMap.BilinMap.toQuadraticMap_apply]
      exact huQ
    have hBu_ne : B u ≠ 0 := by
      intro h
      apply hu0
      have hrow : u ᵥ* Φ = 0 := by
        ext i
        have h1 : B u (Pi.single i 1) = 0 := by rw [h]; rfl
        rw [hBapp, Matrix.dotProduct_mulVec] at h1
        simpa using h1
      exact hvecinj (by show u ᵥ* Φ = 0 ᵥ* Φ; rw [hrow, Matrix.zero_vecMul])
    obtain ⟨z, hz⟩ : ∃ z, B u z ≠ 0 := by
      by_contra h
      push Not at h
      exact hBu_ne (LinearMap.ext h)
    have hspan : Submodule.span k ({u, z} : Set (Fin n → k)) < ⊤ := pair_span_lt_top hn u z
    obtain ⟨y, -, hy⟩ := SetLike.exists_of_lt hspan
    let w : Fin n → k := y - (B u y / B u z) • z
    have hBuw : B u w = 0 := by
      simp only [w, map_sub, map_smul]
      rw [sub_eq_zero, smul_eq_mul]
      field_simp [hz]
    have hw_out : w ∉ Submodule.span k ({u} : Set (Fin n → k)) := by
      intro hw
      apply hy
      have hyw : y = w + (B u y / B u z) • z := by
        simp only [w]
        abel
      rw [hyw]
      have hle : Submodule.span k ({u} : Set (Fin n → k)) ≤
          Submodule.span k ({u, z} : Set (Fin n → k)) :=
        Submodule.span_mono (by intro x hx; rw [Set.mem_singleton_iff] at hx; rw [hx]; simp)
      exact Submodule.add_mem (p := Submodule.span k ({u, z} : Set (Fin n → k)))
        (hle hw)
        (Submodule.smul_mem _ (B u y / B u z)
          (Submodule.subset_span (by simp : z ∈ ({u, z} : Set (Fin n → k)))))
    let c : k := (2 : k)⁻¹ * B w w
    let ψu : Fin n → k := u ᵥ* Φ
    let ψw : Fin n → k := w ᵥ* Φ
    let η : Fin n → k := ψw + c • ψu
    have hΦu : Φ *ᵥ u = ψu := by
      have h := Matrix.vecMul_transpose Φ u
      rw [hsym] at h
      simpa [ψu] using h.symm
    have hΦw : Φ *ᵥ w = ψw := by
      have h := Matrix.vecMul_transpose Φ w
      rw [hsym] at h
      simpa [ψw] using h.symm
    have hψuu : ψu ⬝ᵥ u = 0 := by
      rw [dotProduct_comm]
      have h1 : u ⬝ᵥ ψu = B u u := by rw [hBapp u u, hΦu]
      rw [h1, hBuu]
    have hψuw : ψu ⬝ᵥ w = 0 := by
      calc ψu ⬝ᵥ w = (u ᵥ* Φ) ⬝ᵥ w := rfl
        _ = u ⬝ᵥ (Φ *ᵥ w) := (Matrix.dotProduct_mulVec u Φ w).symm
        _ = u ⬝ᵥ ψw := by rw [hΦw]
        _ = B u w := by rw [hBapp u w, hΦw]
        _ = 0 := hBuw
    have hψwu : ψw ⬝ᵥ u = 0 := by
      calc ψw ⬝ᵥ u = (w ᵥ* Φ) ⬝ᵥ u := rfl
        _ = w ⬝ᵥ (Φ *ᵥ u) := (Matrix.dotProduct_mulVec w Φ u).symm
        _ = w ⬝ᵥ ψu := by rw [hΦu]
        _ = B w u := by rw [hBapp w u, hΦu]
        _ = B u w := hBsym w u
        _ = 0 := hBuw
    have hψww : ψw ⬝ᵥ w = 2 * c := by
      have h : ψw ⬝ᵥ w = B w w := by
        calc ψw ⬝ᵥ w = (w ᵥ* Φ) ⬝ᵥ w := rfl
          _ = w ⬝ᵥ (Φ *ᵥ w) := (Matrix.dotProduct_mulVec w Φ w).symm
          _ = B w w := by rw [hBapp w w]
      rw [h]
      simp only [c]
      field_simp
    have heu : η ⬝ᵥ u = 0 := by
      change (ψw + c • ψu) ⬝ᵥ u = 0
      rw [add_dotProduct, smul_dotProduct, hψwu, hψuu, smul_zero, add_zero]
    have hew : η ⬝ᵥ w = 2 * c := by
      change (ψw + c • ψu) ⬝ᵥ w = 2 * c
      rw [add_dotProduct, smul_dotProduct, hψww, hψuw, smul_zero, add_zero]
    let M : Matrix (Fin n) (Fin n) k := vecMulVec w ψu - vecMulVec u η
    let X : Matrix (Fin n) (Fin n) k := 1 + M
    have hM2 : M * M = -(2 * c) • vecMulVec u ψu := by
      simp only [M]
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
        Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec,
        Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec,
        hψuw, hψuu, hew, heu, Matrix.vecMulVec_smul]
      simp
    have hM3 : M * M * M = 0 := by
      rw [hM2]
      simp only [M]
      rw [neg_smul, neg_mul, Matrix.smul_mul, Matrix.mul_sub,
        Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec]
      simp [hψuw, hψuu]
    have hXsub : X - 1 = M := by
      simp only [X]
      abel
    have hX3 : (X - 1) ^ 3 = 0 := by
      rw [hXsub]
      have h : M ^ 3 = M * M * M := by
        rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]
      rw [h, hM3]
    have hMtr : Mᵀ = vecMulVec ψu w - vecMulVec η u := by
      simp only [M, Matrix.transpose_sub, Matrix.transpose_vecMulVec]
    have hMtrΦ : Mᵀ * Φ = vecMulVec ψu ψw - vecMulVec η ψu := by
      rw [hMtr, Matrix.sub_mul, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul]
    have hΦM : Φ * M = vecMulVec ψw ψu - vecMulVec ψu η := by
      simp only [M]
      rw [Matrix.mul_sub, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, hΦu, hΦw]
    have hMtrΦM : Mᵀ * Φ * M = (2 * c) • vecMulVec ψu ψu := by
      rw [hMtrΦ, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
        Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec,
        Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec,
        hψww, hψwu, hψuw, hψuu, Matrix.vecMulVec_smul]
      simp
    have hiso : Xᵀ * Φ * X = Φ := by
      have hXtr : Xᵀ = 1 + Mᵀ := by
        simp only [X, Matrix.transpose_add, Matrix.transpose_one]
      calc Xᵀ * Φ * X = (1 + Mᵀ) * Φ * (1 + M) := by rw [hXtr]
        _ = (Φ + Mᵀ * Φ) * (1 + M) := by rw [Matrix.add_mul, Matrix.one_mul]
        _ = (Φ + Mᵀ * Φ) + (Φ + Mᵀ * Φ) * M := by rw [Matrix.mul_add, Matrix.mul_one]
        _ = Φ + Mᵀ * Φ + (Φ * M + Mᵀ * Φ * M) := by rw [Matrix.add_mul]
        _ = Φ + (vecMulVec ψu ψw - vecMulVec η ψu) +
              (vecMulVec ψw ψu - vecMulVec ψu η) + (2 * c) • vecMulVec ψu ψu := by
            rw [hMtrΦM, hMtrΦ, hΦM]
            abel
        _ = Φ := by
            have h1 : vecMulVec ψu η = vecMulVec ψu ψw + c • vecMulVec ψu ψu := by
              simp only [η, Matrix.vecMulVec_add, Matrix.vecMulVec_smul]
            have h2 : vecMulVec η ψu = vecMulVec ψw ψu + c • vecMulVec ψu ψu := by
              simp only [η, Matrix.add_vecMulVec, Matrix.smul_vecMulVec]
            rw [h1, h2]
            module
    refine ⟨X, ?_, hX3, hiso⟩
    intro hX1
    have hM0 : M = 0 := by
      have h : X - 1 = 0 := by rw [hX1, sub_self]
      rwa [hXsub] at h
    have hMzero : M *ᵥ z = 0 := by rw [hM0, Matrix.zero_mulVec]
    have hMz : M *ᵥ z = (B u z) • w - (η ⬝ᵥ z) • u := by
      simp only [M, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
      have h1 : ψu ⬝ᵥ z = B u z := by
        calc ψu ⬝ᵥ z = (u ᵥ* Φ) ⬝ᵥ z := rfl
          _ = u ⬝ᵥ (Φ *ᵥ z) := (Matrix.dotProduct_mulVec u Φ z).symm
          _ = B u z := (hBapp u z).symm
      rw [h1]
    rw [hMzero] at hMz
    have hrel : (B u z) • w = (η ⬝ᵥ z) • u := sub_eq_zero.mp hMz.symm
    have hwspan : w ∈ Submodule.span k ({u} : Set (Fin n → k)) := by
      have hw_eq : w = ((B u z)⁻¹ * (η ⬝ᵥ z)) • u := by
        have h := congrArg (fun x => (B u z)⁻¹ • x) hrel
        simpa [smul_smul, inv_mul_cancel₀ hz] using h
      rw [hw_eq]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    exact hw_out hwspan
  ·
    have hanti : ∀ x y : Fin n → k, x ⬝ᵥ (Φ *ᵥ y) = -(y ⬝ᵥ (Φ *ᵥ x)) := by
      intro x y
      have h := Matrix.dotProduct_transpose_mulVec Φ y x
      rw [hsym, Matrix.neg_mulVec, dotProduct_neg] at h
      exact h.symm
    let v : Fin n → k := Pi.single ⟨0, by omega⟩ 1
    have hv0 : v ≠ 0 := by simp [v]
    have hvv : v ⬝ᵥ (Φ *ᵥ v) = 0 := by
      have h := hanti v v
      have hzero : (2 : k) * (v ⬝ᵥ (Φ *ᵥ v)) = 0 := by
        rw [two_mul]
        nth_rewrite 2 [h]
        abel
      exact (mul_eq_zero.mp hzero).resolve_left h2
    let ψ : Fin n → k := v ᵥ* Φ
    have hΦv : Φ *ᵥ v = -ψ := by
      have h := Matrix.vecMul_transpose Φ v
      rw [hsym, Matrix.vecMul_neg] at h
      simpa [ψ] using h.symm
    have hψv : ψ ⬝ᵥ v = 0 := by
      calc ψ ⬝ᵥ v = (v ᵥ* Φ) ⬝ᵥ v := rfl
        _ = v ⬝ᵥ (Φ *ᵥ v) := (Matrix.dotProduct_mulVec v Φ v).symm
        _ = 0 := hvv
    let X := 1 + vecMulVec v ψ
    have hXsub : X - 1 = vecMulVec v ψ := by
      simp only [X]
      rw [add_sub_cancel_left]
    have hψ0 : ψ ≠ 0 := by
      intro h
      apply hv0
      have hrow : v ᵥ* Φ = 0 := by rw [show v ᵥ* Φ = ψ from rfl, h]
      exact hvecinj (by simpa [Matrix.zero_vecMul] using hrow)
    refine ⟨X, ?_, ?_, ?_⟩
    · intro hX1
      have h1 : vecMulVec v ψ = 0 := by
        rw [← hXsub, hX1, sub_self]
      have hψeq : ψ = 0 := by
        ext j
        have hji := congrFun (congrFun h1 ⟨0, by omega⟩) j
        simp only [Matrix.vecMulVec_apply, Matrix.zero_apply] at hji
        exact (mul_eq_zero.mp hji).resolve_left (by simp [v])
      exact hψ0 hψeq
    · have hsq : (X - 1) ^ 2 = 0 := by
        rw [hXsub, pow_two, Matrix.vecMulVec_mul_vecMulVec, hψv, zero_smul,
          Matrix.vecMulVec_zero]
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hsq, Matrix.zero_mul]
    · have hXtr : Xᵀ = 1 + vecMulVec ψ v := by
        simp only [X, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_vecMulVec]
      calc Xᵀ * Φ * X = (1 + vecMulVec ψ v) * Φ * (1 + vecMulVec v ψ) := by rw [hXtr]
        _ = (Φ + vecMulVec ψ v * Φ) * (1 + vecMulVec v ψ) := by
            rw [Matrix.add_mul, Matrix.one_mul]
        _ = (Φ + vecMulVec ψ v * Φ) + (Φ + vecMulVec ψ v * Φ) * vecMulVec v ψ := by
            rw [Matrix.mul_add, Matrix.mul_one]
        _ = Φ + vecMulVec ψ v * Φ + (Φ * vecMulVec v ψ +
              (vecMulVec ψ v * Φ) * vecMulVec v ψ) := by
            rw [Matrix.add_mul]
        _ = Φ := by
            have h3 : vecMulVec ψ v * Φ * vecMulVec v ψ = 0 := by
              rw [show vecMulVec ψ v * Φ = vecMulVec ψ ψ from by rw [Matrix.vecMulVec_mul],
                Matrix.vecMulVec_mul_vecMulVec, hψv, zero_smul, Matrix.vecMulVec_zero]
            rw [h3, Matrix.vecMulVec_mul, Matrix.mul_vecMulVec, hΦv, Matrix.neg_vecMulVec]
            rw [show vecMulVec ψ (v ᵥ* Φ) = vecMulVec ψ ψ from rfl]
            abel

theorem seitzHyperGamma_two_of_planeGen_modelAut {K : Type} [Group K] [Finite K]
    (hZ : Subgroup.center K = ⊥) {P : Type} [Group P] (θ : K ⧸ Subgroup.center K ≃* P)
    {E : Subgroup (MulAut K)} (h4 : Nat.card E = 4)
    (h : PlaneGen (E.map (QuasiHigh2.modelAut θ))) : seitzHyperGamma 2 E = ⊤ := by
  classical
  let ψ : K ≃* P :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans θ
  let e : K ⧸ Subgroup.center K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have he_mk : ∀ y : K, e (QuotientGroup.mk y) = y := by
    intro y
    simp only [e, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
    rw [show QuotientGroup.quotientBot (QuotientGroup.mk y : K ⧸ (⊥ : Subgroup K)) =
      (QuotientGroup.kerLift (MonoidHom.id K)) (QuotientGroup.mk y) from rfl,
      QuotientGroup.kerLift_mk]
    rfl
  have he_symm : ∀ y : K, e.symm y = QuotientGroup.mk y := by
    intro y
    rw [← he_mk y, MulEquiv.symm_apply_apply, he_mk y]
  have hcongr : QuasiHigh2.modelAut θ = (MulAut.congr ψ).toMonoidHom := by
    ext g x
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) (θ.symm x)
    have hx : x = θ ((QuotientGroup.mk' (Subgroup.center K)) k) := by
      conv_lhs => rw [← θ.apply_symm_apply x]
      rw [← hk]
    rw [QuasiHigh2.modelAut_apply, ← hk, QuotientGroup.mk'_apply, quotAut_mk, hx,
      QuotientGroup.mk'_apply]
    change θ (QuotientGroup.mk (g k)) = (MulAut.congr ψ) g (θ (QuotientGroup.mk k))
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
    have h1 : ψ.symm (θ (QuotientGroup.mk k)) = k := by
      rw [show ψ = e.symm.trans θ from rfl,
        MulEquiv.symm_trans_apply e.symm θ (θ (QuotientGroup.mk k)),
        MulEquiv.symm_apply_apply]
      change e (QuotientGroup.mk k) = k
      exact he_mk k
    rw [h1]
    show θ (QuotientGroup.mk (g k)) = ψ (g k)
    rw [show ψ (g k) = θ (QuotientGroup.mk (g k)) from by
      change θ (e.symm (g k)) = θ (QuotientGroup.mk (g k))
      rw [he_symm]]
  rw [← planeGen_iff_seitzHyperGamma Nat.prime_two (by rw [h4]; norm_num)]
  rw [hcongr] at h
  rwa [planeGen_map_congr ψ E] at h

private lemma det_one_add_eq_one_of_cube_zero {K : Type*} [Field K] [Finite K] {n : ℕ}
    [Nonempty (Fin n)] (hK : ringChar K ≠ 2) {N : Matrix (Fin n) (Fin n) K} (hN : N ^ 3 = 0) :
    (1 + N).det = 1 := by
  classical
  let ℓ := ringChar K
  have hℓ : ℓ.Prime := CharP.char_is_prime K ℓ
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := ringChar.charP K
  have : CharP (Matrix (Fin n) (Fin n) K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (Matrix (Fin n) (Fin n) K)).injective ℓ
  have hℓ2 : ℓ ≠ 2 := hK
  have hℓ3 : 3 ≤ ℓ := by
    have h2 := hℓ.two_le
    omega
  have hNℓ : N ^ ℓ = 0 := by
    obtain ⟨k, hk⟩ : ∃ k, ℓ = 3 + k := ⟨ℓ - 3, by omega⟩
    rw [hk, pow_add, hN, Matrix.zero_mul]
  have hXℓ : (1 + N) ^ ℓ = 1 := by
    rw [add_pow_char_of_commute ℓ (Commute.one_left N), hNℓ, add_zero, one_pow]
  have hdetpow : (1 + N).det ^ ℓ = 1 := by
    rw [← Matrix.det_pow, hXℓ, Matrix.det_one]
  have hzero : ((1 + N).det - 1) ^ ℓ = 0 := by
    rw [sub_pow_char_of_commute ℓ (Commute.one_right _), hdetpow, one_pow, sub_self]
  have hsub : (1 + N).det - 1 = 0 := (pow_eq_zero_iff (by omega : ℓ ≠ 0)).mp hzero
  exact sub_eq_zero.mp hsub

private lemma matrix_scalar_eq_smul_one {K : Type*} [Semiring K] {m : Type*}
    [Fintype m] [DecidableEq m] (a : K) :
    Matrix.scalar m a = a • (1 : Matrix m m K) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.scalar_apply, h]

theorem planeGen_of_fixed_unipotent {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : ringChar F ≠ 2) {E : Subgroup (MulAut (projectiveSL n F))} (hE : IsElemAbelian 2 E)
    (h4 : Nat.card E = 4) (X : SpecialLinearGroup (Fin n) F)
    (hX1 : (X : Matrix (Fin n) (Fin n) F) ≠ 1)
    (hX3 : ((X : Matrix (Fin n) (Fin n) F) - 1) ^ 3 = 0)
    (hfix : ∀ e ∈ E, e (proj n F X) = proj n F X) : PlaneGen E := by
  classical
  let ℓ := ringChar F
  have hℓ : ℓ.Prime := CharP.char_is_prime F ℓ
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ2 : ℓ ≠ 2 := hF
  have hℓ3 : 3 ≤ ℓ := by
    have h2 := hℓ.two_le
    omega
  have hn1 : 1 ≤ n := by
    rcases n with _ | n
    · exfalso
      apply hX1
      ext i
      exact i.elim0
    · omega
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have : CharP F ℓ := ringChar.charP F
  have : CharP (Matrix (Fin n) (Fin n) F) ℓ :=
    charP_of_injective_algebraMap (algebraMap F (Matrix (Fin n) (Fin n) F)).injective ℓ
  let N : Matrix (Fin n) (Fin n) F := (X : Matrix (Fin n) (Fin n) F) - 1
  have hN3 : N ^ 3 = 0 := by simpa [N] using hX3
  have hXeq : (X : Matrix (Fin n) (Fin n) F) = 1 + N := by
    simp [N]
  have hNℓ : N ^ ℓ = 0 := by
    obtain ⟨k, hk⟩ : ∃ k, ℓ = 3 + k := ⟨ℓ - 3, by omega⟩
    rw [hk, pow_add, hN3, Matrix.zero_mul]
  have hXmat : (X : Matrix (Fin n) (Fin n) F) ^ ℓ = 1 := by
    rw [hXeq, add_pow_char_of_commute ℓ (Commute.one_left N), hNℓ, add_zero, one_pow]
  have hXg : X ^ ℓ = 1 := by
    apply Subtype.ext
    change (X : Matrix (Fin n) (Fin n) F) ^ ℓ = 1
    exact hXmat
  have hπXpow : (proj n F X) ^ ℓ = 1 := by rw [← map_pow, hXg, map_one]
  have hπX1 : proj n F X ≠ 1 := by
    intro h
    have hker : X ∈ (proj n F).ker := MonoidHom.mem_ker.mpr h
    rw [ker_proj] at hker
    obtain ⟨c, hc, hXc⟩ := mem_scalars.mp hker
    have hNscalar : N = Matrix.scalar (Fin n) ((c : F) - 1) := by
      simp only [N, hXc]
      rw [← map_one (Matrix.scalar (Fin n)), ← map_sub]
    have h3 : (Matrix.scalar (Fin n) ((c : F) - 1)) ^ 3 = 0 := by
      rw [← hNscalar]
      exact hN3
    have h3' : Matrix.scalar (Fin n) (((c : F) - 1) ^ 3) = 0 := by
      rw [map_pow]
      exact h3
    have hentry := congrFun (congrFun h3' ⟨0, hn1⟩) ⟨0, hn1⟩
    simp [Matrix.scalar_apply] at hentry
    have hc1 : (c : F) = 1 := sub_eq_zero.mp hentry
    exact hX1 (by rw [hXc, hc1, map_one])
  have hord : orderOf (proj n F X) = ℓ := orderOf_eq_prime hπXpow hπX1
  let R : Subgroup (projectiveSL n F) := Subgroup.zpowers (proj n F X)
  have hRr : IsPGroup ℓ R := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord, pow_one]
  have hRne : R ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hπX1
  have hER : ∀ e ∈ E, R.map e.toMonoidHom = R := by
    intro e he
    rw [show R = Subgroup.zpowers (proj n F X) from rfl, MonoidHom.map_zpowers]
    show Subgroup.zpowers (e (proj n F X)) = Subgroup.zpowers (proj n F X)
    rw [hfix e he]
  have hgood : ∀ Q : Subgroup (projectiveSL n F), Q ≠ ⊥ →
      IsRadicalPGroup ℓ ⊤ Q →
      CFSG.GroupTheory.HasGoodOppositePRadicals ℓ ⊤ Q := by
    intro Q hQne hQ
    have hrad {Y : Subgroup (projectiveSL n F)} :
        IsRadicalPGroup ℓ ⊤ Y ↔ pCoreOf ℓ (Subgroup.normalizer (Y : Set _)) = Y := by
      rw [IsRadicalPGroup, top_inf_eq]
    have hker : (proj n F).ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) F) := by
      rw [ker_proj]
      exact (scalars_eq_center n F).le
    obtain ⟨V, hVrad, hVc, hVb, hQV, hall⟩ :=
      CFSG.StandardType.GGOppRad.intrinsic_opposition_of_sl_central_quotient
        (proj n F) (proj_surjective n F) hker Q hQne (hrad.mp hQ)
    refine ⟨V, ⟨hrad.mpr hVrad, hVc, ?_⟩, hQV, fun W hW => ?_⟩
    · simpa [top_inf_eq] using hVb
    · exact hall W (hrad.mp hW.1) hW.2.1 (by simpa [top_inf_eq] using hW.2.2)
  exact CFSG.LieType.SeitzGeneration.planeGen_of_normalized_rSubgroup_of_hasGoodOppositePRadicals
    hℓ2 hgood E hE h4 R hRne hRr hER

theorem planeGen_of_semilinear_not_linear {F : Type} [Field F] [Finite F] {n : ℕ}
    (hn : 3 ≤ n) (hF : ringChar F ≠ 2) {E : Subgroup (MulAut (projectiveSL n F))}
    (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4)
    (hσ : ∃ e ∈ E, e ∈ semilinearAutGroup n F ∧ e ∉ linearAutGroup n F) : PlaneGen E := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨ℓ, hcharF⟩ := CharP.exists F
  have hℓ : ℓ.Prime := CharP.char_is_prime F ℓ
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP F ℓ := hcharF
  obtain ⟨f, -, hcard⟩ := FiniteField.card F ℓ
  have hf1 : 1 ≤ (f : ℕ) := f.pos
  have hcardNat : Nat.card F = ℓ ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcard]
  have hℓ2 : ℓ ≠ 2 := by
    rw [← ringChar.eq F ℓ]
    exact hF
  obtain ⟨e, heE, heSemi, heNotLin⟩ := hσ
  have he2 : e ^ 2 = 1 := hE.2 e heE
  have he1 : e ≠ 1 := by
    intro h
    apply heNotLin
    rw [h]
    exact Subgroup.one_mem _
  have hord : orderOf e = 2 := orderOf_eq_prime he2 he1
  obtain ⟨-, hinjField, -, -, -, -, -, hdesc⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent hℓ hf1 hn hcardNat
  obtain ⟨-, σ, hσord, ⟨h, hhLin, heq⟩, hcardk⟩ :=
    hdesc 2 Nat.prime_two hℓ2.symm e heSemi heNotLin hord
  have hσ1 : σ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hσord
    omega
  have hσ2 : σ * σ = 1 := by
    have h := pow_orderOf_eq_one σ
    rwa [hσord] at h
  let E' : Subgroup (MulAut (projectiveSL n F)) := E.map (MulAut.congr h⁻¹).toMonoidHom
  have hcardE' : Nat.card E' = 4 := by
    rw [show E' = E.map (MulAut.congr h⁻¹).toMonoidHom from rfl,
      Subgroup.card_map_of_injective (MulAut.congr h⁻¹).injective, h4]
  have hE' : IsElemAbelian 2 E' :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 2 hE _
  have hfσmem : fieldAut n F σ ∈ E' := by
    refine Subgroup.mem_map.mpr ⟨h * fieldAut n F σ * h⁻¹, ?_, ?_⟩
    · rwa [← heq]
    · ext x
      simp [MulAut.congr_apply, MulEquiv.trans_apply]
  have hfσne : fieldAut n F σ ≠ 1 := by
    intro h1
    apply hσ1
    exact hinjField (by rw [h1, map_one])
  obtain ⟨y, hyE', hyzp⟩ :=
    exists_notMem_zpowers_of_card_sq Nat.prime_two hE'.2 (by rw [hcardE']; norm_num)
      hfσmem hfσne
  have hgen : E' = Subgroup.zpowers (fieldAut n F σ) ⊔ Subgroup.zpowers y :=
    (zpowers_sup_zpowers_eq_of_card_sq Nat.prime_two hE'.2 (by rw [hcardE']; norm_num)
      hfσmem hfσne hyE' hyzp).symm
  have hy2 : y ^ 2 = 1 := hE'.2 y hyE'
  obtain ⟨A, τ, ε, hε, hyform⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.automorphism_generation (K := F) hn |>.2 y
  have hτsq : τ * τ = 1 := by
    rcases (by omega : ε = 0 ∨ ε = 1) with hε0 | hε1
    · obtain ⟨C, θ, hθ, hmul⟩ :=
        CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.standard_form_mul A A τ τ hε hε
      have h1 : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F C *
          (fieldAut n F) (τ * τ) * CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut n F ^ θ = 1 := by
        have h2 : (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F A *
            (fieldAut n F) τ * CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut n F ^ ε) ^ 2 = 1 := by
          rw [hyform] at hy2
          exact hy2
        rw [pow_two, hε0] at h2
        rw [hε0] at hmul
        rwa [hmul] at h2
      have huniq := CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.standard_form_unique
        (A := C) (B := 1) (σ := τ * τ) (τ := 1) (ε := θ) (η := 0)
        hn hθ (by omega : (0 : ℕ) ≤ 1) (by simpa using h1)
      exact huniq.1
    · have h2 : (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F A *
          (fieldAut n F) τ * CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut n F) ^ 2 = 1 := by
        rw [hyform, hε1] at hy2
        exact hy2
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.sq_conjAut_fieldAut_dualAut] at h2
      exact (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.eq_one_of_conjAut_mul_fieldAut_eq_one
        hn _ _ h2).1
  have hτ : τ = 1 ∨ τ = σ := by
    by_cases hτ1 : τ = 1
    · exact Or.inl hτ1
    · have hστ : σ = τ :=
        CFSG.ProperTwoGeneratedCore.Lemma37.ringEquiv_eq_of_involution hσ1 hσ2 hτ1 hτsq
      exact Or.inr hστ.symm
  let y' : MulAut (projectiveSL n F) := if τ = 1 then y else y * fieldAut n F σ
  have hy'E' : y' ∈ E' := by
    by_cases hτ1 : τ = 1
    · simp [y', hτ1, hyE']
    · simp [y', hτ1, hyE', hfσmem, Subgroup.mul_mem]
  have hy'notzp : y' ∉ Subgroup.zpowers (fieldAut n F σ) := by
    by_cases hτ1 : τ = 1
    · simpa [y', hτ1] using hyzp
    · intro hmem
      apply hyzp
      have hfσinv : (fieldAut n F σ)⁻¹ ∈ Subgroup.zpowers (fieldAut n F σ) :=
        Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
      have hEq : y = y' * (fieldAut n F σ)⁻¹ := by
        simp [y', hτ1]
      rw [hEq]
      exact Subgroup.mul_mem _ hmem hfσinv
  have hy'2 : y' ^ 2 = 1 := hE'.2 y' hy'E'
  have hcomm : y' * fieldAut n F σ = fieldAut n F σ * y' := by
    simpa using hE'.1.is_comm.comm ⟨y', hy'E'⟩ ⟨fieldAut n F σ, hfσmem⟩
  have hy'form : ∃ (A' : GL (Fin n) F) (ε' : ℕ), ε' ≤ 1 ∧
      y' = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F A' *
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut n F ^ ε' := by
    by_cases hτ1 : τ = 1
    · refine ⟨A, ε, hε, ?_⟩
      rw [show y' = y from by simp [y', hτ1], hyform, hτ1, map_one, mul_one]
    · have hτσ : τ = σ := hτ.resolve_left hτ1
      obtain ⟨C, θ, hθ, hmul⟩ :=
        CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.standard_form_mul A 1 τ σ hε
          (by norm_num : (0 : ℕ) ≤ 1)
      refine ⟨C, θ, hθ, ?_⟩
      rw [show y' = y * fieldAut n F σ from by simp [y', hτ1], hyform]
      have hmul' : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F A *
          (fieldAut n F) τ * CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut n F ^ ε *
            (fieldAut n F) σ =
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F C *
            (fieldAut n F) (τ * σ) * CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut n F ^ θ := by
        simpa using hmul
      rw [hmul', hτσ, hσ2, map_one, mul_one]

  obtain ⟨A', η, hη, hyform'⟩ := hy'form
  have hyform'' : y' = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F A' *
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut n F ^ η := by
    simpa using hyform'
  have hσA : ∃ lam : F, lam ≠ 0 ∧
      (A' : Matrix (Fin n) (Fin n) F).map σ = lam • (A' : Matrix (Fin n) (Fin n) F) := by
    have hcf : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F A' *
        fieldAut n F σ = fieldAut n F σ * CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F A' := by
      rcases (by omega : η = 0 ∨ η = 1) with hη0 | hη1
      · simpa [hyform'', hη0, pow_zero, mul_one] using hcomm
      · have h := hcomm
        rw [hyform'', hη1] at h
        have h1 : (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F A' * fieldAut n F σ) *
            CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut n F =
            (fieldAut n F σ * CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F A') *
              CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut n F := by
          calc (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F A' * fieldAut n F σ) *
                CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut n F =
              CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F A' *
                (fieldAut n F σ * CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut n F) := by group
            _ = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F A' *
                (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut n F * fieldAut n F σ) := by
                  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut_mul_fieldAut]
            _ = (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F A' *
                CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut n F) * fieldAut n F σ := by group
            _ = (fieldAut n F σ * (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F A' *
                CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut n F)) := h
            _ = (fieldAut n F σ * CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F A') *
                CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut n F := by group
        exact mul_right_cancel h1
    have h2 : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F A' =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F
          (GeneralLinearGroup.map σ A') := by
      have h' : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F A' * fieldAut n F σ =
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F
            (GeneralLinearGroup.map σ A') * fieldAut n F σ := by
        rw [hcf, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut_mul_conjAut]
      exact mul_right_cancel h'
    let B : GL (Fin n) F := A'⁻¹ * GeneralLinearGroup.map σ A'
    have h3 : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F B = 1 := by
      have hB : B = A'⁻¹ * GeneralLinearGroup.map σ A' := rfl
      rw [hB, map_mul, map_inv, ← h2]
      group
    obtain ⟨u, hu⟩ :=
      (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff hn B).mp h3
    refine ⟨(u : F), u.ne_zero, ?_⟩
    have hGL : A' * GeneralLinearGroup.scalar (Fin n) u =
        GeneralLinearGroup.map σ A' := by
      rw [hu, show B = A'⁻¹ * GeneralLinearGroup.map σ A' from rfl]
      group
    have hmat := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) hGL
    have hmat' : (A' : Matrix (Fin n) (Fin n) F) * Matrix.scalar (Fin n) (u : F) =
        (A' : Matrix (Fin n) (Fin n) F).map σ := by
      simpa using hmat
    have hscalar : Matrix.scalar (Fin n) (u : F) =
        (u : F) • (1 : Matrix (Fin n) (Fin n) F) := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.scalar_apply, h]
    have hright : (A' : Matrix (Fin n) (Fin n) F) * Matrix.scalar (Fin n) (u : F) =
        (u : F) • (A' : Matrix (Fin n) (Fin n) F) := by
      rw [hscalar]
      simp
    rw [← hmat', hright]
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have : Nontrivial (Matrix (Fin n) (Fin n) F) := by infer_instance
  obtain ⟨lam, hlam, hX⟩ := hσA
  obtain ⟨cc, hcc, hccrat⟩ :=
    CFSG.LieType.SeitzGeneration.exists_rational_smul (p := 2) Nat.prime_two hℓ hf1 hcardNat
      σ hσord (X := (A' : Matrix (Fin n) (Fin n) F)) (lam := lam) (by
        intro h0
        apply A'.ne_zero
        ext i j
        simpa using congrFun (congrFun h0 i) j) hX

  let uu : Fˣ := Units.mk0 cc hcc
  let A'' : GL (Fin n) F := GeneralLinearGroup.scalar (Fin n) uu * A'
  have hA''coe : (A'' : Matrix (Fin n) (Fin n) F) = cc • (A' : Matrix (Fin n) (Fin n) F) := by
    rw [show A'' = GeneralLinearGroup.scalar (Fin n) uu * A' from rfl, Units.val_mul]
    change Matrix.scalar (Fin n) (cc : F) * (A' : Matrix (Fin n) (Fin n) F) =
      cc • (A' : Matrix (Fin n) (Fin n) F)
    rw [matrix_scalar_eq_smul_one (m := Fin n), Matrix.smul_mul, Matrix.one_mul]
  have hA''rat : (A'' : Matrix (Fin n) (Fin n) F).map σ = (A'' : Matrix (Fin n) (Fin n) F) := by
    rw [hA''coe]
    exact hccrat
  have hA''cA : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F A'' =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F A' := by
    rw [show A'' = GeneralLinearGroup.scalar (Fin n) uu * A' from rfl, map_mul,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_scalar, one_mul]
  let kk : Subfield F := CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ
  have hkk : ∀ x : F, x ∈ kk ↔ σ x = x := fun x => Iff.rfl
  have : CharP kk ℓ := Subfield.charP kk ℓ
  have : Finite kk := by infer_instance
  have hkk2 : ringChar kk ≠ 2 := by
    rw [ringChar.eq kk ℓ]
    exact hℓ2
  let A0 : Matrix (Fin n) (Fin n) kk := Matrix.of fun i j =>
    ⟨(A'' : Matrix (Fin n) (Fin n) F) i j, (hkk _).mpr (by
      have h := congrFun (congrFun hA''rat i) j
      simpa [Matrix.map_apply] using h)⟩
  have hA0map : A0.map (Subfield.subtype kk) = (A'' : Matrix (Fin n) (Fin n) F) := by
    ext i j
    simp [A0]
  have hdetA : IsUnit (A'' : Matrix (Fin n) (Fin n) F).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp ⟨A'', rfl⟩
  have hmain : ∃ X : SpecialLinearGroup (Fin n) F,
      (X : Matrix (Fin n) (Fin n) F) ≠ 1 ∧
      ((X : Matrix (Fin n) (Fin n) F) - 1) ^ 3 = 0 ∧
      (∀ e ∈ E', e (proj n F X) = proj n F X) := by
    rcases (by omega : η = 0 ∨ η = 1) with hη0 | hη1
    · have hy'eq : y' = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F A'' := by
        rw [hyform'', hη0, pow_zero, mul_one, ← hA''cA]
      have h2 : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F (A'' * A'') = 1 := by
        have h := hy'2
        rw [hy'eq, pow_two] at h
        rwa [← map_mul] at h
      obtain ⟨u2, hu2⟩ :=
        (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff hn (A'' * A'')).mp h2
      have hA2 : (A'' : Matrix (Fin n) (Fin n) F) * (A'' : Matrix (Fin n) (Fin n) F) =
          (u2 : F) • 1 := by
        have h' : A'' * A'' = GeneralLinearGroup.scalar (Fin n) u2 := hu2.symm
        have h := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) h'
        rw [Units.val_mul, GeneralLinearGroup.coe_scalar,
          matrix_scalar_eq_smul_one (m := Fin n)] at h
        exact h
      have hA2rat : ((A'' : Matrix (Fin n) (Fin n) F) *
          (A'' : Matrix (Fin n) (Fin n) F)).map σ =
          (A'' : Matrix (Fin n) (Fin n) F) * (A'' : Matrix (Fin n) (Fin n) F) := by
        rw [Matrix.map_mul, hA''rat]
      have hufix : σ (u2 : F) = (u2 : F) := by
        have h1 := congrFun (congrFun hA2rat ⟨0, by omega⟩) ⟨0, by omega⟩
        simp only [Matrix.map_apply] at h1
        rw [hA2] at h1
        simpa using h1
      let μ0 : kk := ⟨(u2 : F), (hkk _).mpr hufix⟩
      have hA02 : A0 * A0 = μ0 • 1 := by
        apply Matrix.map_injective (f := Subfield.subtype kk) (fun x y h => Subtype.ext h)
        change (A0 * A0).map (Subfield.subtype kk) =
          ((μ0 : kk) • (1 : Matrix (Fin n) (Fin n) kk)).map (Subfield.subtype kk)
        rw [Matrix.map_mul, hA0map]
        rw [Matrix.map_smul (Subfield.subtype kk) (μ0 : kk) (fun a => rfl)]
        rw [Matrix.map_one (Subfield.subtype kk) (map_zero _) (map_one _)]
        rw [hA2]
        rfl
      have hA0ns : ∀ c : kk, A0 ≠ c • 1 := by
        intro c hc
        have hscal : (A'' : Matrix (Fin n) (Fin n) F) = (c : F) • 1 := by
          calc (A'' : Matrix (Fin n) (Fin n) F) = A0.map (Subfield.subtype kk) := hA0map.symm
            _ = ((c : kk) • (1 : Matrix (Fin n) (Fin n) kk)).map (Subfield.subtype kk) := by rw [hc]
            _ = (c : F) • (1 : Matrix (Fin n) (Fin n) F) := by
              rw [Matrix.map_smul (Subfield.subtype kk) c (fun a => rfl)]
              rw [Matrix.map_one (Subfield.subtype kk) (map_zero _) (map_one _)]
              rfl
        have hc0F : (c : F) ≠ 0 := by
          intro h0
          have hzero : (A'' : Matrix (Fin n) (Fin n) F) = 0 := by
            simp [h0] at hscal
          have hunit : IsUnit (A'' : Matrix (Fin n) (Fin n) F) := ⟨A'', rfl⟩
          rw [hzero] at hunit
          exact not_isUnit_zero hunit
        have hcA : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F A'' = 1 := by
          have hu : A'' = GeneralLinearGroup.scalar (Fin n) (Units.mk0 (c : F) hc0F) := by
            ext i j
            rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
            have h := congrFun (congrFun hscal i) j
            rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at h
            by_cases hij : i = j
            · simp [hij] at h ⊢
              exact h
            · simp [hij] at h ⊢
              exact h
          rw [hu, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_scalar]
        have hy1 : y' = 1 := by
          rw [hy'eq, hcA]
        exact hy'notzp (by rw [hy1]; exact Subgroup.one_mem _)
      obtain ⟨N0, hN0, hN02, hN0A⟩ :=
        exists_sq_zero_commute_of_sq_scalar hn hA02 hA0ns
      let N : Matrix (Fin n) (Fin n) F := N0.map (Subfield.subtype kk)
      have hN : N ≠ 0 := by
        intro h
        apply hN0
        apply Matrix.map_injective (f := Subfield.subtype kk) (fun x y h => Subtype.ext h)
        simpa [N] using h
      have hN2 : N * N = 0 := by
        have h := congrArg (fun M : Matrix (Fin n) (Fin n) kk => M.map (Subfield.subtype kk)) hN02
        rw [Matrix.map_mul] at h
        simpa [N] using h
      have hNA : (A'' : Matrix (Fin n) (Fin n) F) * N =
          N * (A'' : Matrix (Fin n) (Fin n) F) := by
        have h := congrArg (fun M : Matrix (Fin n) (Fin n) kk => M.map (Subfield.subtype kk)) hN0A
        rw [Matrix.map_mul, Matrix.map_mul, hA0map] at h
        simpa [N] using h
      let X : Matrix (Fin n) (Fin n) F := 1 + N
      have hX1 : X ≠ 1 := by
        intro h
        apply hN
        simpa [X] using sub_eq_zero.mpr h
      have hXsub : X - 1 = N := by simp [X]
      have hN3 : N ^ 3 = 0 := by
        calc N ^ 3 = N ^ 2 * N := by rw [pow_succ]
          _ = 0 := by rw [pow_two, hN2, Matrix.zero_mul]
      have hX3 : (X - 1) ^ 3 = 0 := by rw [hXsub, hN3]
      have hXdet : X.det = 1 := by
        change (1 + N).det = 1
        exact det_one_add_eq_one_of_cube_zero hF hN3
      let Xsl : SpecialLinearGroup (Fin n) F := ⟨X, hXdet⟩
      have hNrat : N.map σ = N := by
        ext i j
        simp only [N, Matrix.map_apply]
        exact (hkk _).mp (N0 i j).2
      have hXrat : X.map σ = X := by
        change (1 + N).map σ = 1 + N
        rw [Matrix.map_add σ (map_add σ), hNrat]
        rw [Matrix.map_one σ (map_zero σ) (map_one σ)]
      have hAX : (A'' : Matrix (Fin n) (Fin n) F) * X = X * (A'' : Matrix (Fin n) (Fin n) F) := by
        simp only [X, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, hNA]
      have hy'fix : y' (proj n F Xsl) = proj n F Xsl := by
        rw [hy'eq, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_proj]
        congr 1
        apply Subtype.ext
        change (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F A'' Xsl :
          Matrix (Fin n) (Fin n) F) = X
        rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_slConjugation]
        have hdetu : IsUnit (A'' : Matrix (Fin n) (Fin n) F).det :=
          (Matrix.isUnit_iff_isUnit_det _).mp ⟨A'', rfl⟩
        have hAXsl : (A'' : Matrix (Fin n) (Fin n) F) * (↑Xsl : Matrix (Fin n) (Fin n) F) =
            (↑Xsl : Matrix (Fin n) (Fin n) F) * (A'' : Matrix (Fin n) (Fin n) F) := by
          simpa using hAX
        calc (A'' : Matrix (Fin n) (Fin n) F) * (↑Xsl : Matrix (Fin n) (Fin n) F) *
              (↑((A'')⁻¹) : Matrix (Fin n) (Fin n) F) =
            (↑Xsl : Matrix (Fin n) (Fin n) F) * (A'' : Matrix (Fin n) (Fin n) F) *
              (↑((A'')⁻¹) : Matrix (Fin n) (Fin n) F) := by rw [hAXsl]
          _ = (↑Xsl : Matrix (Fin n) (Fin n) F) *
              ((A'' : Matrix (Fin n) (Fin n) F) * (↑((A'')⁻¹) : Matrix (Fin n) (Fin n) F)) :=
              Matrix.mul_assoc _ _ _
          _ = (↑Xsl : Matrix (Fin n) (Fin n) F) *
              ((A'' : Matrix (Fin n) (Fin n) F) * (A'' : Matrix (Fin n) (Fin n) F)⁻¹) := by
              rw [GeneralLinearGroup.coe_inv]
          _ = X := by
              rw [Matrix.mul_nonsing_inv _ hdetu, Matrix.mul_one]
      have hfσfix : fieldAut n F σ (proj n F Xsl) = proj n F Xsl := by
        rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut_proj]
        congr 1
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.map_apply_coe]
        exact hXrat
      refine ⟨Xsl, ?_, hX3, ?_⟩
      · exact hX1
      · intro e he
        have hyfix : y (proj n F Xsl) = proj n F Xsl := by
          by_cases hτ1 : τ = 1
          · rwa [show y = y' from by simp [y', hτ1]]
          · have hys : y = y' * fieldAut n F σ := by
              simp only [y', if_neg hτ1]
              rw [mul_assoc, ← map_mul, hσ2, map_one, mul_one]
            rw [hys, MulAut.mul_apply, hfσfix, hy'fix]
        have hstab : (Subgroup.zpowers (fieldAut n F σ) ⊔ Subgroup.zpowers y) ≤
            MulAction.stabilizer (MulAut (projectiveSL n F)) (proj n F Xsl) :=
          sup_le (Subgroup.zpowers_le.mpr (by simpa [MulAction.mem_stabilizer_iff] using hfσfix))
            (Subgroup.zpowers_le.mpr (by simpa [MulAction.mem_stabilizer_iff] using hyfix))
        rw [hgen] at he
        simpa [MulAction.mem_stabilizer_iff] using hstab he

    · have hy'eq1 : y' = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F A'' *
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut n F := by
        rw [hyform'', hη1, pow_one, ← hA''cA]
      have h2 : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F
          (A'' * Matrix.GeneralLinearGroup.inverseTranspose A'') = 1 := by
        have h := hy'2
        rw [hy'eq1] at h
        have hsq : (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F A'' *
            CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut n F) ^ 2 =
            CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut n F
              (A'' * Matrix.GeneralLinearGroup.inverseTranspose A'') := by
          have hsq0 := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.sq_conjAut_fieldAut_dualAut
            (n := n) (K := F) A'' (1 : F ≃+* F)
          rw [show ((1 : F ≃+* F) : F →+* F) = RingHom.id F from rfl,
            Matrix.GeneralLinearGroup.map_id] at hsq0
          simpa using hsq0
        rwa [hsq] at h
      obtain ⟨cc, hcc⟩ :=
        (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff hn
          (A'' * Matrix.GeneralLinearGroup.inverseTranspose A'')).mp h2
      have hmat : (A'' : Matrix (Fin n) (Fin n) F) * ((A'' : Matrix (Fin n) (Fin n) F)ᵀ)⁻¹ =
          (cc : F) • 1 := by
        have h := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) hcc
        rw [GeneralLinearGroup.coe_scalar, Units.val_mul,
          Matrix.GeneralLinearGroup.coe_inverseTranspose, GeneralLinearGroup.coe_inv,
          Matrix.transpose_nonsing_inv, matrix_scalar_eq_smul_one (m := Fin n)] at h
        exact h.symm
      have hdetT : IsUnit ((A'' : Matrix (Fin n) (Fin n) F)ᵀ).det := by
        rwa [Matrix.det_transpose]
      have hAt : (A'' : Matrix (Fin n) (Fin n) F) =
          (cc : F) • (A'' : Matrix (Fin n) (Fin n) F)ᵀ := by
        have h := congrArg (fun M : Matrix (Fin n) (Fin n) F => M * (A'' : Matrix (Fin n) (Fin n) F)ᵀ) hmat
        rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul ((A'' : Matrix (Fin n) (Fin n) F)ᵀ) hdetT,
          Matrix.mul_one] at h
        simpa [Matrix.smul_mul, Matrix.one_mul] using h
      have hAtt : (A'' : Matrix (Fin n) (Fin n) F)ᵀ =
          (cc : F) • (A'' : Matrix (Fin n) (Fin n) F) := by
        calc (A'' : Matrix (Fin n) (Fin n) F)ᵀ = ((cc : F) • (A'' : Matrix (Fin n) (Fin n) F)ᵀ)ᵀ :=
          congrArg Matrix.transpose hAt
          _ = (cc : F) • (A'' : Matrix (Fin n) (Fin n) F) := by
            rw [Matrix.transpose_smul, Matrix.transpose_transpose]
      have hc2 : (cc : F) ^ 2 = 1 := by
        have h : (A'' : Matrix (Fin n) (Fin n) F) = (cc : F) ^ 2 • (A'' : Matrix (Fin n) (Fin n) F) := by
          calc (A'' : Matrix (Fin n) (Fin n) F) = (cc : F) • (A'' : Matrix (Fin n) (Fin n) F)ᵀ := hAt
            _ = (cc : F) • ((cc : F) • (A'' : Matrix (Fin n) (Fin n) F)) := by rw [hAtt]
            _ = (cc : F) ^ 2 • (A'' : Matrix (Fin n) (Fin n) F) := by
              rw [smul_smul, pow_two]
        obtain ⟨i, j, hij⟩ : ∃ i j, (A'' : Matrix (Fin n) (Fin n) F) i j ≠ 0 := by
          by_contra hcon
          push Not at hcon
          apply A''.ne_zero
          ext i j
          simpa using hcon i j
        have h1 := congrFun (congrFun h i) j
        simp only [Matrix.smul_apply, smul_eq_mul] at h1
        have h2 : (cc : F) ^ 2 * (A'' : Matrix (Fin n) (Fin n) F) i j =
            1 * (A'' : Matrix (Fin n) (Fin n) F) i j := by
          rw [one_mul]
          exact h1.symm
        exact mul_right_cancel₀ hij h2
      have hcpm : cc = 1 ∨ cc = -1 := by
        rcases sq_eq_one_iff.mp hc2 with h | h
        · left; ext; simpa using h
        · right; ext; simpa using h
      have hA0det : IsUnit A0.det := by
        rw [isUnit_iff_ne_zero]
        intro h0
        have hmapdet : (Subfield.subtype kk) A0.det = (A'' : Matrix (Fin n) (Fin n) F).det := by
          have h := RingHom.map_det (Subfield.subtype kk) A0
          rw [show (Subfield.subtype kk).mapMatrix A0 = A0.map (Subfield.subtype kk) from rfl,
            hA0map] at h
          exact h
        rw [h0, map_zero] at hmapdet
        exact hdetA.ne_zero hmapdet.symm
      have hsym : A0ᵀ = A0 ∨ A0ᵀ = -A0 := by
        have hmapT : (A0ᵀ).map (Subfield.subtype kk) = (A'' : Matrix (Fin n) (Fin n) F)ᵀ := by
          rw [Matrix.transpose_map, hA0map]
        rcases hcpm with hc1 | hcneg
        · left
          apply Matrix.map_injective (f := Subfield.subtype kk) (fun x y h => Subtype.ext h)
          change (A0ᵀ).map (Subfield.subtype kk) = A0.map (Subfield.subtype kk)
          rw [hmapT, hA0map]
          have hc1F : (cc : F) = 1 := by simpa using congrArg (fun u : Fˣ => (u : F)) hc1
          simpa [hc1F] using hAtt
        · right
          apply Matrix.map_injective (f := Subfield.subtype kk) (fun x y h => Subtype.ext h)
          change (A0ᵀ).map (Subfield.subtype kk) = (-A0).map (Subfield.subtype kk)
          rw [hmapT]
          rw [show (-A0).map (Subfield.subtype kk) = -(A'' : Matrix (Fin n) (Fin n) F) from by
            ext i j
            simp [← hA0map]]
          have hcnegF : (cc : F) = -1 := by simpa using congrArg (fun u : Fˣ => (u : F)) hcneg
          simpa [hcnegF] using hAtt
      obtain ⟨Y0, hY0, hY03, hYiso⟩ :=
        exists_unipotent_isometry hkk2 hn hA0det hsym
      let X0 : Matrix (Fin n) (Fin n) kk := Y0ᵀ
      have hX0ne : X0 ≠ 1 := by
        intro h
        apply hY0
        exact Matrix.transpose_injective (by simpa [X0] using h)
      have hX03 : (X0 - 1) ^ 3 = 0 := by
        have h := congrArg Matrix.transpose hY03
        simpa [X0, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_pow] using h
      have hX0iso : X0 * A0 * X0ᵀ = A0 := by simpa [X0] using hYiso
      let X : Matrix (Fin n) (Fin n) F := X0.map (Subfield.subtype kk)
      have hX0map : X0.map (Subfield.subtype kk) = X := rfl
      have hXrat : X.map σ = X := by
        ext i j
        simp only [X, Matrix.map_apply]
        exact (hkk _).mp (X0 i j).2
      have hX1 : X ≠ 1 := by
        intro h
        apply hX0ne
        apply Matrix.map_injective (f := Subfield.subtype kk) (fun x y h => Subtype.ext h)
        simpa [X] using h
      have hX3 : (X - 1) ^ 3 = 0 := by
        have h := congrArg (Subfield.subtype kk).mapMatrix hX03
        rw [map_pow, map_sub, map_one, map_zero] at h
        exact h
      have hXisoF : X * (A'' : Matrix (Fin n) (Fin n) F) * Xᵀ = (A'' : Matrix (Fin n) (Fin n) F) := by
        have hT : Xᵀ = (X0ᵀ).map (Subfield.subtype kk) := Matrix.transpose_map.symm
        show X * (A'' : Matrix (Fin n) (Fin n) F) * Xᵀ = (A'' : Matrix (Fin n) (Fin n) F)
        rw [hT, ← hA0map]
        show X0.map (Subfield.subtype kk) * A0.map (Subfield.subtype kk) *
          (X0ᵀ).map (Subfield.subtype kk) = A0.map (Subfield.subtype kk)
        rw [← Matrix.map_mul, ← Matrix.map_mul, hX0iso]
      have hXdet : X.det = 1 := by
        have h := det_one_add_eq_one_of_cube_zero (N := X - 1) hF (by simpa using hX3)
        simpa [sub_add_cancel] using h
      let Xsl : SpecialLinearGroup (Fin n) F := ⟨X, hXdet⟩
      have hXdetu : IsUnit X.det := ⟨1, by simp [hXdet]⟩
      have hXTdetu : IsUnit (Xᵀ).det := by
        rwa [Matrix.det_transpose]
      have hfixmat : (A'' : Matrix (Fin n) (Fin n) F) * (Xᵀ)⁻¹ *
          (A'' : Matrix (Fin n) (Fin n) F)⁻¹ = X := by
        have h1 : X * (A'' : Matrix (Fin n) (Fin n) F) * Xᵀ * (Xᵀ)⁻¹ =
            (A'' : Matrix (Fin n) (Fin n) F) * (Xᵀ)⁻¹ := by
          rw [hXisoF]
        rw [← h1, Matrix.mul_assoc (X * (A'' : Matrix (Fin n) (Fin n) F)) Xᵀ (Xᵀ)⁻¹,
          Matrix.mul_nonsing_inv _ hXTdetu, Matrix.mul_one, Matrix.mul_assoc,
          Matrix.mul_nonsing_inv _ hdetA, Matrix.mul_one]
      have hXinvmat : (↑((Xsl⁻¹).transpose) : Matrix (Fin n) (Fin n) F) = (Xᵀ)⁻¹ := by
        rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_inv]
        change ((X : Matrix (Fin n) (Fin n) F).adjugate)ᵀ = (Xᵀ)⁻¹
        have hadj : (X : Matrix (Fin n) (Fin n) F).adjugate = X⁻¹ := by
          rw [Matrix.nonsing_inv_apply (A := X) hXdetu]
          have hunit1 : hXdetu.unit = 1 := by
            ext
            rw [Units.val_one, IsUnit.unit_spec, hXdet]
          rw [hunit1]
          simp
        rw [hadj, Matrix.transpose_nonsing_inv]
      have hy'fix : y' (proj n F Xsl) = proj n F Xsl := by
        rw [hy'eq1, MulAut.mul_apply,
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dualAut_proj,
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_proj]
        congr 1
        apply Subtype.ext
        change (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F A''
          ((Xsl⁻¹).transpose) : Matrix (Fin n) (Fin n) F) = X
        rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_slConjugation]
        rw [GeneralLinearGroup.coe_inv, hXinvmat]
        exact hfixmat
      have hfσfix : fieldAut n F σ (proj n F Xsl) = proj n F Xsl := by
        rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.fieldAut_proj]
        congr 1
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.map_apply_coe]
        exact hXrat
      refine ⟨Xsl, hX1, hX3, ?_⟩
      intro e he
      have hyfix : y (proj n F Xsl) = proj n F Xsl := by
        by_cases hτ1 : τ = 1
        · rwa [show y = y' from by simp [y', hτ1]]
        · have hys : y = y' * fieldAut n F σ := by
            simp only [y', if_neg hτ1]
            rw [mul_assoc, ← map_mul, hσ2, map_one, mul_one]
          rw [hys, MulAut.mul_apply, hfσfix, hy'fix]
      have hstab : (Subgroup.zpowers (fieldAut n F σ) ⊔ Subgroup.zpowers y) ≤
          MulAction.stabilizer (MulAut (projectiveSL n F)) (proj n F Xsl) :=
        sup_le (Subgroup.zpowers_le.mpr (by simpa [MulAction.mem_stabilizer_iff] using hfσfix))
          (Subgroup.zpowers_le.mpr (by simpa [MulAction.mem_stabilizer_iff] using hyfix))
      rw [hgen] at he
      simpa [MulAction.mem_stabilizer_iff] using hstab he

  obtain ⟨X, hX1, hX3, hfix⟩ := hmain
  exact (planeGen_map_congr h⁻¹ E).mp
    (planeGen_of_fixed_unipotent hF hE' hcardE' X hX1 hX3 hfix)

end CFSG.LocalAnalysis.WeakClosure81.PSLOuter

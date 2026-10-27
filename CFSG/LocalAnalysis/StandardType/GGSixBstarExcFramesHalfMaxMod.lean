module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxDefs
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LieType.Chevalley.LangRootArithmeticDet
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Abel

public section

namespace CFSG.StandardType

namespace ExcFramesHalf

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.E6

open scoped Matrix

theorem exists_vecMulVec_of_rank_le_one {K : Type*} [Field K] {n : ℕ}
    {R : Matrix (Fin n) (Fin n) K} (hrank : R.rank ≤ 1) (hR : R ≠ 0) :
    ∃ l c : Fin n → K, l ≠ 0 ∧ c ≠ 0 ∧ R = Matrix.vecMulVec l c := by
  classical
  have hfin : Module.finrank K (LinearMap.range R.mulVecLin) ≤ 1 := by
    simpa only [Matrix.rank] using hrank
  obtain ⟨v, hv⟩ := (finrank_le_one_iff (K := K) (V := LinearMap.range R.mulVecLin)).mp hfin
  have hcol_mem : ∀ j : Fin n, R.col j ∈ LinearMap.range R.mulVecLin := fun j =>
    ⟨Pi.single j (1 : K), by rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]⟩
  let c : Fin n → K := fun j => Classical.choose (hv ⟨R.col j, hcol_mem j⟩)
  have hc : ∀ j, c j • (v : Fin n → K) = R.col j := fun j =>
    congrArg Subtype.val (Classical.choose_spec (hv ⟨R.col j, hcol_mem j⟩))
  have hvne : (v : Fin n → K) ≠ 0 := by
    intro hv0
    apply hR
    ext i j
    have h := hc j
    rw [hv0] at h
    have hz : R.col j = 0 := by rw [← h]; simp
    have := congrFun hz i
    simpa [Matrix.col_apply] using this
  have hcne : c ≠ 0 := by
    intro hc0
    apply hR
    ext i j
    have h := hc j
    rw [hc0] at h
    have hz : R.col j = 0 := by rw [← h]; simp
    have := congrFun hz i
    simpa [Matrix.col_apply] using this
  refine ⟨v, c, hvne, hcne, ?_⟩
  ext i j
  have := congrFun (hc j) i
  rw [Pi.smul_apply, smul_eq_mul, Matrix.col_apply] at this
  rw [Matrix.vecMulVec_apply, ← this, mul_comm]

theorem matrix_mul_self_eq_one_of_isometry_rank_le_one {K : Type*} [Field K] {n : ℕ}
    (B N : Matrix (Fin n) (Fin n) K) (hBsymm : Bᵀ = B) (hBdet : B.det ≠ 0)
    (hiso : Nᵀ * B * N = B) (hrank : (N + 1).rank ≤ 1) : N * N = 1 := by
  by_cases h0 : N + 1 = 0
  · have hN : N = -1 := eq_neg_of_add_eq_zero_left h0
    rw [hN]; simp
  · obtain ⟨l, c, hl, hc, hRl⟩ := exists_vecMulVec_of_rank_le_one hrank h0
    let b : Fin n → K := B *ᵥ l
    let β : K := l ⬝ᵥ b
    have hisoR : (N + 1)ᵀ * B * (N + 1) = (N + 1)ᵀ * B + B * (N + 1) := by
      rw [Matrix.transpose_add, Matrix.transpose_one, add_mul, one_mul, add_mul, mul_add,
        mul_add, mul_one, mul_one, hiso]
      abel
    have hstar : β • Matrix.vecMulVec c c = Matrix.vecMulVec c b + Matrix.vecMulVec b c := by
      rw [hRl] at hisoR
      have hb : l ᵥ* B = b := by rw [← Matrix.mulVec_transpose, hBsymm]
      have hL : (Matrix.vecMulVec l c)ᵀ * B * Matrix.vecMulVec l c
          = β • Matrix.vecMulVec c c := by
        rw [Matrix.transpose_vecMulVec, Matrix.vecMulVec_mul, hb, Matrix.vecMulVec_mul_vecMulVec,
          dotProduct_comm b l, Matrix.vecMulVec_smul]
      have hRs : (Matrix.vecMulVec l c)ᵀ * B = Matrix.vecMulVec c b := by
        rw [Matrix.transpose_vecMulVec, Matrix.vecMulVec_mul, hb]
      have hRr : B * Matrix.vecMulVec l c = Matrix.vecMulVec b c := by
        rw [Matrix.mul_vecMulVec]
      rw [hL, hRs, hRr] at hisoR
      exact hisoR
    have hentry : ∀ i j, β * (c i * c j) = c i * b j + b i * c j := by
      intro i j
      have h := congrFun (congrFun hstar i) j
      simpa [Matrix.vecMulVec_apply, smul_eq_mul] using h
    obtain ⟨i₀, hc₀'⟩ := Function.ne_iff.mp hc
    have hc₀ : c i₀ ≠ 0 := by simpa using hc₀'
    let μ : K := (β * c i₀ - b i₀) / c i₀
    have hmu : ∀ j, b j = μ * c j := by
      intro j
      have h := hentry i₀ j
      have hb0 : c i₀ * b j = (β * c i₀ - b i₀) * c j := by
        have h' : c i₀ * b j = β * (c i₀ * c j) - b i₀ * c j := by
          rw [eq_sub_iff_add_eq]; exact h.symm
        rw [h']; ring
      have : b j = (β * c i₀ - b i₀) * c j / c i₀ := by
        rw [eq_div_iff hc₀, mul_comm (b j) (c i₀), hb0]
      simpa [μ, div_mul_eq_mul_div] using this
    have hβ2 : β = 2 * μ := by
      have h := hentry i₀ i₀
      rw [hmu i₀] at h
      have h2 : β * (c i₀ * c i₀) = (2 * μ) * (c i₀ * c i₀) := by rw [h]; ring
      exact mul_right_cancel₀ (mul_ne_zero hc₀ hc₀) h2
    have hβlc : β = μ * (l ⬝ᵥ c) := by
      have hbmu : b = μ • c := funext fun j => by rw [hmu j, Pi.smul_apply, smul_eq_mul]
      show l ⬝ᵥ b = μ * (l ⬝ᵥ c)
      rw [hbmu, dotProduct_smul, smul_eq_mul]
    have hμne : μ ≠ 0 := by
      intro hμ0
      have hbzero : b = 0 := funext fun j => by rw [hmu j, hμ0, zero_mul]; rfl
      have hBl : B *ᵥ l = 0 := by simpa [b] using hbzero
      exact hl (Matrix.eq_zero_of_mulVec_eq_zero hBdet hBl)
    have hlc : l ⬝ᵥ c = 2 := by
      have h : μ * (l ⬝ᵥ c) = μ * 2 := by rw [← hβlc, hβ2, mul_comm 2 μ]
      exact mul_left_cancel₀ hμne h
    have hRsq : Matrix.vecMulVec l c * Matrix.vecMulVec l c = (2 : K) • Matrix.vecMulVec l c := by
      rw [Matrix.vecMulVec_mul_vecMulVec, dotProduct_comm c l, hlc, Matrix.vecMulVec_smul]
    have hN : N = Matrix.vecMulVec l c - 1 := by
      rw [← hRl]; abel
    calc N * N = (Matrix.vecMulVec l c - 1) * (Matrix.vecMulVec l c - 1) := by rw [hN]
      _ = Matrix.vecMulVec l c * Matrix.vecMulVec l c - Matrix.vecMulVec l c
            - Matrix.vecMulVec l c + 1 := by noncomm_ring
      _ = (2 : K) • Matrix.vecMulVec l c - Matrix.vecMulVec l c - Matrix.vecMulVec l c + 1 := by
            rw [hRsq]
      _ = 1 := by rw [two_smul]; abel

theorem natCard_neg_one_eigenspace {K : Type*} [Field K] [Fintype K] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) K) :
    Nat.card {z : Fin n → K // Nᵀ *ᵥ z = (-1 : K) • z}
      = Nat.card K ^ Module.finrank K (LinearMap.ker (Nᵀ + 1).mulVecLin) := by
  have hneg : ∀ z : Fin n → K, ((-1 : K) • z : Fin n → K) = -z := by
    intro z
    funext i
    change (-1 : K) * z i = -z i
    calc (-1 : K) * z i = -((1 : K) * z i) := neg_mul (1 : K) (z i)
      _ = -z i := by rw [one_mul]
  let g : (Fin n → K) →ₗ[K] (Fin n → K) := (Nᵀ + 1).mulVecLin
  have hker : ∀ z, (Nᵀ *ᵥ z = (-1 : K) • z) ↔ z ∈ LinearMap.ker g := by
    intro z
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.add_mulVec, Matrix.one_mulVec,
      add_eq_zero_iff_eq_neg, hneg]
  calc Nat.card {z : Fin n → K // Nᵀ *ᵥ z = (-1 : K) • z}
      = Nat.card (LinearMap.ker g) := Nat.card_congr (Equiv.subtypeEquivRight hker)
    _ = Nat.card K ^ Module.finrank K (LinearMap.ker g) :=
        Module.natCard_eq_pow_finrank

theorem rank_add_one_le_one_of_card_eigenspace {K : Type*} [Field K] [Fintype K] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) K)
    (hge : Nat.card K ^ (n - 1) ≤ Nat.card {z : Fin n → K // Nᵀ *ᵥ z = (-1 : K) • z}) :
    (N + 1).rank ≤ 1 := by
  have hcard := natCard_neg_one_eigenspace N
  have hle : n - 1 ≤ Module.finrank K (LinearMap.ker (Nᵀ + 1).mulVecLin) := by
    rw [hcard] at hge
    have hK : 1 < Nat.card K := by
      rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
    exact (Nat.pow_le_pow_iff_right hK).mp hge
  let g : (Fin n → K) →ₗ[K] (Fin n → K) := (Nᵀ + 1).mulVecLin
  have hdim : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  have hrank_eq : (N + 1).rank = Module.finrank K (LinearMap.range g) := by
    rw [← Matrix.rank_transpose (N + 1)]
    have htrans : Nᵀ + 1 = (N + 1)ᵀ := by rw [Matrix.transpose_add, Matrix.transpose_one]
    rw [← htrans]
    rfl
  rw [hrank_eq]
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  rw [hdim] at hrn
  have hle_g : n - 1 ≤ Module.finrank K (LinearMap.ker g) := hle
  omega

section Mod


theorem weylMatrix_transpose_mul_symmetrizedCartan_mul {τ : Tag} (w : WeylGroup τ) :
    (weylMatrix w)ᵀ * (τ.symmetrizedCartan * weylMatrix w) = τ.symmetrizedCartan := by
  ext i j
  have h := iform_smul w (Pi.single i (1 : ℤ)) (Pi.single j (1 : ℤ))
  rw [← weylMatrix_mulVec w, ← weylMatrix_mulVec w,
    ← dotProduct_mulVec_eq_iform, ← dotProduct_mulVec_eq_iform] at h
  rw [Matrix.mulVec_single_one (weylMatrix w) i,
    Matrix.mulVec_single_one (weylMatrix w) j,
    Matrix.mulVec_single_one τ.symmetrizedCartan j] at h
  rw [← Matrix.col_mul_eq_mulVec_col] at h
  rw [single_dotProduct, one_mul, Matrix.col_apply] at h
  exact h

theorem modMat_weylMatrix_mul_self_eq_one {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (w : WeylGroup τ)
    (hge : p ^ (τ.rank - 1) ≤ Nat.card {z : Fin τ.rank → ZMod p //
      (modMat p (weylMatrix w))ᵀ *ᵥ z = (-1 : ZMod p) • z}) :
    modMat p (weylMatrix (w * w)) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  let N : Matrix (Fin τ.rank) (Fin τ.rank) (ZMod p) := modMat p (weylMatrix w)
  let B : Matrix (Fin τ.rank) (Fin τ.rank) (ZMod p) := modMat p (τ.symmetrizedCartan)
  have hBsymm : Bᵀ = B := by
    ext i j
    simp only [B, modMat, Matrix.transpose_apply, Matrix.map_apply]
    exact congrArg (fun x : ℤ => (x : ZMod p)) (symmetrizedCartan_symm τ j i)
  have hdetC : τ.symmetrizedCartan.det = 2 ∨ τ.symmetrizedCartan.det = 1 := by
    rcases hτ with rfl | rfl
    · left; simpa [Tag.symmetrizedCartan, Tag.symmetrizer] using det_cartan_E7
    · right; simpa [Tag.symmetrizedCartan, Tag.symmetrizer] using det_cartan_E8
  have hBdet : B.det ≠ 0 := by
    have hmap : B.det = ((τ.symmetrizedCartan.det : ℤ) : ZMod p) := by
      have := (RingHom.map_det (Int.castRingHom (ZMod p)) τ.symmetrizedCartan).symm
      simpa [B, modMat] using this
    rw [hmap]
    rcases hdetC with h | h
    · rw [h]
      intro hzero
      have hp2dvd : p ∣ 2 := by
        rw [← Int.natCast_dvd_natCast]
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd (2 : ℤ) p).mp hzero
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2dvd)
    · rw [h]
      intro hz
      have hp1dvd : p ∣ 1 := by
        have hz' := (ZMod.intCast_zmod_eq_zero_iff_dvd (1 : ℤ) p).mp hz
        exact_mod_cast hz'
      exact hp.not_dvd_one hp1dvd
  have hiso : Nᵀ * B * N = B := by
    have hZ := weylMatrix_transpose_mul_symmetrizedCartan_mul w
    have hmap := congrArg (fun M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ =>
      M.map (Int.castRingHom (ZMod p))) hZ
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map] at hmap
    simpa [N, B, modMat, mul_assoc] using hmap
  have hrank : (N + 1).rank ≤ 1 := by
    apply rank_add_one_le_one_of_card_eigenspace (K := ZMod p) (n := τ.rank)
    rw [Nat.card_zmod]
    exact hge
  have hgoal : modMat p (weylMatrix (w * w)) = N * N := by
    rw [weylMatrix_mul]
    simp only [N, modMat, Matrix.map_mul]
  rw [hgoal]
  exact matrix_mul_self_eq_one_of_isometry_rank_le_one B N hBsymm hBdet hiso hrank

end Mod

end ExcFramesHalf

end CFSG.StandardType

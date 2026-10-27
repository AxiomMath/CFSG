module

public import CFSG.RankThree.PartOne.SEITZU49.FourData
public import CFSG.RankThree.PartOne.SEITZU49.Stmt

public section

namespace CFSG.RankThree.PartOne.SEITZU49.Four

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
open CFSG.RankThree.PartOne.CTP.U5Four
open CFSG.RankThree.PartOne.CTP.U5Gen (dgSU mat Cset tv_congr)
open CFSG.RankThree.PartOne.SEITZU49.Frame (shiftZ)

section Val

variable {K : Type} [Field K] [CharP K 2] {ω : K}

theorem valMat_gsq (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) (A : M5) :
    valMat ω (gsq A) = valMat ω A * valMat ω A := valMat_gmm hω A A

theorem valMat_gsq_pow (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) {A : M5}
    {X : Matrix (Fin 5) (Fin 5) K} {n : ℕ} (h : valMat ω A = X ^ n) :
    valMat ω (gsq A) = X ^ (2 * n) := by
  rw [valMat_gsq hω, h, ← pow_add]
  congr 1
  omega

theorem valMat_U41 (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) :
    valMat ω U41 = valMat ω Ug ^ 41 := by
  generalize hV : valMat ω Ug = V
  have h1 : valMat ω Ug = V ^ 1 := by rw [hV, pow_one]
  have h2 := valMat_gsq_pow hω h1
  have h4 := valMat_gsq_pow hω h2
  have h8 := valMat_gsq_pow hω h4
  have h16 := valMat_gsq_pow hω h8
  have h32 := valMat_gsq_pow hω h16
  rw [U41, valMat_gmm hω, valMat_gmm hω, h32, h8, h1, ← pow_add, ← pow_add]

end Val

section Group

variable {K : Type} [Field K] [Finite K] [CharP K 2] {ω : K}

local notation "σ₄" => unitaryInvolution K 2 2

theorem hunit_Ug (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) :
    conjTr σ₄ (valMat ω Ug) * valMat ω Ug = 1 := by
  rw [← valMat_gconjT hω σ₄ (sigma_omega ω), ← valMat_gmm hω, check_Ug_unitary, valMat_I5]

theorem det_Ug (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) : (valMat ω Ug).det = 1 := by
  have h5 : σ₄ (valMat ω Ug).det * (valMat ω Ug).det = 1 :=
    Eich.norm_det_of_conjTr σ₄ (hunit_Ug hω)
  rw [sigma_apply] at h5
  have h41 : (valMat ω Ug).det ^ 41 = 1 := by
    rw [← Matrix.det_pow, ← valMat_U41 hω, check_Ug_order, valMat_I5, Matrix.det_one]
  have e : (valMat ω Ug).det ^ 41 = (valMat ω Ug).det * ((valMat ω Ug).det ^ 4 *
      (valMat ω Ug).det) ^ 8 := by ring
  rw [e, h5, one_pow, mul_one] at h41
  exact h41

@[expose] noncomputable def uEl (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) : SUid σ₄ 5 :=
  mkSU σ₄ (valMat ω Ug) (det_Ug hω) (Eich.isom_of_conjTr σ₄ (hunit_Ug hω))

theorem mat_uEl (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) : mat σ₄ (uEl hω) = valMat ω Ug := rfl

theorem mat_inv' (x : SUid σ₄ 5) : mat σ₄ x⁻¹ = conjTr σ₄ (mat σ₄ x) := by
  have h1 : conjTr σ₄ (mat σ₄ x) * mat σ₄ x = 1 := x.2.2
  have h2 : mat σ₄ x * mat σ₄ x⁻¹ = 1 := by
    rw [← CFSG.RankThree.PartOne.CTP.U5Gen.mat_mul, mul_inv_cancel]
    rfl
  calc mat σ₄ x⁻¹ = (conjTr σ₄ (mat σ₄ x) * mat σ₄ x) * mat σ₄ x⁻¹ := by rw [h1, Matrix.one_mul]
    _ = conjTr σ₄ (mat σ₄ x) * (mat σ₄ x * mat σ₄ x⁻¹) := by rw [Matrix.mul_assoc]
    _ = conjTr σ₄ (mat σ₄ x) := by rw [h2, Matrix.mul_one]

@[expose] noncomputable def letEl (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) :
    Fin 10 → SUid σ₄ 5 := ![
  dgW hω (dE 0) (dE_sum 0), dgW hω (dE 1) (dE_sum 1), dgW hω (dE 2) (dE_sum 2),
  dgW hω (dE 3) (dE_sum 3), uEl hω,
  dgW hω (dEinv 0) (dEinv_sum 0), dgW hω (dEinv 1) (dEinv_sum 1), dgW hω (dEinv 2) (dEinv_sum 2),
  dgW hω (dEinv 3) (dEinv_sum 3), (uEl hω)⁻¹]

theorem mat_letEl (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) (k : Fin 10) :
    mat σ₄ (letEl hω k) = valMat ω (letG k) := by
  fin_cases k
  · show mat σ₄ (dgW hω (dE 0) (dE_sum 0)) = valMat ω (diagG (dE 0))
    rw [mat_dgW, valMat_diagG hω]
  · show mat σ₄ (dgW hω (dE 1) (dE_sum 1)) = valMat ω (diagG (dE 1))
    rw [mat_dgW, valMat_diagG hω]
  · show mat σ₄ (dgW hω (dE 2) (dE_sum 2)) = valMat ω (diagG (dE 2))
    rw [mat_dgW, valMat_diagG hω]
  · show mat σ₄ (dgW hω (dE 3) (dE_sum 3)) = valMat ω (diagG (dE 3))
    rw [mat_dgW, valMat_diagG hω]
  · show mat σ₄ (uEl hω) = valMat ω Ug
    rfl
  · show mat σ₄ (dgW hω (dEinv 0) (dEinv_sum 0)) = valMat ω (diagG (dEinv 0))
    rw [mat_dgW, valMat_diagG hω]
  · show mat σ₄ (dgW hω (dEinv 1) (dEinv_sum 1)) = valMat ω (diagG (dEinv 1))
    rw [mat_dgW, valMat_diagG hω]
  · show mat σ₄ (dgW hω (dEinv 2) (dEinv_sum 2)) = valMat ω (diagG (dEinv 2))
    rw [mat_dgW, valMat_diagG hω]
  · show mat σ₄ (dgW hω (dEinv 3) (dEinv_sum 3)) = valMat ω (diagG (dEinv 3))
    rw [mat_dgW, valMat_diagG hω]
  · show mat σ₄ ((uEl hω)⁻¹) = valMat ω (gconjT Ug)
    rw [mat_inv', mat_uEl, valMat_gconjT hω σ₄ (sigma_omega ω)]

theorem letEl_mem (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) {hz : σ₄ ω * ω = 1}
    {M : Subgroup (SUid σ₄ 5)} (hM : GenHyp σ₄ ω hz M) (k : Fin 10) : letEl hω k ∈ M := by
  have hu : uEl hω ∈ M := by
    refine hM.cent _ ?_
    rw [mat_uEl]
    have e : valMat ω Sgz = shiftZ ω := by
      rw [Sgz, valMat_gmm hω, valMat_Sg, valMat_diagG hω, shiftZ]
      congr 2
      funext i
      fin_cases i <;> simp
    rw [← e, ← valMat_gmm hω, ← valMat_gmm hω, check_Ug_comm]
  have hD : ∀ (e : Fin 5 → ℕ) (he : (∑ i, e i) % 5 = 0), dgW hω e he ∈ M := fun e he =>
    hM.diag _ _ _
  fin_cases k
  · exact hD (dE 0) (dE_sum 0)
  · exact hD (dE 1) (dE_sum 1)
  · exact hD (dE 2) (dE_sum 2)
  · exact hD (dE 3) (dE_sum 3)
  · exact hu
  · exact hD (dEinv 0) (dEinv_sum 0)
  · exact hD (dEinv 1) (dEinv_sum 1)
  · exact hD (dEinv 2) (dEinv_sum 2)
  · exact hD (dEinv 3) (dEinv_sum 3)
  · exact M.inv_mem hu

@[expose] noncomputable def wordEl (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) (w : List (Fin 10)) :
    SUid σ₄ 5 :=
  w.foldl (fun B k => B * letEl hω k) 1

theorem mat_foldl (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) (w : List (Fin 10))
    (acc : SUid σ₄ 5) (A : M5) (h : mat σ₄ acc = valMat ω A) :
    mat σ₄ (w.foldl (fun B k => B * letEl hω k) acc) =
      valMat ω (w.foldl (fun B k => gmm B (letG k)) A) := by
  induction w generalizing acc A with
  | nil => simpa using h
  | cons k w ih =>
    simp only [List.foldl_cons]
    refine ih _ _ ?_
    rw [CFSG.RankThree.PartOne.CTP.U5Gen.mat_mul, h, mat_letEl hω, valMat_gmm hω]

theorem mat_wordEl (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) (w : List (Fin 10)) :
    mat σ₄ (wordEl hω w) = valMat ω (evalLW w) := by
  refine mat_foldl hω w 1 I5 ?_
  rw [valMat_I5]
  rfl

theorem wordEl_mem (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) {M : Subgroup (SUid σ₄ 5)}
    (hL : ∀ k, letEl hω k ∈ M) (w : List (Fin 10)) : wordEl hω w ∈ M := by
  suffices H : ∀ (w : List (Fin 10)) (acc : SUid σ₄ 5), acc ∈ M →
      w.foldl (fun B k => B * letEl hω k) acc ∈ M from H w 1 M.one_mem
  intro w
  induction w with
  | nil => intro acc hacc; exact hacc
  | cons k w ih => intro acc hacc; exact ih _ (M.mul_mem hacc (hL k))

@[expose] noncomputable def sqEl (x : SUid σ₄ 5) : SUid σ₄ 5 := x * x

theorem mat_sqEl (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) {x : SUid σ₄ 5} {A : M5}
    (h : mat σ₄ x = valMat ω A) : mat σ₄ (sqEl x) = valMat ω (gsq A) := by
  rw [sqEl, CFSG.RankThree.PartOne.CTP.U5Gen.mat_mul, h, valMat_gsq hω]

@[expose] noncomputable def Tel (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) : SUid σ₄ 5 :=
  sqEl (sqEl (sqEl (sqEl (sqEl (sqEl (wordEl hω wT)))))) * wordEl hω wT

theorem mat_Tel (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) : mat σ₄ (Tel hω) = valMat ω Tg := by
  have h1 := mat_wordEl hω wT
  have h2 := mat_sqEl hω (mat_sqEl hω (mat_sqEl hω (mat_sqEl hω (mat_sqEl hω
    (mat_sqEl hω h1)))))
  rw [Tel, CFSG.RankThree.PartOne.CTP.U5Gen.mat_mul, h2, h1, Tg, valMat_gmm hω]

theorem Tel_mem (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) {M : Subgroup (SUid σ₄ 5)}
    (hL : ∀ k, letEl hω k ∈ M) : Tel hω ∈ M := by
  have hg := wordEl_mem hω hL wT
  have hs : ∀ x ∈ M, sqEl x ∈ M := fun x hx => M.mul_mem hx hx
  exact M.mul_mem (hs _ (hs _ (hs _ (hs _ (hs _ (hs _ hg)))))) hg

@[expose] noncomputable def P1el (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) : SUid σ₄ 5 :=
  wordEl hω h1 * Tel hω * wordEl hω hinv1

@[expose] noncomputable def P2el (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) : SUid σ₄ 5 :=
  wordEl hω h2 * Tel hω * wordEl hω hinv2

theorem mat_P1el (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) :
    mat σ₄ (P1el hω) = valMat ω P1 := by
  rw [P1el, CFSG.RankThree.PartOne.CTP.U5Gen.mat_mul, CFSG.RankThree.PartOne.CTP.U5Gen.mat_mul,
    mat_wordEl hω, mat_wordEl hω, mat_Tel hω, P1, valMat_gmm hω, valMat_gmm hω]

theorem mat_P2el (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) :
    mat σ₄ (P2el hω) = valMat ω P2 := by
  rw [P2el, CFSG.RankThree.PartOne.CTP.U5Gen.mat_mul, CFSG.RankThree.PartOne.CTP.U5Gen.mat_mul,
    mat_wordEl hω, mat_wordEl hω, mat_Tel hω, P2, valMat_gmm hω, valMat_gmm hω]

@[expose] def Yk (ω : K) : Fin 5 → K := fun i => val ω (Yg i)

theorem Yk_eq (ω : K) :
    Yk ω = ![0, val ω ![1, 0, 1, 1], val ω ![1, 0, 1, 1], 1, 1] := by
  funext i
  fin_cases i <;> simp [Yk, Yg, val_eq]

theorem herm_Yk (ω : K) : herm σ₄ (Yk ω) (Yk ω) = 0 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [Yk_eq]
  simp only [herm, Fin.sum_univ_five]
  show σ₄ 0 * 0 + σ₄ (val ω ![1, 0, 1, 1]) * val ω ![1, 0, 1, 1] +
    σ₄ (val ω ![1, 0, 1, 1]) * val ω ![1, 0, 1, 1] + σ₄ 1 * 1 + σ₄ 1 * 1 = 0
  rw [map_zero, map_one]
  linear_combination (σ₄ (val ω ![1, 0, 1, 1]) * val ω ![1, 0, 1, 1] + 1) * h2

theorem valMat_tvYG (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) (c : G16) :
    valMat ω (tvYG c) = tvMat σ₄ (Yk ω) (val ω c) := by
  ext i j
  have h1 : val ω (I5 i j) = (1 : Matrix (Fin 5) (Fin 5) K) i j := by
    have := congrFun (congrFun (valMat_I5 (ω := ω)) i) j
    simpa [valMat] using this
  simp only [valMat, tvYG, YYg, Matrix.of_apply, val_add, val_gmul hω,
    val_gconj hω σ₄ (sigma_omega ω), h1, tvMat, Matrix.add_apply, Matrix.smul_apply,
    vecMulVec_apply, smul_eq_mul, Yk]

theorem tv_mem_of_mat (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) {M : Subgroup (SUid σ₄ 5)}
    (hσ : ∀ c, σ₄ (σ₄ c) = c) {g : SUid σ₄ 5} (hg : g ∈ M) {c : G16}
    (hc : val ω c + σ₄ (val ω c) = 0) (hmat : mat σ₄ g = valMat ω (tvYG c)) :
    tv hσ (herm_Yk ω) hc ∈ M := by
  have : tv hσ (herm_Yk ω) hc = g := by
    apply Subtype.ext
    apply Units.ext
    show mat σ₄ (tv hσ (herm_Yk ω) hc) = mat σ₄ g
    rw [hmat, valMat_tvYG hω]
    rfl
  rw [this]
  exact hg

theorem norm_val_one (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) :
    val ω ![1, 0, 0, 0] + σ₄ (val ω ![1, 0, 0, 0]) = 0 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have e : val ω ![1, 0, 0, 0] = 1 := by simp [val_eq]
  rw [e, map_one]
  linear_combination h2

theorem val_c1_sq (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) :
    val ω ![1, 0, 1, 1] ^ 2 + val ω ![1, 0, 1, 1] + 1 = 0 := by
  have h := congrArg (val ω) check_c1_sq
  rw [val_add, val_add, val_gmul hω] at h
  have e1 : val ω ![1, 0, 0, 0] = 1 := by simp [val_eq]
  have e0 : val ω (0 : G16) = 0 := map_zero (valHom ω)
  rw [e1, e0] at h
  linear_combination h

theorem Yk_mem_Cset (hK : Nat.card K = (2 ^ 2) ^ 2)
    (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) {hz : σ₄ ω * ω = 1} {M : Subgroup (SUid σ₄ 5)}
    (hM : GenHyp σ₄ ω hz M) : Yk ω ∈ Cset (unitaryInvolution_involutive hK) M := by
  have h20 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hσ : ∀ c : K, σ₄ (σ₄ c) = c := unitaryInvolution_involutive hK
  have hL : ∀ k, letEl hω k ∈ M := letEl_mem hω hM
  have hc₁ : val ω ![1, 0, 1, 1] + σ₄ (val ω ![1, 0, 1, 1]) = 0 :=
    val_norm_fixed hω _ check_c1_conj
  have hc₂ := norm_val_one hω
  have hP1 : P1el hω ∈ M :=
    M.mul_mem (M.mul_mem (wordEl_mem hω hL h1) (Tel_mem hω hL)) (wordEl_mem hω hL hinv1)
  have hP2 : P2el hω ∈ M :=
    M.mul_mem (M.mul_mem (wordEl_mem hω hL h2) (Tel_mem hω hL)) (wordEl_mem hω hL hinv2)
  have hm1 : mat σ₄ (P1el hω) = valMat ω (tvYG ![1, 0, 1, 1]) := by rw [mat_P1el hω, check_P1]
  have hm2 : mat σ₄ (P2el hω) = valMat ω (tvYG ![1, 0, 0, 0]) := by rw [mat_P2el hω, check_P2]
  have ht₁ : tv hσ (herm_Yk ω) hc₁ ∈ M := tv_mem_of_mat hω hσ hP1 hc₁ hm1
  have ht₂ : tv hσ (herm_Yk ω) hc₂ ∈ M := tv_mem_of_mat hω hσ hP2 hc₂ hm2
  have e1 : val ω ![1, 0, 0, 0] = 1 := by simp [val_eq]
  have hw2 := val_c1_sq hω
  have hs : val ω ![1, 0, 1, 1] + (val ω ![1, 0, 1, 1] + 1) = 1 := by
    linear_combination (val ω ![1, 0, 1, 1]) * h20
  have hp : val ω ![1, 0, 1, 1] * (val ω ![1, 0, 1, 1] + 1) = 1 := by
    linear_combination hw2 - h20
  refine ⟨herm_Yk ω, fun c hc => ?_⟩
  have hc4 : c + c ^ 4 = 0 := by rwa [sigma_apply] at hc
  rcases four_roots h20 hs hp hc4 with rfl | rfl | rfl | rfl
  · rw [tv_zero hσ (herm_Yk ω) hc]
    exact M.one_mem
  · rw [tv_congr σ₄ hσ (herm_Yk ω) e1.symm hc hc₂]
    exact ht₂
  · exact ht₁
  · have hcd : (val ω ![1, 0, 1, 1] + val ω ![1, 0, 0, 0]) +
        σ₄ (val ω ![1, 0, 1, 1] + val ω ![1, 0, 0, 0]) = 0 := by
      rw [map_add, e1, map_one]
      linear_combination hc₁ + h20
    rw [tv_congr σ₄ hσ (herm_Yk ω) (show val ω ![1, 0, 1, 1] + 1 =
      val ω ![1, 0, 1, 1] + val ω ![1, 0, 0, 0] by rw [e1]) hc hcd,
      ← tv_mul_tv hσ (herm_Yk ω) hc₁ hc₂ hcd]
    exact M.mul_mem ht₁ ht₂

end Group

end CFSG.RankThree.PartOne.SEITZU49.Four

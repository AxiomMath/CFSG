module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res8ProofSLTwoMain
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction
import CFSG.RankThree.PartTwo.Sec14.Item148Res8ProofLinRoot

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148Res8

open Matrix

variable {K : Type} [Field K]

@[expose] def blkMat (A : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1]

theorem blkMat_mul (A B : Matrix (Fin 2) (Fin 2) K) : blkMat (A * B) = blkMat A * blkMat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem blkMat_one : blkMat (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkMat]

theorem det_blkMat (A : Matrix (Fin 2) (Fin 2) K) : (blkMat A).det = A.det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [blkMat]

@[expose] def blkSL : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 3) K where
  toFun A := ⟨blkMat (A : Matrix (Fin 2) (Fin 2) K), (det_blkMat _).trans A.2⟩
  map_one' := Subtype.ext blkMat_one
  map_mul' A B := Subtype.ext (blkMat_mul (A : Matrix (Fin 2) (Fin 2) K) B)

@[expose] noncomputable def conjSL (g : GL (Fin 3) K) :
    SpecialLinearGroup (Fin 3) K →* SpecialLinearGroup (Fin 3) K :=
  (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K g).toMonoidHom

theorem coe_conjSL (g : GL (Fin 3) K) (A : SpecialLinearGroup (Fin 3) K) :
    ((conjSL g A : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (g : Matrix (Fin 3) (Fin 3) K) * A * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
  CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix 3 K g A

theorem det_one_add_smul_vecMulVec (b : K) (v φ : Fin 3 → K) :
    (1 + b • vecMulVec v φ).det = 1 + b * (φ ⬝ᵥ v) := by
  rw [Matrix.det_fin_three]
  simp [vecMulVec_apply, dotProduct, Fin.sum_univ_three]
  ring

theorem exists_map_eq_one_add (F₀ : Subfield K) (w ψ : Fin 3 → F₀) (hψw : ψ ⬝ᵥ w = 0) (b : F₀) :
    ∃ A : SpecialLinearGroup (Fin 3) F₀,
      ((SpecialLinearGroup.map F₀.subtype A : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) =
        1 + (b : K) • vecMulVec (fun r => (w r : K)) (fun c => (ψ c : K)) := by
  let A : SpecialLinearGroup (Fin 3) F₀ :=
    ⟨1 + b • vecMulVec w ψ, by rw [det_one_add_smul_vecMulVec, hψw, mul_zero, add_zero]⟩
  refine ⟨A, ?_⟩
  show F₀.subtype.mapMatrix (1 + b • vecMulVec w ψ) = _
  rw [RingHom.mapMatrix_apply]
  ext r c
  simp [Matrix.one_apply, vecMulVec_apply]
  split_ifs <;> simp

theorem single_one_eq_vecMulVec {n : ℕ} (i j : Fin n) :
    single i j (1 : K) = vecMulVec (Pi.single i 1) (Pi.single j 1) := by
  ext r c
  simp only [Matrix.single_apply, vecMulVec_apply, Pi.single_apply]
  by_cases hr : r = i
  · subst hr
    by_cases hc : c = j
    · subst hc; simp
    · simp [hc, Ne.symm hc]
  · simp [hr, Ne.symm hr]

theorem mul_single_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    A * single i j (1 : K) * B = vecMulVec (A.col i) (B.row j) := by
  rw [single_one_eq_vecMulVec, mul_vecMulVec, vecMulVec_mul, mulVec_single_one,
    single_one_vecMul]

@[expose] noncomputable def rankOneSL (v φ : Fin 3 → K) (h : φ ⬝ᵥ v = 0) (c : K) :
    SpecialLinearGroup (Fin 3) K :=
  ⟨1 + c • vecMulVec v φ, by rw [det_one_add_smul_vecMulVec, h, mul_zero, add_zero]⟩

theorem coe_rankOneSL (v φ : Fin 3 → K) (h : φ ⬝ᵥ v = 0) (c : K) :
    ((rankOneSL v φ h c : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      1 + c • vecMulVec v φ :=
  rfl

section Conj

variable [Finite K] [CharP K 2]

theorem rootPair_pow (F₀ : Subfield K) {n : ℕ} (hn : 2 ≤ n)
    (hF₀ : Nat.card F₀ = 2 ^ n) {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (H : Subgroup (SpecialLinearGroup (Fin 3) K)) {v₀ φ₀ v₂ φ₂ : Fin 3 → K}
    (h₀ : φ₀ ⬝ᵥ v₀ = 0) (h₂ : φ₂ ⬝ᵥ v₂ = 0)
    (hT₀mem : ∀ a ∈ F₀, rankOneSL v₀ φ₀ h₀ a ∈ H)
    (hT₀S : ∀ c, rankOneSL v₀ φ₀ h₀ c ∈ H → c ∈ F₀)
    (hT₂mem : ∀ b ∈ F₀, rankOneSL v₂ φ₂ h₂ b ∈ H)
    {h : SpecialLinearGroup (Fin 3) K} (hh : h ∈ H) :
    (((φ₀ ᵥ* ((h⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ⬝ᵥ v₂) *
        (φ₂ ⬝ᵥ ((h : Matrix (Fin 3) (Fin 3) K) *ᵥ v₀))) ^ (2 ^ (2 * n)) =
      ((φ₀ ᵥ* ((h⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ⬝ᵥ v₂) *
        (φ₂ ⬝ᵥ ((h : Matrix (Fin 3) (Fin 3) K) *ᵥ v₀)) := by
  set hM := (h : Matrix (Fin 3) (Fin 3) K) with hhM
  set hiM := ((h⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hhiM
  set v₁ : Fin 3 → K := hM *ᵥ v₀ with hv₁
  set φ₁ : Fin 3 → K := φ₀ ᵥ* hiM with hφ₁
  have hpos : 2 ^ (2 * n) ≠ 0 := by positivity
  by_cases hlam : φ₁ ⬝ᵥ v₂ = 0
  · rw [hlam, zero_mul, zero_pow hpos]
  by_cases hmu : φ₂ ⬝ᵥ v₁ = 0
  · rw [hmu, mul_zero, zero_pow hpos]
  set lam := φ₁ ⬝ᵥ v₂ with hlam'
  set mu := φ₂ ⬝ᵥ v₁ with hmu'
  have hhi : hiM * hM = 1 := by
    have : ((h⁻¹ * h : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [inv_mul_cancel]; rfl
    exact this
  have hih : hM * hiM = 1 := by
    have : ((h * h⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [mul_inv_cancel]; rfl
    exact this
  set N := vecMulVec v₁ φ₁ with hN
  have hNh : hM * vecMulVec v₀ φ₀ * hiM = N := by
    rw [mul_vecMulVec, vecMulVec_mul]
  have hφ₁v₁ : φ₁ ⬝ᵥ v₁ = 0 := by
    rw [hφ₁, hv₁, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hhi, Matrix.vecMul_one, h₀]
  set s := crossProduct φ₁ φ₂ with hs
  have hφ₁s : φ₁ ⬝ᵥ s = 0 := dot_self_cross φ₁ φ₂
  have hφ₂s : φ₂ ⬝ᵥ s = 0 := dot_cross_self φ₁ φ₂
  set g₀ : Matrix (Fin 3) (Fin 3) K := (Matrix.of ![v₁, v₂, s])ᵀ with hg₀
  have hdet : g₀.det ≠ 0 := by
    rw [hg₀, Matrix.det_transpose]
    have e1 : (Matrix.of ![v₁, v₂, s]).det = v₁ ⬝ᵥ crossProduct v₂ s :=
      (triple_product_eq_det v₁ v₂ s).symm
    rw [e1, triple_product_permutation, triple_product_permutation, dotProduct_comm, hs,
      cross_dot_cross, dotProduct_comm v₁ φ₁, dotProduct_comm v₂ φ₂, dotProduct_comm v₁ φ₂,
      dotProduct_comm v₂ φ₁, hφ₁v₁, h₂, zero_mul, zero_sub, neg_ne_zero]
    exact mul_ne_zero hmu hlam
  set g : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero g₀ hdet with hg
  have hgM : (g : Matrix (Fin 3) (Fin 3) K) = g₀ := rfl
  have hgg : g₀ * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← hgM, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hcol0 : g₀.col 0 = v₁ := by
    ext r; simp [hg₀, Matrix.col_apply]
  have hcol1 : g₀.col 1 = v₂ := by
    ext r; simp [hg₀, Matrix.col_apply]
  have hrow : ∀ φ : Fin 3 → K, φ ᵥ* g₀ = ![v₁ ⬝ᵥ φ, v₂ ⬝ᵥ φ, s ⬝ᵥ φ] := by
    intro φ
    rw [hg₀, Matrix.vecMul_transpose]
    ext c
    fin_cases c <;> simp [Matrix.mulVec]
  set M := vecMulVec v₂ φ₂ with hMdef
  have hI1 : N * g₀ = lam • (g₀ * single 0 1 (1 : K)) := by
    rw [hN, vecMulVec_mul, hrow, single_one_eq_vecMulVec, mul_vecMulVec, mulVec_single_one, hcol0,
      ← vecMulVec_smul]
    congr 1
    ext c
    fin_cases c
    · simp [dotProduct_comm v₁ φ₁, hφ₁v₁]
    · simp [dotProduct_comm v₂ φ₁, hlam']
    · simp [dotProduct_comm s φ₁, hφ₁s]
  have hI2 : M * g₀ = mu • (g₀ * single 1 0 (1 : K)) := by
    rw [hMdef, vecMulVec_mul, hrow, single_one_eq_vecMulVec, mul_vecMulVec, mulVec_single_one,
      hcol1, ← vecMulVec_smul]
    congr 1
    ext c
    fin_cases c
    · simp [dotProduct_comm v₁ φ₂, hmu']
    · simp [dotProduct_comm v₂ φ₂, h₂]
    · simp [dotProduct_comm s φ₂, hφ₂s]
  have hconj1 : g₀ * single 0 1 (1 : K) * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      lam⁻¹ • N := by
    have e : N = N * g₀ * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [Matrix.mul_assoc, hgg, Matrix.mul_one]
    rw [e, hI1, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hlam, one_smul]
  have hconj2 : g₀ * single 1 0 (1 : K) * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      mu⁻¹ • M := by
    have e : M = M * g₀ * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [Matrix.mul_assoc, hgg, Matrix.mul_one]
    rw [e, hI2, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hmu, one_smul]
  set θ := (conjSL g).comp blkSL with hθ
  set G := H.comap θ with hG
  have hθ_coe : ∀ A : SpecialLinearGroup (Fin 2) K,
      ((θ A : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        g₀ * blkMat (A : Matrix (Fin 2) (Fin 2) K) *
          ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    fun A => coe_conjSL g (blkSL A)
  have hblk_u : ∀ x : K, blkMat ((uSL x : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = 1 + x • single 0 1 (1 : K) := by
    intro x
    rw [uSL_coe]
    ext r c
    fin_cases r <;> fin_cases c <;> simp [blkMat]
  have hblk_l : ∀ y : K, blkMat ((lSL y : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = 1 + y • single 1 0 (1 : K) := by
    intro y
    rw [lSL_coe]
    ext r c
    fin_cases r <;> fin_cases c <;> simp [blkMat]
  have hθu : ∀ x : K, θ (uSL x) = h * rankOneSL v₀ φ₀ h₀ (x * lam⁻¹) * h⁻¹ := by
    intro x
    apply Subtype.ext
    have e2 : ((h * rankOneSL v₀ φ₀ h₀ (x * lam⁻¹) * h⁻¹ :
        SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        hM * (1 + (x * lam⁻¹) • vecMulVec v₀ φ₀) * hiM := rfl
    calc ((θ (uSL x) : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          g₀ * (1 + x • single 0 1 (1 : K)) *
            ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          rw [hθ_coe, hblk_u]
      _ = 1 + (x * lam⁻¹) • N := by
          rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hgg, Matrix.mul_smul,
            Matrix.smul_mul, hconj1, smul_smul]
      _ = hM * (1 + (x * lam⁻¹) • vecMulVec v₀ φ₀) * hiM := by
          rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hih, Matrix.mul_smul,
            Matrix.smul_mul, hNh]
      _ = _ := e2.symm
  have hθl : ∀ y : K, ((θ (lSL y) : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = 1 + (y * mu⁻¹) • M := by
    intro y
    rw [hθ_coe, hblk_l, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hgg, Matrix.mul_smul,
      Matrix.smul_mul, hconj2, smul_smul]
  have hu : ∀ a ∈ F₀, uSL (lam * a) ∈ G := by
    intro a ha
    show θ (uSL (lam * a)) ∈ H
    rw [hθu, mul_comm lam a, mul_inv_cancel_right₀ hlam]
    exact H.mul_mem (H.mul_mem hh (hT₀mem a ha)) (H.inv_mem hh)
  have hl : ∀ b ∈ F₀, lSL (mu * b) ∈ G := by
    intro b hb
    show θ (lSL (mu * b)) ∈ H
    have : θ (lSL (mu * b)) = rankOneSL v₂ φ₂ h₂ b := by
      apply Subtype.ext
      rw [hθl, mul_comm mu b, mul_inv_cancel_right₀ hmu]
      rfl
    rw [this]
    exact hT₂mem b hb
  have hU : ∀ x, uSL x ∈ G → ∃ a ∈ F₀, x = lam * a := by
    intro x hx
    have hx' : θ (uSL x) ∈ H := hx
    rw [hθu] at hx'
    have hmem : rankOneSL v₀ φ₀ h₀ (x * lam⁻¹) ∈ H := by
      have := H.mul_mem (H.mul_mem (H.inv_mem hh) hx') hh
      simpa [mul_assoc] using this
    refine ⟨x * lam⁻¹, hT₀S _ hmem, ?_⟩
    field_simp
  exact mul_pow_of_rootGroups F₀ hn hF₀ hf hK hlam hmu G hu hl hU

theorem dot_mul_dot_mem (F₀ : Subfield K) {n : ℕ} (hn : 2 ≤ n)
    (hF₀ : Nat.card F₀ = 2 ^ n) (hK : Nat.card K = 2 ^ (3 * n))
    (H : Subgroup (SpecialLinearGroup (Fin 3) K))
    (hι : (SpecialLinearGroup.map F₀.subtype).range ≤ H) {i j : Fin 3} (hij : i ≠ j)
    (hS : ∀ a : K, SpecialLinearGroup.transvection hij a ∈ H → a ∈ F₀)
    {h : SpecialLinearGroup (Fin 3) K} (hh : h ∈ H) (w ψ : Fin 3 → F₀) (hψw : ψ ⬝ᵥ w = 0) :
    (((h⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).row j ⬝ᵥ
        (fun r => (w r : K))) *
      ((fun c => (ψ c : K)) ⬝ᵥ (h : Matrix (Fin 3) (Fin 3) K).col i) ∈ F₀ := by
  have h₀ : (Pi.single j (1 : K) : Fin 3 → K) ⬝ᵥ Pi.single i 1 = 0 := by
    rw [single_dotProduct, one_mul, Pi.single_eq_of_ne hij.symm]
  have h₂ : (fun c => (ψ c : K)) ⬝ᵥ (fun r => (w r : K)) = 0 := by
    have := congrArg (Subtype.val : F₀ → K) hψw
    simpa [dotProduct] using this
  have htr : ∀ c : K, rankOneSL (Pi.single i 1) (Pi.single j 1) h₀ c =
      SpecialLinearGroup.transvection hij c := by
    intro c
    apply Subtype.ext
    rw [coe_rankOneSL, SpecialLinearGroup.transvection_coe, ← single_one_eq_vecMulVec,
      Matrix.smul_single, smul_eq_mul, mul_one]
  have key := rootPair_pow F₀ hn hF₀ (by omega) hK H h₀ h₂
    (fun a ha => by
      rw [htr]
      exact hι ⟨SpecialLinearGroup.transvection hij ⟨a, ha⟩, map_subtype_transvection F₀ hij
        ⟨a, ha⟩⟩)
    (fun c hc => hS c (by rwa [htr] at hc))
    (fun b hb => by
      obtain ⟨A, hA⟩ := exists_map_eq_one_add F₀ w ψ hψw ⟨b, hb⟩
      have : rankOneSL (fun r => (w r : K)) (fun c => (ψ c : K)) h₂ b =
          SpecialLinearGroup.map F₀.subtype A := by
        apply Subtype.ext
        rw [hA]
        rfl
      rw [this]
      exact hι ⟨A, rfl⟩) hh
  rw [mulVec_single_one, single_one_vecMul] at key
  set x := (((h⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).row j ⬝ᵥ
      (fun r => (w r : K))) * ((fun c => (ψ c : K)) ⬝ᵥ (h : Matrix (Fin 3) (Fin 3) K).col i)
    with hx
  have hq3 : x ^ (2 ^ (3 * n)) = x := by
    have := Fintype.ofFinite K
    rw [← hK, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card _
  have hqq : x ^ (2 ^ n) = x := by
    have e : 2 ^ (3 * n) = 2 ^ (2 * n) * 2 ^ n := by rw [← pow_add]; ring_nf
    rw [e, pow_mul, key] at hq3
    exact hq3
  exact mem_of_pow_eq_self F₀ hF₀ (Nat.one_lt_two_pow (by omega)) hqq

end Conj

end CFSG.RankThree.PartTwo.Sec14.Item148Res8

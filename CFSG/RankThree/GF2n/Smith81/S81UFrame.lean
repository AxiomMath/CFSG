module

public import CFSG.RankThree.GF2n.Smith81.S81UModel
public import CFSG.RankThree.GF2n.Smith81.S81BNLine
public import CFSG.LieType.Universal.Unitary.Hermitian

public section

namespace CFSG.RankThree.GF2n.Smith81.U6Cube

open CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.A5Cube Matrix
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
  CFSG.RankThree.GF2n.Smith81.EGeom

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}

@[expose] def hypGram (F : Type) [Field F] : Matrix (Fin 6) (Fin 6) F :=
  Matrix.of fun i j => if i.val / 2 = j.val / 2 ∧ i.val % 2 ≠ j.val % 2 then 1 else 0

@[expose] def frameMat (σ : F ≃+* F) (ω : F) : Matrix (Fin 6) (Fin 6) F :=
  Matrix.of fun i j => if i.val / 2 = j.val / 2 then
    (if j.val % 2 = 0 then 1 else if i.val % 2 = 0 then ω else σ ω) else 0

@[expose] def frameInv (σ : F ≃+* F) (ω : F) : Matrix (Fin 6) (Fin 6) F :=
  Matrix.of fun i j => if i.val / 2 = j.val / 2 then
    (if i.val % 2 = 0 then (if j.val % 2 = 0 then σ ω else ω) else 1) else 0

theorem frameMat_mul_frameInv {ω : F} (hω : ω + σ ω = 1) :
    frameMat σ ω * frameInv σ ω = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_six, frameMat, frameInv, Matrix.one_apply,
      CharTwo.add_self_eq_zero]
  all_goals
    first
    | linear_combination hω
    | linear_combination h2
    | linear_combination (ω * σ ω) * h2
    | linear_combination ω * h2
    | linear_combination σ ω * h2

theorem frameInv_mul_frameMat {ω : F} (hω : ω + σ ω = 1) :
    frameInv σ ω * frameMat σ ω = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_six, frameMat, frameInv, Matrix.one_apply,
      CharTwo.add_self_eq_zero]
  all_goals
    first
    | linear_combination hω
    | linear_combination h2
    | linear_combination (ω * σ ω) * h2
    | linear_combination ω * h2
    | linear_combination σ ω * h2

theorem conjTr_frameMat_mul (hσ : ∀ c, σ (σ c) = c) {ω : F} (hω : ω + σ ω = 1) :
    conjTr σ (frameMat σ ω) * frameMat σ ω = hypGram F := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_six, conjTr_apply, frameMat, hypGram, hσ,
      CharTwo.add_self_eq_zero]
  all_goals
    first
    | linear_combination hω
    | linear_combination h2
    | linear_combination (ω * σ ω) * h2
    | linear_combination ω * h2
    | linear_combination σ ω * h2

@[expose] noncomputable def frameGL (σ : F ≃+* F) (ω : F) (hω : ω + σ ω = 1) : GL (Fin 6) F where
  val := frameMat σ ω
  inv := frameInv σ ω
  val_inv := frameMat_mul_frameInv hω
  inv_val := frameInv_mul_frameMat hω

theorem frameGL_val (ω : F) (hω : ω + σ ω = 1) :
    ((frameGL σ ω hω : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = frameMat σ ω := rfl

theorem frameMat_mulVec_even (ω : F) (j : Fin 3) :
    (frameMat σ ω).mulVec (Pi.single (⟨2 * j.val, by omega⟩ : Fin 6) (1 : F)) = e3uT0Vec j := by
  funext r
  have h1 : (2 * j.val) / 2 = j.val := by omega
  have h2 : (2 * j.val) % 2 = 0 := by omega
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, frameMat, e3uT0Vec, h1, h2]

theorem pt0_eq_ιMulti_T0 : pt0 F = exteriorPower.ιMulti F 3 e3uT0Vec := by
  unfold pt0
  congr 1
  funext i
  fin_cases i <;> funext r <;> fin_cases r <;> simp [e3uT0Vec, Pi.single_apply]

theorem rho_frameGL_p0 (ω : F) (hω : ω + σ ω = 1) :
    rho F (frameGL σ ω hω : GL (Fin 6) F) (p0 F) = pt0 F := by
  rw [p0_eq, rho_ιMulti, frameGL_val, pt0_eq_ιMulti_T0]
  congr 1
  funext i
  fin_cases i
  · exact frameMat_mulVec_even ω 0
  · exact frameMat_mulVec_even ω 1
  · exact frameMat_mulVec_even ω 2

private theorem frameConj_val (ĝ : GL (Fin 6) F) {ω : F} (hω : ω + σ ω = 1) :
    ((frameGL σ ω hω * ĝ * (frameGL σ ω hω)⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      frameMat σ ω * (ĝ : Matrix (Fin 6) (Fin 6) F) * frameInv σ ω := by
  rw [Units.val_mul, Units.val_mul]
  rfl

theorem frame_conj_mem_SUid (hσ : ∀ c, σ (σ c) = c) {ω : F} (hω : ω + σ ω = 1)
    {ĝ : GL (Fin 6) F} (hdet : (ĝ : Matrix (Fin 6) (Fin 6) F).det = 1)
    (hu : conjTr σ (ĝ : Matrix (Fin 6) (Fin 6) F) * hypGram F * (ĝ : Matrix (Fin 6) (Fin 6) F) =
      hypGram F) :
    frameGL σ ω hω * ĝ * (frameGL σ ω hω)⁻¹ ∈ SUid σ 6 := by
  have hS : frameMat σ ω * frameInv σ ω = 1 := frameMat_mul_frameInv hω
  have hG : conjTr σ (frameMat σ ω) * frameMat σ ω = hypGram F := conjTr_frameMat_mul hσ hω
  have hdd : (frameMat σ ω).det * (frameInv σ ω).det = 1 := by
    rw [← Matrix.det_mul, hS, Matrix.det_one]
  refine CFSG.LieType.Universal.Unitary.mem_SUid.mpr ⟨?_, ?_⟩
  · rw [frameConj_val, Matrix.det_mul, Matrix.det_mul, hdet]
    linear_combination hdd
  · rw [frameConj_val]
    calc conjTr σ (frameMat σ ω * (ĝ : Matrix (Fin 6) (Fin 6) F) * frameInv σ ω) *
          (frameMat σ ω * (ĝ : Matrix (Fin 6) (Fin 6) F) * frameInv σ ω)
        = conjTr σ (frameInv σ ω) * (conjTr σ (ĝ : Matrix (Fin 6) (Fin 6) F) *
            (conjTr σ (frameMat σ ω) * frameMat σ ω) * (ĝ : Matrix (Fin 6) (Fin 6) F)) *
            frameInv σ ω := by
          simp only [conjTr_mul, Matrix.mul_assoc]
      _ = conjTr σ (frameInv σ ω) * (conjTr σ (ĝ : Matrix (Fin 6) (Fin 6) F) * hypGram F *
            (ĝ : Matrix (Fin 6) (Fin 6) F)) * frameInv σ ω := by rw [hG]
      _ = conjTr σ (frameInv σ ω) * hypGram F * frameInv σ ω := by rw [hu]
      _ = conjTr σ (frameInv σ ω) * (conjTr σ (frameMat σ ω) * frameMat σ ω) * frameInv σ ω := by
          rw [hG]
      _ = conjTr σ (frameMat σ ω * frameInv σ ω) * (frameMat σ ω * frameInv σ ω) := by
          simp only [conjTr_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hS, conjTr_one, Matrix.one_mul]

theorem frame_conj_unip_of_mem_U0Sub (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1)
    {g : SUid σ 6} (hg : g ∈ e3uU0Sub σ) :
    (frameGL σ ω hω)⁻¹ * (g : GL (Fin 6) F) * frameGL σ ω hω ∈ UnipGL F (S0 F) := by
  have hfix : ∀ i : Fin 3, ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec i) =
      e3uT0Vec i := hg
  have hdetg : ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).det = 1 :=
    ((CFSG.ClassicalGroups.Unitary.mem_SUid_iff σ).mp g.2).1
  have hpres : ∀ (i : Fin 3) (x : Fin 6 → F),
      CFSG.ClassicalGroups.Unitary.herm σ (e3uT0Vec i)
        (((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec x) =
        CFSG.ClassicalGroups.Unitary.herm σ (e3uT0Vec i) x := by
    intro i x
    have h' : CFSG.ClassicalGroups.Unitary.herm σ (g • e3uT0Vec i) (g • x) =
        CFSG.ClassicalGroups.Unitary.herm σ (e3uT0Vec i) x :=
      CFSG.ClassicalGroups.Unitary.herm_smul_smul σ g _ _
    have h2 : g • (e3uT0Vec i : Fin 6 → F) = e3uT0Vec i := hfix i
    rw [h2] at h'
    exact h'
  have herm0 : ∀ x : Fin 6 → F,
      CFSG.ClassicalGroups.Unitary.herm σ (e3uT0Vec 0) x = x 0 + x 1 := by
    intro x
    simp [CFSG.ClassicalGroups.Unitary.herm, e3uT0Vec, Fin.sum_univ_six]
  have herm1 : ∀ x : Fin 6 → F,
      CFSG.ClassicalGroups.Unitary.herm σ (e3uT0Vec 1) x = x 2 + x 3 := by
    intro x
    simp [CFSG.ClassicalGroups.Unitary.herm, e3uT0Vec, Fin.sum_univ_six]
  have herm2 : ∀ x : Fin 6 → F,
      CFSG.ClassicalGroups.Unitary.herm σ (e3uT0Vec 2) x = x 4 + x 5 := by
    intro x
    simp [CFSG.ClassicalGroups.Unitary.herm, e3uT0Vec, Fin.sum_univ_six]
  have hsum0 : ∀ w : Fin 6 → F,
      (((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec w) 0 +
        (((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec w) 1 = w 0 + w 1 := by
    intro w
    have h := hpres 0 w
    rw [herm0, herm0] at h
    exact h
  have hsum1 : ∀ w : Fin 6 → F,
      (((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec w) 2 +
        (((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec w) 3 = w 2 + w 3 := by
    intro w
    have h := hpres 1 w
    rw [herm1, herm1] at h
    exact h
  have hsum2 : ∀ w : Fin 6 → F,
      (((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec w) 4 +
        (((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec w) 5 = w 4 + w 5 := by
    intro w
    have h := hpres 2 w
    rw [herm2, herm2] at h
    exact h
  have hy0 : ∀ w : Fin 6 → F,
      (((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec w - w) 0 +
        (((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec w - w) 1 = 0 := by
    intro w
    have h := hsum0 w
    simp only [Pi.sub_apply]
    linear_combination h
  have hy1 : ∀ w : Fin 6 → F,
      (((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec w - w) 2 +
        (((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec w - w) 3 = 0 := by
    intro w
    have h := hsum1 w
    simp only [Pi.sub_apply]
    linear_combination h
  have hy2 : ∀ w : Fin 6 → F,
      (((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec w - w) 4 +
        (((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec w - w) 5 = 0 := by
    intro w
    have h := hsum2 w
    simp only [Pi.sub_apply]
    linear_combination h
  have hdecomp : ∀ s : Fin 6 → F, (∀ j : Fin 6, j.val % 2 = 1 → s j = 0) →
      (frameMat σ ω).mulVec s = s 0 • e3uT0Vec 0 + s 2 • e3uT0Vec 1 + s 4 • e3uT0Vec 2 := by
    intro s hs
    have h1 : s 1 = 0 := hs 1 (by decide)
    have h3 : s 3 = 0 := hs 3 (by decide)
    have h5 : s 5 = 0 := hs 5 (by decide)
    funext k
    fin_cases k <;>
      simp [frameMat, Matrix.mulVec, dotProduct, Fin.sum_univ_six, e3uT0Vec, h1, h3, h5]
  have hfixS0 : ∀ s : Fin 6 → F, (∀ j : Fin 6, j.val % 2 = 1 → s j = 0) →
      ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec ((frameMat σ ω).mulVec s) =
        (frameMat σ ω).mulVec s := by
    intro s hs
    rw [hdecomp s hs]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hfix]
  have hfixS : ∀ s : Fin 6 → F, (∀ j : Fin 6, j.val % 2 = 1 → s j = 0) →
      (frameInv σ ω * ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * frameMat σ ω).mulVec s =
        s := by
    intro s hs
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfixS0 s hs, Matrix.mulVec_mulVec,
      frameInv_mul_frameMat hω, Matrix.one_mulVec]
  have hodd : ∀ y : Fin 6 → F, y 0 + y 1 = 0 → y 2 + y 3 = 0 → y 4 + y 5 = 0 →
      ∀ j : Fin 6, j.val % 2 = 1 → (frameInv σ ω).mulVec y j = 0 := by
    intro y h0 h1 h2 j hj
    fin_cases j
    · simp at hj
    · simpa [frameInv, Matrix.mulVec, dotProduct, Fin.sum_univ_six] using h0
    · simp at hj
    · simpa [frameInv, Matrix.mulVec, dotProduct, Fin.sum_univ_six] using h1
    · simp at hj
    · simpa [frameInv, Matrix.mulVec, dotProduct, Fin.sum_univ_six] using h2
  have hy : ∀ v : Fin 6 → F,
      (frameInv σ ω * ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * frameMat σ ω).mulVec v - v =
        (frameInv σ ω).mulVec
          ((((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec ((frameMat σ ω).mulVec v)) -
            (frameMat σ ω).mulVec v) := by
    intro v
    have h1 : (frameInv σ ω).mulVec ((frameMat σ ω).mulVec v) = v := by
      rw [Matrix.mulVec_mulVec, frameInv_mul_frameMat hω, Matrix.one_mulVec]
    rw [Matrix.mulVec_sub, h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hX : (((frameGL σ ω hω)⁻¹ * (g : GL (Fin 6) F) * frameGL σ ω hω : GL (Fin 6) F) :
      Matrix (Fin 6) (Fin 6) F) =
        frameInv σ ω * ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * frameMat σ ω := by
    rw [Units.val_mul, Units.val_mul]
    rfl
  have hAS : (frameInv σ ω).det * (frameMat σ ω).det = 1 := by
    rw [← Matrix.det_mul, frameInv_mul_frameMat hω, Matrix.det_one]
  show _ ∧ _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [hX, Matrix.det_mul, Matrix.det_mul, hdetg, mul_one]
    exact hAS
  · intro v
    rw [hX]
    refine s81A12_mem_S0.2 (fun j hj => ?_)
    rw [hy v]
    exact hodd _ (hy0 ((frameMat σ ω).mulVec v)) (hy1 ((frameMat σ ω).mulVec v))
      (hy2 ((frameMat σ ω).mulVec v)) j hj
  · intro s hs
    rw [hX]
    exact hfixS s (s81A12_mem_S0.1 hs)

private theorem longRoot_hyp_conj {a b : Fin 6} (ha : a.val % 2 = 0) (hb : b.val = a.val + 1) :
    conjTr σ (Matrix.transvection a b (1 : F)) * hypGram F * Matrix.transvection a b (1 : F) =
      hypGram F := by
  have hba : b ≠ a := by
    intro h
    have h2 : b.val = a.val := congrArg Fin.val h
    omega
  have hT : conjTr σ (Matrix.transvection a b (1 : F)) = 1 + Matrix.single b a (1 : F) := by
    have hmapadd : ∀ M N : Matrix (Fin 6) (Fin 6) F, (M + N).map σ = M.map σ + N.map σ := by
      intro M N
      ext i j
      simp
    simp only [conjTr, Matrix.transvection, hmapadd, Matrix.map_one (⇑σ) (map_zero σ) (map_one σ),
      Matrix.map_single, map_one, Matrix.transpose_add, Matrix.transpose_one,
      Matrix.transpose_single]
  have hA : ∀ y : Fin 6, hypGram F a y = if b = y then 1 else 0 := by
    intro y
    have key : (a.val / 2 = y.val / 2 ∧ a.val % 2 ≠ y.val % 2) ↔ b = y := by
      rw [Fin.ext_iff]; omega
    simp only [hypGram, Matrix.of_apply]
    by_cases h : b = y
    · rw [if_pos h, if_pos (key.mpr h)]
    · have hP : ¬ (a.val / 2 = y.val / 2 ∧ a.val % 2 ≠ y.val % 2) := fun hk => h (key.mp hk)
      rw [if_neg h, if_neg hP]
  have hB : ∀ x : Fin 6, hypGram F x a = if b = x then 1 else 0 := by
    intro x
    have key : (x.val / 2 = a.val / 2 ∧ x.val % 2 ≠ a.val % 2) ↔ b = x := by
      rw [Fin.ext_iff]; omega
    simp only [hypGram, Matrix.of_apply]
    by_cases h : b = x
    · rw [if_pos h, if_pos (key.mpr h)]
    · have hP : ¬ (x.val / 2 = a.val / 2 ∧ x.val % 2 ≠ a.val % 2) := fun hk => h (key.mp hk)
      rw [if_neg h, if_neg hP]
  have H1 : Matrix.single b a (1 : F) * hypGram F = Matrix.single b b (1 : F) := by
    ext x y
    by_cases hx : x = b
    · rw [hx]; simp [hA, Matrix.single_apply]
    · simp [hx, Ne.symm hx, Matrix.single_apply]
  have H2 : hypGram F * Matrix.single a b (1 : F) = Matrix.single b b (1 : F) := by
    ext x y
    by_cases hy : y = b
    · rw [hy]; simp [hB, Matrix.single_apply]
    · simp [hy, Ne.symm hy, Matrix.single_apply]
  have hsum : Matrix.single b b (1 : F) + Matrix.single b b (1 : F) = 0 := by
    rw [← Matrix.single_add, CharTwo.add_self_eq_zero, Matrix.single_zero]
  have h0 : Matrix.single b b (1 : F) * Matrix.single a b (1 : F) = 0 := by
    simp [hba]
  have hexp : (1 + Matrix.single b a (1 : F)) * hypGram F * (1 + Matrix.single a b (1 : F)) =
      hypGram F + (Matrix.single b a (1 : F) * hypGram F + hypGram F * Matrix.single a b (1 : F) +
        Matrix.single b a (1 : F) * hypGram F * Matrix.single a b (1 : F)) := by
    noncomm_ring
  rw [hT, Matrix.transvection, hexp, H1, H2, h0, add_zero, hsum, add_zero]

private theorem longRoot_mulVec_fix {ω : F} (hω : ω + σ ω = 1) {a b : Fin 6}
    (ha : a.val % 2 = 0) (hb : b.val = a.val + 1) (i : Fin 3) :
    (frameMat σ ω * Matrix.transvection a b (1 : F) * frameInv σ ω).mulVec (e3uT0Vec i) =
      e3uT0Vec i := by
  have hbi : b ≠ (⟨2 * i.val, by omega⟩ : Fin 6) := by
    intro h
    have h2 : b.val = 2 * i.val := congrArg Fin.val h
    omega
  have hv : ((Pi.single (⟨2 * i.val, by omega⟩ : Fin 6) (1 : F) : Fin 6 → F)) b = 0 := by
    rw [Pi.single_apply, if_neg hbi]
  have hTp : Matrix.transvection a b (1 : F) *ᵥ
      (Pi.single (⟨2 * i.val, by omega⟩ : Fin 6) (1 : F) : Fin 6 → F) =
      (Pi.single (⟨2 * i.val, by omega⟩ : Fin 6) (1 : F) : Fin 6 → F) := by
    rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq, hv,
      mul_zero, zero_smul, add_zero]
  have hinv : frameInv σ ω *ᵥ
      (frameMat σ ω *ᵥ (Pi.single (⟨2 * i.val, by omega⟩ : Fin 6) (1 : F) : Fin 6 → F)) =
      (Pi.single (⟨2 * i.val, by omega⟩ : Fin 6) (1 : F) : Fin 6 → F) := by
    rw [Matrix.mulVec_mulVec, frameInv_mul_frameMat hω, Matrix.one_mulVec]
  rw [← frameMat_mulVec_even (σ := σ) ω i, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hinv,
    hTp]

private theorem longRoot_exists (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1)
    {a b : Fin 6} (ha : a.val % 2 = 0) (hb : b.val = a.val + 1) (hne : a ≠ b) :
    ∃ g : SUid σ 6, g ∈ e3uU0Sub σ ∧ (g : GL (Fin 6) F) =
      frameGL σ ω hω * transvGL F a b hne 1 * (frameGL σ ω hω)⁻¹ := by
  have hdet : ((transvGL F a b hne 1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).det = 1 := by
    rw [transvGL_val]
    exact Matrix.det_transvection_of_ne a b hne 1
  have hu : conjTr σ ((transvGL F a b hne 1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
      hypGram F * ((transvGL F a b hne 1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
        hypGram F := by
    rw [transvGL_val]
    exact longRoot_hyp_conj ha hb
  have hmem : ∀ i : Fin 3,
      ((frameGL σ ω hω * transvGL F a b hne 1 * (frameGL σ ω hω)⁻¹ : GL (Fin 6) F) :
        Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec i) = e3uT0Vec i := by
    intro i
    rw [frameConj_val, transvGL_val]
    exact longRoot_mulVec_fix hω ha hb i
  exact ⟨⟨_, frame_conj_mem_SUid hσ.invol hω hdet hu⟩, hmem, rfl⟩

theorem exists_longRoot (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) (j : Fin 3) :
    ∃ g : SUid σ 6, g ∈ e3uU0Sub σ ∧ (g : GL (Fin 6) F) =
      frameGL σ ω hω * transvGL F ⟨2 * j.val, by omega⟩ ⟨2 * j.val + 1, by omega⟩
        (by intro h; have := congrArg Fin.val h; simp at this) 1 * (frameGL σ ω hω)⁻¹ := by
  exact longRoot_exists hσ hω (by simp) (by simp) _

theorem smul_mem_Fq_of_mem_Wsub (hσ : ∀ c, σ (σ c) = c) {v p : Cube F} (hv : v ∈ Wsub σ)
    (hp : p ∈ Wsub σ) (hp0 : p ≠ 0) {c : F} (h : v = c • p) : σ c = c := by
  have hv' : theta σ v = v := mem_Wsub_iff.mp hv
  have hp' : theta σ p = p := mem_Wsub_iff.mp hp
  have h3 : σ c • p = c • p := by
    calc σ c • p = σ c • theta σ p := by rw [hp']
      _ = theta σ (c • p) := (theta_smul c p).symm
      _ = theta σ v := by rw [h]
      _ = v := hv'
      _ = c • p := h
  have h4 : (σ c - c) • p = 0 := (sub_smul (σ c) c p).trans (sub_eq_zero.mpr h3)
  rcases smul_eq_zero.mp h4 with h5 | h5
  · exact sub_eq_zero.mp h5
  · exact absurd h5 hp0

@[expose] def pairBlock (a b c d : F) : Matrix (Fin 6) (Fin 6) F :=
  Matrix.of fun i j =>
    if i.val < 4 ∨ j.val < 4 then (if i = j then 1 else 0)
    else if i.val = 4 then (if j.val = 4 then a else c)
    else (if j.val = 4 then b else d)

theorem pairBlock_unitary (hσ : ∀ c, σ (σ c) = c) {a b c d : F} (ha : σ a = a) (hb : σ b = b)
    (hc : σ c = c) (hd : σ d = d) (hdet : a * d + b * c = 1) :
    conjTr σ (pairBlock a b c d) * hypGram F * pairBlock a b c d = hypGram F ∧
      (pairBlock a b c d).det = 1 ∧ (pairBlock a b c d).det ≠ 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hσM : ∀ i j, σ (pairBlock a b c d i j) = pairBlock a b c d i j := by
    intro i j
    simp only [pairBlock, Matrix.of_apply]
    split_ifs <;> simp [ha, hb, hc, hd]
  have hMT : conjTr σ (pairBlock a b c d) = (pairBlock a b c d)ᵀ := by
    ext i j
    rw [conjTr_apply, hσM, Matrix.transpose_apply]
  have hunit : conjTr σ (pairBlock a b c d) * hypGram F * pairBlock a b c d = hypGram F := by
    rw [hMT]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_six, pairBlock, hypGram] <;>
      first
        | linear_combination hdet
        | linear_combination (a * b) * h2
        | linear_combination (c * d) * h2
  have hdet1 : (pairBlock a b c d).det = 1 := by
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, pairBlock]
    linear_combination hdet - (b * c) * h2
  exact ⟨hunit, hdet1, by rw [hdet1]; exact one_ne_zero⟩

open exteriorPower

private noncomputable def u6lR0 (L : Type) [Field L] : Cube L :=
  ιMulti L 3 ![e L 0, e L 2, e L 5]

private def u6lJ : Set.powersetCard (Fin 6) 3 :=
  tripleSet 0 2 5 (by decide) (by decide) (by decide)

private theorem u6l_mem_S0_iff {v : Fin 6 → F} : v ∈ S0 F ↔ ∀ j : Fin 6, j.val % 2 = 1 → v j = 0 :=
  Iff.rfl

private theorem u6l_mem_UnipGL_iff {X : GL (Fin 6) F} :
    X ∈ UnipGL F (S0 F) ↔ (X : Matrix (Fin 6) (Fin 6) F).det = 1 ∧
      (∀ v : Fin 6 → F, (X : Matrix (Fin 6) (Fin 6) F).mulVec v - v ∈ S0 F) ∧
      ∀ s ∈ S0 F, (X : Matrix (Fin 6) (Fin 6) F).mulVec s = s :=
  Iff.rfl

private theorem u6l_e_mem_S0 {i : Fin 6} (hi : i.val % 2 = 0) : e F i ∈ S0 F := by
  refine u6l_mem_S0_iff.mpr fun j hj => ?_
  have hji : j ≠ i := fun h => by subst h; omega
  simp [e, Pi.single_apply, hji]

private theorem u6l_pair_e0 (a b c d : F) : (pairBlock a b c d).mulVec (e F 0) = e F 0 := by
  funext j
  fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six, pairBlock, e, Pi.single_apply]

private theorem u6l_pair_e2 (a b c d : F) : (pairBlock a b c d).mulVec (e F 2) = e F 2 := by
  funext j
  fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six, pairBlock, e, Pi.single_apply]

private theorem u6l_pair_e4 (a b c d : F) :
    (pairBlock a b c d).mulVec (e F 4) = a • e F 4 + b • e F 5 := by
  funext j
  fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_six, pairBlock, e, Pi.single_apply]

private theorem u6l_pair_rho (g : GL (Fin 6) F) {a b c d : F}
    (hg : (g : Matrix (Fin 6) (Fin 6) F) = pairBlock a b c d) :
    rho F g (p0 F) = a • p0 F + b • u6lR0 F := by
  unfold u6lR0
  rw [p0_eq, rho_ιMulti]
  have h0 : (g : Matrix (Fin 6) (Fin 6) F).mulVec (e F 0) = e F 0 := by
    rw [hg]; exact u6l_pair_e0 a b c d
  have h2 : (g : Matrix (Fin 6) (Fin 6) F).mulVec (e F 2) = e F 2 := by
    rw [hg]; exact u6l_pair_e2 a b c d
  have h4 : (g : Matrix (Fin 6) (Fin 6) F).mulVec (e F 4) = a • e F 4 + b • e F 5 := by
    rw [hg]; exact u6l_pair_e4 a b c d
  have hv : (fun i => (g : Matrix (Fin 6) (Fin 6) F).mulVec (![e F 0, e F 2, e F 4] i)) =
      ![e F 0, e F 2, a • e F 4 + b • e F 5] := by
    funext i
    fin_cases i
    · exact h0
    · exact h2
    · exact h4
  rw [hv, ι3_add_thd, ι3_smul_thd, ι3_smul_thd]

private theorem u6l_rho_inv_rho (S : GL (Fin 6) F) (v : Cube F) :
    rho F S⁻¹ (rho F S v) = v := by
  rw [← rho_mul_apply, inv_mul_cancel, rho_one, Module.End.one_apply]

private theorem u6l_rho_conj (S X : GL (Fin 6) F) (v : Cube F) :
    rho F (S * X * S⁻¹) (rho F S v) = rho F S (rho F X v) := by
  rw [rho_mul_apply, rho_mul_apply, u6l_rho_inv_rho]

private theorem u6l_rho_inv_pt0 {ω : F} (hω : ω + σ ω = 1) :
    rho F (frameGL σ ω hω)⁻¹ (pt0 F) = p0 F := by
  rw [← rho_frameGL_p0 ω hω, u6l_rho_inv_rho]

private theorem u6l_rho_conj_pt0 {ω : F} (hω : ω + σ ω = 1) {a b c d : F} {X g : GL (Fin 6) F}
    (hX : (X : Matrix (Fin 6) (Fin 6) F) = pairBlock a b c d)
    (hg : g = frameGL σ ω hω * X * (frameGL σ ω hω)⁻¹) :
    rho F g (pt0 F) = a • pt0 F + b • rho F (frameGL σ ω hω) (u6lR0 F) := by
  subst hg
  calc rho F (frameGL σ ω hω * X * (frameGL σ ω hω)⁻¹) (pt0 F)
      = rho F (frameGL σ ω hω * X * (frameGL σ ω hω)⁻¹)
          (rho F (frameGL σ ω hω) (p0 F)) := by rw [rho_frameGL_p0]
    _ = rho F (frameGL σ ω hω) (rho F X (p0 F)) := u6l_rho_conj _ _ _
    _ = rho F (frameGL σ ω hω) (a • p0 F + b • u6lR0 F) := by rw [u6l_pair_rho X hX]
    _ = a • pt0 F + b • rho F (frameGL σ ω hω) (u6lR0 F) := by
        rw [map_add, map_smul, map_smul, rho_frameGL_p0]

private theorem u6l_iota_e02 (t : Fin 6 → F) (ht : ∀ j : Fin 6, j.val % 2 = 1 → t j = 0) :
    ιMulti F 3 ![e F 0, e F 2, e F 5 + t] =
      ιMulti F 3 ![e F 0, e F 2, e F 5] + t 4 • ιMulti F 3 ![e F 0, e F 2, e F 4] := by
  have hdec : t = t 0 • e F 0 + t 2 • e F 2 + t 4 • e F 4 := by
    have h1 := ht 1 (by decide)
    have h3 := ht 3 (by decide)
    have h5 := ht 5 (by decide)
    funext j
    fin_cases j <;> simp [e, Pi.single_apply, h1, h3, h5]
  conv_lhs => rw [hdec]
  simp only [ι3_add_thd, ι3_smul_thd, ι3_eq_fst_thd, ι3_eq_snd_thd, smul_zero, add_zero, zero_add]

private theorem u6l_rho_unip_r0 {X : GL (Fin 6) F} (hX : X ∈ UnipGL F (S0 F)) :
    ∃ s : F, rho F X (u6lR0 F) - u6lR0 F = s • p0 F := by
  obtain ⟨-, hX2, hX3⟩ := u6l_mem_UnipGL_iff.mp hX
  have hX0 : (X : Matrix (Fin 6) (Fin 6) F).mulVec (e F 0) = e F 0 :=
    hX3 _ (u6l_e_mem_S0 (i := 0) (by decide))
  have hX2' : (X : Matrix (Fin 6) (Fin 6) F).mulVec (e F 2) = e F 2 :=
    hX3 _ (u6l_e_mem_S0 (i := 2) (by decide))
  have ht : ∀ j : Fin 6, j.val % 2 = 1 →
      ((X : Matrix (Fin 6) (Fin 6) F).mulVec (e F 5) - e F 5) j = 0 :=
    u6l_mem_S0_iff.mp (hX2 (e F 5))
  have hvec : (fun i => (X : Matrix (Fin 6) (Fin 6) F).mulVec (![e F 0, e F 2, e F 5] i)) =
      ![e F 0, e F 2, e F 5 + ((X : Matrix (Fin 6) (Fin 6) F).mulVec (e F 5) - e F 5)] := by
    funext i
    fin_cases i <;> simp [hX0, hX2']
  refine ⟨((X : Matrix (Fin 6) (Fin 6) F).mulVec (e F 5) - e F 5) 4, ?_⟩
  unfold u6lR0
  rw [rho_ιMulti, hvec, u6l_iota_e02 _ ht, p0_eq]
  abel

private theorem u6l_pt0_diff {ω : F} (hω : ω + σ ω = 1) {X : GL (Fin 6) F} {s : F}
    (hs : rho F X (u6lR0 F) - u6lR0 F = s • p0 F) :
    rho F (frameGL σ ω hω) (rho F X (u6lR0 F)) - rho F (frameGL σ ω hω) (u6lR0 F) =
      s • pt0 F := by
  rw [← map_sub, hs, map_smul, rho_frameGL_p0]

private theorem u6l_coord_r0 : coord F (u6lR0 F) u6lJ = 1 := by
  unfold u6lR0
  rw [coord_ιMulti_e_sorted (i := 0) (j := 2) (k := 5) (by decide) (by decide)]
  have h : u6lJ.val = ({0, 2, 5} : Finset (Fin 6)) := rfl
  rw [if_pos h]

private theorem u6l_coord_p0 : coord F (p0 F) u6lJ = 0 := by
  rw [p0_eq, coord_ιMulti_e_sorted (i := 0) (j := 2) (k := 4) (by decide) (by decide)]
  have h : ¬ (u6lJ.val = ({0, 2, 4} : Finset (Fin 6))) := by decide
  rw [if_neg h]

private theorem u6l_exists_cd {a b : F} (ha : σ a = a) (hb : σ b = b) (h : a ≠ 0 ∨ b ≠ 0) :
    ∃ c d : F, σ c = c ∧ σ d = d ∧ a * d + b * c = 1 := by
  rcases h with h | h
  · exact ⟨0, a⁻¹, map_zero σ, by rw [map_inv₀, ha], by rw [mul_zero, add_zero, mul_inv_cancel₀ h]⟩
  · exact ⟨b⁻¹, 0, by rw [map_inv₀, hb], map_zero σ, by rw [mul_zero, zero_add, mul_inv_cancel₀ h]⟩

private theorem u6l_exists_pairSU (hσ : ∀ c, σ (σ c) = c) {ω : F} (hω : ω + σ ω = 1) {a b c d : F}
    (ha : σ a = a) (hb : σ b = b) (hc : σ c = c) (hd : σ d = d) (hdet : a * d + b * c = 1) :
    ∃ g : SUid σ 6, ∃ X : GL (Fin 6) F, (X : Matrix (Fin 6) (Fin 6) F) = pairBlock a b c d ∧
      (g : GL (Fin 6) F) = frameGL σ ω hω * X * (frameGL σ ω hω)⁻¹ := by
  obtain ⟨h1, h2, h3⟩ := pairBlock_unitary hσ ha hb hc hd hdet
  obtain ⟨X, hXv⟩ : ∃ X : GL (Fin 6) F, (X : Matrix (Fin 6) (Fin 6) F) = pairBlock a b c d :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (pairBlock a b c d) h3, rfl⟩
  have hmem : frameGL σ ω hω * X * (frameGL σ ω hω)⁻¹ ∈ SUid σ 6 :=
    frame_conj_mem_SUid hσ hω (by rw [hXv]; exact h2) (by rw [hXv]; exact h1)
  exact ⟨⟨_, hmem⟩, X, hXv, rfl⟩

end CFSG.RankThree.GF2n.Smith81.U6Cube

namespace CFSG.RankThree.GF2n.Smith81

open CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.RankThree.GF2n.Smith81.A5Cube
  CFSG.RankThree.GF2n.Smith81.EGeom CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.LieType.BorelTits

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F} {K : Type} [Field K]
  {e : K ≃+* Fσ σ}

theorem u6_U0_fix : ∀ u ∈ e3uU0 σ e, u (e3uP0 σ e) = e3uP0 σ e := by
  intro u hu
  have hu' : u ∈ (e3uU0Sub σ).map (e3uWact σ e) := hu
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hu'
  have hg' : ∀ i : Fin 3, ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec i) =
      e3uT0Vec i := hg
  have hpt : rho F (g : GL (Fin 6) F) (pt0 F) = pt0 F := by
    rw [pt0_eq_ιMulti_T0, rho_ιMulti]
    congr 1
    funext i
    exact hg' i
  have hP : e3uVal (e3uP0 σ e) = pt0 F := rfl
  have key : e3uVal (e3uWact σ e g (e3uP0 σ e)) = e3uVal (e3uP0 σ e) := by
    rw [e3uWact_val, hP]
    exact hpt
  exact Subtype.ext key

theorem exists_pair_of_two_odd (s : Finset (Fin 6)) (hs : s.card = 3)
    (h2 : 2 ≤ (s.filter (fun i : Fin 6 => i.val % 2 = 1)).card) :
    ∃ j : Fin 3, (⟨2 * j.val + 1, by omega⟩ : Fin 6) ∈ s ∧ (⟨2 * j.val, by omega⟩ : Fin 6) ∉ s ∧
      ∃ c : Fin 6, c ∈ s ∧ c.val % 2 = 1 ∧ c ≠ ⟨2 * j.val + 1, by omega⟩ := by
  revert s
  decide

private theorem coord_eq_zero_of_root_fix {a b : Fin 6} (hab : a.val + 1 = b.val) (hne : a ≠ b)
    (t : F) (ξ : Cube F) (I : Set.powersetCard (Fin 6) 3) (hbI : b ∈ I.val) (haI : a ∉ I.val)
    (c : Fin 6) (hcI : c ∈ I.val) (hc : c.val % 2 = 1) (hcb : c ≠ b)
    (h : rho F (transvGL F a b hne 1) ξ - ξ = t • p0 F) : coord F ξ I = 0 := by
  obtain ⟨J, hJ⟩ : ∃ J, replSet I a b hbI haI = J := ⟨_, rfl⟩
  have hJc : a ∈ J.val ∧ b ∉ J.val := replSet_eq_imp hne hbI haI hJ
  have hIJ : I = replSet J b a hJc.1 hJc.2 := (replSet_eq_iff hbI haI hJc.1 hJc.2).mp hJ
  have hcJ : c ∈ J.val := by
    rw [← hJ]
    exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hcb, hcI⟩)
  have hSJ : S024 ≠ J := by
    intro hS
    have hcS : c ∈ S024.val := by
      rw [hS]
      exact hcJ
    exact odd_not_mem_S024 c hc hcS
  have hp0 : coord F (p0 F) J = 0 := by
    rw [p0, coord_cubeBasis, if_neg hSJ]
  have key := coord_rho_transvGL (Or.inl hab) hne 1 ξ J
  rw [dif_pos hJc, one_mul] at key
  have hW : coord F ξ (replSet J b a hJc.1 hJc.2) = coord F ξ I := by
    rw [hIJ]
  have h1 : coord F (rho F (transvGL F a b hne 1) ξ - ξ) J = coord F (t • p0 F) J := by
    rw [h]
  rw [coord_sub, coord_smul, hp0, mul_zero] at h1
  linear_combination h1 - key - hW

theorem coord_hat_eq_zero_of_mem_Wsp (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1)
    {ξ : E3UWspace σ e} (hξ : ξ ∈ Wsp (Submodule.span K {e3uP0 σ e}) (e3uU0 σ e))
    (I : Set.powersetCard (Fin 6) 3)
    (hI : 2 ≤ (I.val.filter (fun i : Fin 6 => i.val % 2 = 1)).card) :
    coord F (rho F ((frameGL σ ω hω)⁻¹ : GL (Fin 6) F) (e3uVal ξ)) I = 0 := by
  obtain ⟨j, hbI, haI, c, hcI, hc, hcb⟩ := exists_pair_of_two_odd I.val I.prop hI
  obtain ⟨g, hgU, hgeq⟩ := exists_longRoot hσ hω j
  have hne : (⟨2 * j.val, by omega⟩ : Fin 6) ≠ ⟨2 * j.val + 1, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have hu : e3uWact σ e g ∈ e3uU0 σ e := Subgroup.mem_map.mpr ⟨g, hgU, rfl⟩
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (mem_Wsp.mp hξ _ hu)
  have hvt : rho F (g : GL (Fin 6) F) (e3uVal ξ) - e3uVal ξ = ((e t : Fσ σ) : F) • pt0 F :=
    (congrArg e3uVal ht).symm
  have hSS : ∀ y : Cube F, rho F (frameGL σ ω hω)⁻¹ (rho F (frameGL σ ω hω) y) = y := by
    intro y
    rw [← rho_mul_apply, inv_mul_cancel, rho_one]
    rfl
  have hconj : ∀ x : Cube F, rho F (frameGL σ ω hω)⁻¹ (rho F (g : GL (Fin 6) F) x) =
      rho F (transvGL F _ _ hne 1) (rho F (frameGL σ ω hω)⁻¹ x) := by
    intro x
    rw [hgeq, mul_assoc, rho_mul_apply, rho_mul_apply, hSS]
  have hpS : rho F (frameGL σ ω hω)⁻¹ (pt0 F) = p0 F := by
    rw [← rho_frameGL_p0 ω hω, hSS]
  have hmain := congrArg (rho F (frameGL σ ω hω)⁻¹) hvt
  rw [map_sub, hconj, map_smul, hpS] at hmain
  exact coord_eq_zero_of_root_fix (a := ⟨2 * j.val, by omega⟩) (b := ⟨2 * j.val + 1, by omega⟩)
    rfl hne _ _ I hbI haI c hcI hc hcb hmain

private theorem u6W_e3uVal_sub (w w' : E3UWspace σ e) :
    e3uVal (w - w') = e3uVal w - e3uVal w' := rfl

private theorem u6W_e3uVal_mem (w : E3UWspace σ e) : e3uVal w ∈ U6Cube.Wsub σ :=
  U6Cube.mem_Wform_iff.mp (show U6Cube.Wform σ from w).2

private theorem u6W_e3uVal_eq_zero {w : E3UWspace σ e} (h : e3uVal w = 0) : w = 0 :=
  Subtype.ext h

private theorem u6W_descent {ω : F} (hω : ω + σ ω = 1)
    {x y : Cube F} (hx : x ∈ U6Cube.Wsub σ) (hy : y ∈ U6Cube.Wsub σ) (h : x + ω • y = 0) :
    x = 0 ∧ y = 0 := by
  have h2F : ∀ z : F, z + z = 0 := fun z => CharTwo.add_self_eq_zero z
  have hθ : U6Cube.theta σ (x + ω • y) = U6Cube.theta σ 0 := by rw [h]
  rw [map_add, U6Cube.theta_smul, map_zero, U6Cube.mem_Wsub_iff.mp hx,
    U6Cube.mem_Wsub_iff.mp hy] at hθ
  have h2 : ω • y = σ ω • y := add_left_cancel (h.trans hθ.symm)
  have hy0 : y = 0 := by
    calc y = (ω + σ ω) • y := by rw [hω, one_smul]
      _ = ω • y + σ ω • y := add_smul _ _ _
      _ = σ ω • y + σ ω • y := by rw [h2]
      _ = (σ ω + σ ω) • y := (add_smul _ _ _).symm
      _ = 0 := by rw [h2F, zero_smul]
  refine ⟨?_, hy0⟩
  rw [hy0, smul_zero, add_zero] at h
  exact h

private theorem u6W_card_sq_le {ω : F} (hω : ω + σ ω = 1)
    (A : Submodule K (E3UWspace σ e))
    (hA : ∀ ξ ∈ A, ∀ I : Set.powersetCard (Fin 6) 3,
      2 ≤ (I.val.filter (fun i : Fin 6 => i.val % 2 = 1)).card →
      coord F (rho F ((frameGL σ ω hω)⁻¹ : GL (Fin 6) F) (e3uVal ξ)) I = 0) :
    Nat.card A * Nat.card A ≤ Nat.card (W0Idx → F) := by
  have hrho_inj : ∀ x : Cube F, rho F ((frameGL σ ω hω)⁻¹ : GL (Fin 6) F) x = 0 → x = 0 := by
    intro x hx
    have h1 : rho F (frameGL σ ω hω : GL (Fin 6) F)
        (rho F ((frameGL σ ω hω)⁻¹ : GL (Fin 6) F) x) = x := by
      rw [← rho_mul_apply, mul_inv_cancel, rho_one, Module.End.one_apply]
    rw [hx, map_zero] at h1
    exact h1.symm
  have hA' : ∀ (a : A) (I : Set.powersetCard (Fin 6) 3),
      2 ≤ (I.val.filter (fun i : Fin 6 => i.val % 2 = 1)).card →
      coord F (rho F ((frameGL σ ω hω)⁻¹ : GL (Fin 6) F) (e3uVal (a : E3UWspace σ e))) I = 0 :=
    fun a I hI => hA (a : E3UWspace σ e) a.2 I hI
  have hvT : ∀ (a b : A) (I : Set.powersetCard (Fin 6) 3),
      2 ≤ (I.val.filter (fun i : Fin 6 => i.val % 2 = 1)).card →
      coord F (rho F ((frameGL σ ω hω)⁻¹ : GL (Fin 6) F)
        (e3uVal (a : E3UWspace σ e) + ω • e3uVal (b : E3UWspace σ e))) I = 0 := by
    intro a b I hI
    rw [map_add, map_smul, coord_add, coord_smul, hA' a I hI, hA' b I hI, mul_zero, add_zero]
  have hinj : Function.Injective (fun p : A × A => fun s : W0Idx =>
      coord F (rho F ((frameGL σ ω hω)⁻¹ : GL (Fin 6) F)
        (e3uVal (p.1 : E3UWspace σ e) + ω • e3uVal (p.2 : E3UWspace σ e))) ⟨s.1, s.2.1⟩) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hG
    have hdiff : rho F ((frameGL σ ω hω)⁻¹ : GL (Fin 6) F)
        ((e3uVal (a : E3UWspace σ e) + ω • e3uVal (b : E3UWspace σ e)) -
          (e3uVal (a' : E3UWspace σ e) + ω • e3uVal (b' : E3UWspace σ e))) = 0 := by
      apply eq_zero_of_coord_eq_zero
      intro I
      rw [map_sub, coord_sub]
      by_cases hI : (I.val.filter (fun i : Fin 6 => i.val % 2 = 1)).card ≤ 1
      · exact sub_eq_zero.mpr (congrFun hG ⟨I.val, I.prop, hI⟩)
      · have hI2 : 2 ≤ (I.val.filter (fun i : Fin 6 => i.val % 2 = 1)).card := by omega
        rw [hvT a b I hI2, hvT a' b' I hI2, sub_zero]
    have hv := sub_eq_zero.mp (hrho_inj _ hdiff)
    have hxy : e3uVal ((a : E3UWspace σ e) - (a' : E3UWspace σ e)) +
        ω • e3uVal ((b : E3UWspace σ e) - (b' : E3UWspace σ e)) = 0 := by
      rw [u6W_e3uVal_sub, u6W_e3uVal_sub, smul_sub]
      calc _ = (e3uVal (a : E3UWspace σ e) + ω • e3uVal (b : E3UWspace σ e)) -
            (e3uVal (a' : E3UWspace σ e) + ω • e3uVal (b' : E3UWspace σ e)) := by abel
        _ = 0 := by rw [hv, sub_self]
    obtain ⟨hx, hy⟩ := u6W_descent hω
      (u6W_e3uVal_mem ((a : E3UWspace σ e) - (a' : E3UWspace σ e)))
      (u6W_e3uVal_mem ((b : E3UWspace σ e) - (b' : E3UWspace σ e))) hxy
    have ha : (a : E3UWspace σ e) = (a' : E3UWspace σ e) :=
      sub_eq_zero.mp (u6W_e3uVal_eq_zero hx)
    have hb : (b : E3UWspace σ e) = (b' : E3UWspace σ e) :=
      sub_eq_zero.mp (u6W_e3uVal_eq_zero hy)
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective _ hinj

theorem u6_W_le (hσ : IsUnitaryInvolution σ) [Finite K] (hF : Nat.card F = Nat.card K ^ 2) :
    Nat.card (Wsp (Submodule.span K {e3uP0 σ e}) (e3uU0 σ e)) ≤ Nat.card K ^ 10 := by
  obtain ⟨ω, hω⟩ := hσ.trace_surj 1 (map_one σ)
  have key := u6W_card_sq_le hω (Wsp (Submodule.span K {e3uP0 σ e}) (e3uU0 σ e))
    (fun ξ hξ I hI => coord_hat_eq_zero_of_mem_Wsp hσ hω hξ I hI)
  rw [Nat.card_fun, card_W0Idx, hF] at key
  have h10 : (Nat.card K ^ 2) ^ 10 = Nat.card K ^ 10 * Nat.card K ^ 10 := by ring
  rw [h10] at key
  exact Nat.mul_self_le_mul_self_iff.mp key

theorem u6_line (hσ : IsUnitaryInvolution σ) :
    ∃ g₁ ∈ e3uGam σ e, g₁ (e3uP0 σ e) ∈ Wsp (Submodule.span K {e3uP0 σ e}) (e3uU0 σ e) ∧
      g₁ (e3uP0 σ e) ∉ Submodule.span K {e3uP0 σ e} ∧
      ∀ a b : K, (a ≠ 0 ∨ b ≠ 0) → ∃ g ∈ e3uGam σ e, g (e3uP0 σ e) = a • e3uP0 σ e + b • g₁ (e3uP0 σ e) := by
  obtain ⟨ω, hω⟩ := hσ.trace_surj 1 (map_one σ)
  have hinv : ∀ c, σ (σ c) = c := hσ.invol
  have hfix : ∀ x : K, σ ((e x : Fσ σ) : F) = ((e x : Fσ σ) : F) :=
    fun x => mem_Fσ_iff.mp (e x).2
  have hne : ∀ x : K, x ≠ 0 → ((e x : Fσ σ) : F) ≠ 0 := fun x hx h0 =>
    hx (e.injective (by rw [map_zero]; exact Subtype.ext h0))
  have hsmul : ∀ (c : K) (w : E3UWspace σ e), e3uVal (c • w) = ((e c : Fσ σ) : F) • e3uVal w :=
    fun _ _ => rfl
  have hadd : ∀ x y : E3UWspace σ e, e3uVal (x + y) = e3uVal x + e3uVal y := fun _ _ => rfl
  have hsub : ∀ x y : E3UWspace σ e, e3uVal (x - y) = e3uVal x - e3uVal y := fun _ _ => rfl
  have hinj : ∀ w w' : E3UWspace σ e, e3uVal w = e3uVal w' → w = w' :=
    fun _ _ h => Subtype.ext h
  have hP0 : e3uVal (e3uP0 σ e) = pt0 F := rfl
  have hpt0W : pt0 F ∈ Wsub σ := mem_Wsub_iff.mpr theta_pt0
  have hpt0ne : pt0 F ≠ 0 := pt0_ne_zero
  have hWmem : ∀ w : E3UWspace σ e, e3uVal w ∈ Wsub σ :=
    fun w => mem_Wform_iff.mp (show Wform σ from w).2
  have hmemG : ∀ g : SUid σ 6, e3uWact σ e g ∈ e3uGam σ e :=
    fun g => MonoidHom.mem_range.mpr ⟨g, rfl⟩
  obtain ⟨gs, Xs, hXs, hgs⟩ := u6l_exists_pairSU hinv hω (a := 0) (b := 1) (c := 1) (d := 0)
    (map_zero σ) (map_one σ) (map_one σ) (map_zero σ) (by norm_num)
  have hP1 : e3uVal (e3uWact σ e gs (e3uP0 σ e)) = rho F (frameGL σ ω hω) (u6lR0 F) := by
    rw [e3uWact_val, hP0, u6l_rho_conj_pt0 hω hXs hgs, zero_smul, one_smul, zero_add]
  refine ⟨e3uWact σ e gs, hmemG gs, ?_, ?_, ?_⟩
  ·
    rw [mem_Wsp]
    intro u hu
    obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨X', hX'⟩ : ∃ X' : GL (Fin 6) F,
        X' = (frameGL σ ω hω)⁻¹ * (g' : GL (Fin 6) F) * frameGL σ ω hω := ⟨_, rfl⟩
    have hU' : X' ∈ UnipGL F (S0 F) := by
      rw [hX']; exact frame_conj_unip_of_mem_U0Sub hσ hω hg'
    have hgX : (g' : GL (Fin 6) F) = frameGL σ ω hω * X' * (frameGL σ ω hω)⁻¹ := by
      rw [hX']; group
    obtain ⟨s, hs⟩ := u6l_rho_unip_r0 hU'
    have hA : e3uVal (e3uWact σ e g' (e3uWact σ e gs (e3uP0 σ e))) =
        rho F (frameGL σ ω hω) (rho F X' (u6lR0 F)) := by
      rw [e3uWact_val, hP1, hgX, u6l_rho_conj]
    have hdiff : e3uVal (e3uWact σ e g' (e3uWact σ e gs (e3uP0 σ e)) -
        e3uWact σ e gs (e3uP0 σ e)) = s • pt0 F := by
      rw [hsub, hA, hP1, u6l_pt0_diff hω hs]
    have hWs : s • pt0 F ∈ Wsub σ := by
      rw [← hdiff]; exact hWmem _
    have hσs : σ s = s := smul_mem_Fq_of_mem_Wsub hinv hWs hpt0W hpt0ne rfl
    obtain ⟨k, hk⟩ : ∃ k : K, ((e k : Fσ σ) : F) = s :=
      ⟨e.symm ⟨s, mem_Fσ_iff.mpr hσs⟩, by simp⟩
    have hkP : k • e3uP0 σ e = e3uWact σ e g' (e3uWact σ e gs (e3uP0 σ e)) -
        e3uWact σ e gs (e3uP0 σ e) :=
      hinj _ _ (by rw [hsmul, hk, hP0, hdiff])
    rw [← hkP]
    exact Submodule.smul_mem _ k (Submodule.mem_span_singleton_self _)
  ·
    intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have h1 : ((e c : Fσ σ) : F) • pt0 F = rho F (frameGL σ ω hω) (u6lR0 F) := by
      rw [← hP1, ← hc, hsmul, hP0]
    have h2 : ((e c : Fσ σ) : F) • p0 F = u6lR0 F := by
      have h : rho F (frameGL σ ω hω)⁻¹ (((e c : Fσ σ) : F) • pt0 F) =
          rho F (frameGL σ ω hω)⁻¹ (rho F (frameGL σ ω hω) (u6lR0 F)) := by rw [h1]
      rw [map_smul, u6l_rho_inv_pt0 hω, u6l_rho_inv_rho] at h
      exact h
    have h3 : coord F (((e c : Fσ σ) : F) • p0 F) u6lJ = coord F (u6lR0 F) u6lJ := by
      rw [h2]
    rw [coord_smul, u6l_coord_p0, u6l_coord_r0, mul_zero] at h3
    exact zero_ne_one h3
  ·
    intro a b hab
    have hab' : ((e a : Fσ σ) : F) ≠ 0 ∨ ((e b : Fσ σ) : F) ≠ 0 := by
      rcases hab with h | h
      · exact Or.inl (hne a h)
      · exact Or.inr (hne b h)
    obtain ⟨c, d, hc, hd, hdet⟩ := u6l_exists_cd (hfix a) (hfix b) hab'
    obtain ⟨g, X, hX, hg⟩ := u6l_exists_pairSU hinv hω (hfix a) (hfix b) hc hd hdet
    refine ⟨e3uWact σ e g, hmemG g, ?_⟩
    apply hinj
    have hL : e3uVal (e3uWact σ e g (e3uP0 σ e)) =
        ((e a : Fσ σ) : F) • pt0 F + ((e b : Fσ σ) : F) • rho F (frameGL σ ω hω) (u6lR0 F) := by
      rw [e3uWact_val, hP0, u6l_rho_conj_pt0 hω hX hg]
    have hR : e3uVal (a • e3uP0 σ e + b • e3uWact σ e gs (e3uP0 σ e)) =
        ((e a : Fσ σ) : F) • pt0 F + ((e b : Fσ σ) : F) • rho F (frameGL σ ω hω) (u6lR0 F) := by
      rw [hadd, hsmul, hsmul, hP0, hP1]
    exact hL.trans hR.symm

private theorem u6ML_rho_conj (S s : GL (Fin 6) F) (v : Cube F) :
    rho F (S⁻¹ * s * S) v = rho F S⁻¹ (rho F s (rho F S v)) := by
  rw [rho_mul_apply, rho_mul_apply]

private theorem u6ML_rho_comm {S X Z : GL (Fin 6) F} (h : S * X = Z * S) (v : Cube F) :
    rho F S (rho F X v) = rho F Z (rho F S v) := by
  rw [← rho_mul_apply, ← rho_mul_apply, h]

private theorem u6ML_det_conj (S s : GL (Fin 6) F) (hs : (s : Matrix (Fin 6) (Fin 6) F).det = 1) :
    ((S⁻¹ * s * S : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).det = 1 := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hs, mul_one,
    ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]

private theorem u6ML_rho_ne_zero (s : GL (Fin 6) F) {v : Cube F} (hv : v ≠ 0) :
    rho F s v ≠ 0 := by
  intro h
  apply hv
  have h2 : rho F s⁻¹ (rho F s v) = v := by
    rw [← rho_mul_apply, inv_mul_cancel, rho_one, Module.End.one_apply]
  rw [← h2, h, map_zero]

private theorem u6ML_val_add (x y : E3UWspace σ e) : e3uVal (x + y) = e3uVal x + e3uVal y := rfl

private theorem u6ML_val_sub (x y : E3UWspace σ e) : e3uVal (x - y) = e3uVal x - e3uVal y := rfl

private theorem u6ML_val_smul (c : K) (x : E3UWspace σ e) :
    e3uVal (c • x) = ((e c : Fσ σ) : F) • e3uVal x := rfl

private theorem u6ML_val_p0 : e3uVal (e3uP0 σ e) = pt0 F := rfl

private theorem u6ML_val_mem (x : E3UWspace σ e) : e3uVal x ∈ Wsub σ :=
  mem_Wform_iff.mp (show Wform σ from x).2

private theorem u6ML_inj {x y : E3UWspace σ e} (h : e3uVal x = e3uVal y) : x = y :=
  Subtype.ext h

private theorem u6ML_of_frame (hinv : ∀ c : F, σ (σ c) = c) (S : GL (Fin 6) F)
    (hSp : rho F S (p0 F) = pt0 F)
    (hSU : ∀ g : SUid σ 6, g ∈ e3uU0Sub σ → rhoEquiv F (S⁻¹ * (g : GL (Fin 6) F) * S) ∈ U0 F) :
    EGeom.MinuscLine (e3uGam σ e) (e3uP0 σ e) (e3uU0 σ e) := by
  refine ⟨fun g₁ hg₁ g₂ hg₂ g₃ hg₃ a b c ha hb hc h => ?_⟩
  obtain ⟨s₁, rfl⟩ := MonoidHom.mem_range.mp (show g₁ ∈ (e3uWact σ e).range from hg₁)
  obtain ⟨s₂, rfl⟩ := MonoidHom.mem_range.mp (show g₂ ∈ (e3uWact σ e).range from hg₂)
  obtain ⟨s₃, rfl⟩ := MonoidHom.mem_range.mp (show g₃ ∈ (e3uWact σ e).range from hg₃)
  have hea : ∀ x : K, x ≠ 0 → ((e x : Fσ σ) : F) ≠ 0 := by
    intro x hx h0
    apply hx
    apply e.injective
    rw [map_zero]
    exact Subtype.ext h0
  have hα := hea a ha
  have hβ := hea b hb
  have hγ := hea c hc
  have hrelC : ((e a : Fσ σ) : F) • rho F (s₁ : GL (Fin 6) F) (pt0 F) +
      ((e b : Fσ σ) : F) • rho F (s₂ : GL (Fin 6) F) (pt0 F) =
      ((e c : Fσ σ) : F) • rho F (s₃ : GL (Fin 6) F) (pt0 F) := by
    have h1 := congrArg e3uVal h
    simpa only [u6ML_val_add, u6ML_val_smul, e3uWact_val, u6ML_val_p0] using h1
  have hA : ∀ s : SUid σ 6, rhoEquiv F (S⁻¹ * (s : GL (Fin 6) F) * S) (p0 F) =
      rho F S⁻¹ (rho F (s : GL (Fin 6) F) (pt0 F)) := by
    intro s
    rw [rhoEquiv_apply, u6ML_rho_conj, hSp]
  have hrelL : ((e a : Fσ σ) : F) • rhoEquiv F (S⁻¹ * (s₁ : GL (Fin 6) F) * S) (p0 F) +
      ((e b : Fσ σ) : F) • rhoEquiv F (S⁻¹ * (s₂ : GL (Fin 6) F) * S) (p0 F) =
      ((e c : Fσ σ) : F) • rhoEquiv F (S⁻¹ * (s₃ : GL (Fin 6) F) * S) (p0 F) := by
    rw [hA s₁, hA s₂, hA s₃]
    have h1 := congrArg (rho F S⁻¹) hrelC
    simpa only [map_add, map_smul] using h1
  have hG : ∀ s : SUid σ 6, rhoEquiv F (S⁻¹ * (s : GL (Fin 6) F) * S) ∈ A5Cube.Gam F := fun s =>
    Subgroup.mem_map_of_mem (rhoEquiv F)
      (CFSG.Open.StatedAPI.mem_statedSL_of_det
        (u6ML_det_conj S (s : GL (Fin 6) F) (mem_SUid.mp s.2).1))
  have hline := (A5Cube.a5MinuscLine (K := F)).line_iff _ (hG s₁) _ (hG s₂) _ (hG s₃) _ _ _
    hα hβ hγ hrelL
  rw [EGeom.mem_Wsp]
  intro u hu
  obtain ⟨u₀, hu₀, rfl⟩ := EGeom.mem_conjSub.mp hu
  obtain ⟨g', hg', rfl⟩ :=
    Subgroup.mem_map.mp (show u₀ ∈ (e3uU0Sub σ).map (e3uWact σ e) from hu₀)
  have hU : e3uWact σ e s₁ * e3uWact σ e g' * (e3uWact σ e s₁)⁻¹ =
      e3uWact σ e (s₁ * g' * s₁⁻¹) := by
    simp only [map_mul, map_inv]
  have hYmem : rhoEquiv F ((S⁻¹ * (s₁ : GL (Fin 6) F) * S) * (S⁻¹ * (g' : GL (Fin 6) F) * S) *
      (S⁻¹ * (s₁ : GL (Fin 6) F) * S)⁻¹) ∈
      EGeom.conjSub (rhoEquiv F (S⁻¹ * (s₁ : GL (Fin 6) F) * S)) (A5Cube.U0 F) :=
    EGeom.mem_conjSub.mpr ⟨_, hSU g' hg', by simp only [map_mul, map_inv]⟩
  obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp (EGeom.mem_Wsp.mp hline _ hYmem)
  have hX : ∀ s : SUid σ 6, rho F S (rho F (S⁻¹ * (s : GL (Fin 6) F) * S) (p0 F)) =
      rho F (s : GL (Fin 6) F) (pt0 F) := by
    intro s
    have hc : S * (S⁻¹ * (s : GL (Fin 6) F) * S) = (s : GL (Fin 6) F) * S := by group
    rw [u6ML_rho_comm hc, hSp]
  have hkey : lam • rho F (s₁ : GL (Fin 6) F) (pt0 F) =
      rho F ((s₁ : GL (Fin 6) F) * (g' : GL (Fin 6) F) * (s₁ : GL (Fin 6) F)⁻¹)
        (rho F (s₂ : GL (Fin 6) F) (pt0 F)) - rho F (s₂ : GL (Fin 6) F) (pt0 F) := by
    have hSY : S * ((S⁻¹ * (s₁ : GL (Fin 6) F) * S) * (S⁻¹ * (g' : GL (Fin 6) F) * S) *
        (S⁻¹ * (s₁ : GL (Fin 6) F) * S)⁻¹) =
        ((s₁ : GL (Fin 6) F) * (g' : GL (Fin 6) F) * (s₁ : GL (Fin 6) F)⁻¹) * S := by
      group
    have h2 := congrArg (rho F S) hlam
    simp only [rhoEquiv_apply, map_smul, map_sub] at h2
    rw [hX s₁, u6ML_rho_comm hSY, hX s₂] at h2
    exact h2
  have hp0 : e3uVal (e3uWact σ e s₁ (e3uP0 σ e)) ≠ 0 := by
    rw [e3uWact_val, u6ML_val_p0]
    exact u6ML_rho_ne_zero _ U6Cube.pt0_ne_zero
  have hv1 : e3uVal (e3uWact σ e (s₁ * g' * s₁⁻¹) (e3uWact σ e s₂ (e3uP0 σ e)) -
      e3uWact σ e s₂ (e3uP0 σ e)) ∈ Wsub σ :=
    u6ML_val_mem _
  have hval : e3uVal (e3uWact σ e (s₁ * g' * s₁⁻¹) (e3uWact σ e s₂ (e3uP0 σ e)) -
      e3uWact σ e s₂ (e3uP0 σ e)) = lam • e3uVal (e3uWact σ e s₁ (e3uP0 σ e)) := by
    simp only [u6ML_val_sub, e3uWact_val, u6ML_val_p0, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hkey.symm
  have hσlam : σ lam = lam := smul_mem_Fq_of_mem_Wsub hinv hv1 (u6ML_val_mem _) hp0 hval
  have hσmem : lam ∈ Fσ σ := mem_Fσ_iff.mpr hσlam
  have hek : ((e (e.symm ⟨lam, hσmem⟩) : Fσ σ) : F) = lam :=
    congrArg Subtype.val (e.apply_symm_apply ⟨lam, hσmem⟩)
  rw [hU, Submodule.mem_span_singleton]
  refine ⟨e.symm ⟨lam, hσmem⟩, ?_⟩
  apply u6ML_inj
  rw [u6ML_val_smul, hek, hval]

theorem u6_MinuscLine (hσ : IsUnitaryInvolution σ) [Finite K] :
    MinuscLine (e3uGam σ e) (e3uP0 σ e) (e3uU0 σ e) := by
  obtain ⟨ω, hω⟩ := hσ.trace_surj 1 (map_one σ)
  refine u6ML_of_frame hσ.invol (frameGL σ ω hω) (rho_frameGL_p0 ω hω) (fun g hg => ?_)
  rw [U0_eq_Urad]
  exact Subgroup.mem_map_of_mem (rhoEquiv F) (frame_conj_unip_of_mem_U0Sub hσ hω hg)

theorem u6_MinuscGeom (hσ : IsUnitaryInvolution σ) [Finite K] (hF : Nat.card F = Nat.card K ^ 2) :
    MinuscGeom (e3uGam σ e) (e3uP0 σ e) (e3uU0 σ e) 10 := by
  refine ⟨?_, ?_, u6_U0_fix, u6_W_le hσ hF, u6_line hσ⟩
  · intro h
    apply pt0_ne_zero (K := F)
    rw [← u6ML_val_p0 (σ := σ) (e := e), h]
    rfl
  · exact Subgroup.map_le_range _ _

end CFSG.RankThree.GF2n.Smith81

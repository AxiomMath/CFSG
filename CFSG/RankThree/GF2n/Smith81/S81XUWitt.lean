module

public import CFSG.RankThree.GF2n.Smith81.S81UTrans

public section

namespace CFSG.RankThree.GF2n.Smith81.U6Cube

open CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.A5Cube Matrix exteriorPower
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}

private theorem u6w_det_conjTr (M : Matrix (Fin 6) (Fin 6) F) : (conjTr σ M).det = σ M.det := by
  rw [conjTr, Matrix.det_transpose]
  exact (RingHom.map_det σ.toRingHom M).symm

private theorem u6w_sigma_det (M : Matrix (Fin 6) (Fin 6) F) (hM : conjTr σ M * M = 1) :
    σ M.det * M.det = 1 := by
  have h := congrArg Matrix.det hM
  rw [Matrix.det_mul, u6w_det_conjTr, Matrix.det_one] at h
  exact h

private theorem u6w_hilbert90 (hσ : IsUnitaryInvolution σ) {d : F} (hd : σ d * d = 1) :
    ∃ l : F, l ≠ 0 ∧ σ l = d * l := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hL : ∀ a : F, σ (a + σ (d * a)) = d * (a + σ (d * a)) := by
    intro a
    simp only [map_add, map_mul, hσ.invol]
    linear_combination (-(σ a)) * hd
  have hex : ∃ a : F, a + σ (d * a) ≠ 0 := by
    by_contra hne
    have hall : ∀ a : F, a + σ (d * a) = 0 := fun a => by
      by_contra h
      exact hne ⟨a, h⟩
    have h1 : σ d = 1 := by
      have h := hall 1
      rw [mul_one] at h
      linear_combination h - h2
    have hd1 : d = 1 := by
      rw [h1, one_mul] at hd
      exact hd
    obtain ⟨c, hc⟩ := hσ.exists_ne
    have h := hall c
    rw [hd1, one_mul] at h
    exact hc (by linear_combination h - c * h2)
  obtain ⟨a, ha⟩ := hex
  exact ⟨a + σ (d * a), ha, hL a⟩

private noncomputable def u6w_T (τ : F ≃+* F) (l : F) : Fin 6 → F :=
  ![l, (τ l)⁻¹, 1, 1, 1, 1]

private theorem u6w_T_ne {l : F} (hl0 : l ≠ 0) : ∀ k, u6w_T σ l k ≠ 0 := by
  have hσl0 : σ l ≠ 0 := (map_ne_zero σ).mpr hl0
  intro k
  fin_cases k <;> simp [u6w_T, hl0, hσl0]

private noncomputable def u6w_diag (t : Fin 6 → F) (ht : ∀ k, t k ≠ 0) : GL (Fin 6) F where
  val := Matrix.diagonal t
  inv := Matrix.diagonal fun k => (t k)⁻¹
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    exact mul_inv_cancel₀ (ht k)
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    exact inv_mul_cancel₀ (ht k)

private noncomputable def u6w_D (ω : F) (hω : ω + σ ω = 1) (t : Fin 6 → F)
    (ht : ∀ k, t k ≠ 0) : GL (Fin 6) F :=
  frameGL σ ω hω * u6w_diag t ht * (frameGL σ ω hω)⁻¹

private theorem u6w_D_val (ω : F) (hω : ω + σ ω = 1) (t : Fin 6 → F) (ht : ∀ k, t k ≠ 0) :
    ((u6w_D ω hω t ht : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      frameMat σ ω * Matrix.diagonal t * frameInv σ ω := by
  rw [u6w_D, Units.val_mul, Units.val_mul]
  rfl

private theorem u6w_D_mulVec (ω : F) (hω : ω + σ ω = 1) (t : Fin 6 → F) (ht : ∀ k, t k ≠ 0)
    (j : Fin 3) :
    ((u6w_D ω hω t ht : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec j) =
      t ⟨2 * j.val, by omega⟩ • e3uT0Vec j := by
  have hp : (frameInv σ ω).mulVec (e3uT0Vec j) =
      Pi.single (⟨2 * j.val, by omega⟩ : Fin 6) (1 : F) := by
    rw [← frameMat_mulVec_even (σ := σ) ω j, Matrix.mulVec_mulVec, frameInv_mul_frameMat hω,
      Matrix.one_mulVec]
  have hd : (Matrix.diagonal t).mulVec (Pi.single (⟨2 * j.val, by omega⟩ : Fin 6) (1 : F)) =
      t ⟨2 * j.val, by omega⟩ • Pi.single (⟨2 * j.val, by omega⟩ : Fin 6) (1 : F) := by
    funext i
    by_cases h : i = ⟨2 * j.val, by omega⟩
    · subst h
      simp [Matrix.mulVec_diagonal]
    · simp [Matrix.mulVec_diagonal, Pi.single_apply, h]
  rw [u6w_D_val, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hp, hd, Matrix.mulVec_smul,
    frameMat_mulVec_even (σ := σ) ω j]

private theorem u6w_D_det (ω : F) (hω : ω + σ ω = 1) (t : Fin 6 → F) (ht : ∀ k, t k ≠ 0) :
    ((u6w_D ω hω t ht : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).det = ∏ k, t k := by
  rw [u6w_D_val, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  have hdd : (frameMat σ ω).det * (frameInv σ ω).det = 1 := by
    rw [← Matrix.det_mul, frameMat_mul_frameInv hω, Matrix.det_one]
  calc (frameMat σ ω).det * (∏ k, t k) * (frameInv σ ω).det
      = (∏ k, t k) * ((frameMat σ ω).det * (frameInv σ ω).det) := by ring
    _ = ∏ k, t k := by rw [hdd, mul_one]

private theorem u6w_frame_unit (hσ : ∀ c, σ (σ c) = c) {ω : F} (hω : ω + σ ω = 1)
    {M : Matrix (Fin 6) (Fin 6) F} (hM : conjTr σ M * hypGram F * M = hypGram F) :
    conjTr σ (frameMat σ ω * M * frameInv σ ω) * (frameMat σ ω * M * frameInv σ ω) = 1 := by
  have hS : frameMat σ ω * frameInv σ ω = 1 := frameMat_mul_frameInv hω
  have hG : conjTr σ (frameMat σ ω) * frameMat σ ω = hypGram F := conjTr_frameMat_mul hσ hω
  calc conjTr σ (frameMat σ ω * M * frameInv σ ω) * (frameMat σ ω * M * frameInv σ ω)
      = conjTr σ (frameInv σ ω) * (conjTr σ M * (conjTr σ (frameMat σ ω) * frameMat σ ω) * M) *
          frameInv σ ω := by
        simp only [conjTr_mul, Matrix.mul_assoc]
    _ = conjTr σ (frameInv σ ω) * (conjTr σ M * hypGram F * M) * frameInv σ ω := by rw [hG]
    _ = conjTr σ (frameInv σ ω) * hypGram F * frameInv σ ω := by rw [hM]
    _ = conjTr σ (frameInv σ ω) * (conjTr σ (frameMat σ ω) * frameMat σ ω) * frameInv σ ω := by
        rw [hG]
    _ = conjTr σ (frameMat σ ω * frameInv σ ω) * (frameMat σ ω * frameInv σ ω) := by
        simp only [conjTr_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hS, conjTr_one, Matrix.one_mul]

private theorem u6w_D_unit (hσ : ∀ c, σ (σ c) = c) {ω : F} (hω : ω + σ ω = 1) (t : Fin 6 → F)
    (ht : ∀ k, t k ≠ 0)
    (hM : conjTr σ (Matrix.diagonal t) * hypGram F * Matrix.diagonal t = hypGram F) :
    conjTr σ ((u6w_D ω hω t ht : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
      ((u6w_D ω hω t ht : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = 1 := by
  rw [u6w_D_val]
  exact u6w_frame_unit hσ hω hM

private theorem u6w_gram (hσ : ∀ c, σ (σ c) = c) {l : F} (hl0 : l ≠ 0) :
    conjTr σ (Matrix.diagonal (u6w_T σ l)) * hypGram F * Matrix.diagonal (u6w_T σ l) =
      hypGram F := by
  have hσl0 : σ l ≠ 0 := (map_ne_zero σ).mpr hl0
  have hc : conjTr σ (Matrix.diagonal (u6w_T σ l)) =
      Matrix.diagonal (fun k => σ (u6w_T σ l k)) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [conjTr_apply]
    · simp [conjTr_apply, Matrix.diagonal_apply, h, Ne.symm h]
  rw [hc]
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;>
    simp [u6w_T, hypGram, hσ, hσl0, hl0, map_inv₀, mul_inv_cancel₀, inv_mul_cancel₀]

theorem u6_exists_su_of_ti (hσ : IsUnitaryInvolution σ) {v : Fin 3 → Fin 6 → F}
    (hv : ιMulti F 3 v ≠ 0) (hiso : ∀ i j, ∑ k, σ (v i k) * v j k = 0) :
    ∃ g : SUid σ 6, ∃ l : F, l ≠ 0 ∧
      ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec 0) = l • v 0 ∧
      ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec 1) = v 1 ∧
      ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec 2) = v 2 := by
  obtain ⟨w, hvw, hww⟩ := exists_hyperbolic_partners hσ hv hiso
  obtain ⟨ω, hω⟩ := hσ.trace_surj 1 (map_one σ)
  obtain ⟨g₀, hg₀, hgv⟩ := exists_unitary_of_hyp hσ hω hiso hvw hww
  obtain ⟨l, hl0, hlσ⟩ := u6w_hilbert90 hσ (u6w_sigma_det _ hg₀)
  have hσl0 : σ l ≠ 0 := (map_ne_zero σ).mpr hl0
  have hT : ∀ k, u6w_T σ l k ≠ 0 := u6w_T_ne hl0
  obtain ⟨D, hDdef⟩ : ∃ D : GL (Fin 6) F, D = u6w_D ω hω (u6w_T σ l) hT := ⟨_, rfl⟩
  have hDe : ∀ j : Fin 3, (D : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec j) =
      u6w_T σ l ⟨2 * j.val, by omega⟩ • e3uT0Vec j := by
    intro j
    rw [hDdef]
    exact u6w_D_mulVec ω hω (u6w_T σ l) hT j
  have hDd : (D : Matrix (Fin 6) (Fin 6) F).det = ∏ k, u6w_T σ l k := by
    rw [hDdef]
    exact u6w_D_det ω hω (u6w_T σ l) hT
  have hDu : conjTr σ (D : Matrix (Fin 6) (Fin 6) F) * (D : Matrix (Fin 6) (Fin 6) F) = 1 := by
    rw [hDdef]
    exact u6w_D_unit hσ.invol hω (u6w_T σ l) hT (u6w_gram hσ.invol hl0)
  have hprod : ∏ k, u6w_T σ l k = l * (σ l)⁻¹ := by
    simp [Fin.prod_univ_six, u6w_T]
  have hkey : (g₀ : Matrix (Fin 6) (Fin 6) F).det * (l * (σ l)⁻¹) = 1 := by
    calc (g₀ : Matrix (Fin 6) (Fin 6) F).det * (l * (σ l)⁻¹)
        = ((g₀ : Matrix (Fin 6) (Fin 6) F).det * l) * (σ l)⁻¹ := by ring
      _ = σ l * (σ l)⁻¹ := by rw [← hlσ]
      _ = 1 := mul_inv_cancel₀ hσl0
  have hdet : ((g₀ * D : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).det = 1 := by
    rw [Units.val_mul, Matrix.det_mul, hDd, hprod]
    exact hkey
  have hunit : conjTr σ ((g₀ * D : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
      ((g₀ * D : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = 1 := by
    rw [Units.val_mul]
    calc conjTr σ ((g₀ : Matrix (Fin 6) (Fin 6) F) * (D : Matrix (Fin 6) (Fin 6) F)) *
          ((g₀ : Matrix (Fin 6) (Fin 6) F) * (D : Matrix (Fin 6) (Fin 6) F))
        = conjTr σ (D : Matrix (Fin 6) (Fin 6) F) *
            (conjTr σ (g₀ : Matrix (Fin 6) (Fin 6) F) * (g₀ : Matrix (Fin 6) (Fin 6) F)) *
              (D : Matrix (Fin 6) (Fin 6) F) := by
          simp only [conjTr_mul, Matrix.mul_assoc]
      _ = conjTr σ (D : Matrix (Fin 6) (Fin 6) F) * (D : Matrix (Fin 6) (Fin 6) F) := by
          rw [hg₀, Matrix.mul_one]
      _ = 1 := hDu
  have hD0 : (D : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec 0) = l • e3uT0Vec 0 := hDe 0
  have hD1 : (D : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec 1) = e3uT0Vec 1 := by
    rw [hDe 1]
    exact one_smul F _
  have hD2 : (D : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec 2) = e3uT0Vec 2 := by
    rw [hDe 2]
    exact one_smul F _
  refine ⟨⟨g₀ * D, CFSG.LieType.Universal.Unitary.mem_SUid.mpr ⟨hdet, hunit⟩⟩, l, hl0, ?_, ?_, ?_⟩
  · show ((g₀ * D : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec 0) = l • v 0
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hD0, Matrix.mulVec_smul, hgv 0]
  · show ((g₀ * D : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec 1) = v 1
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hD1, hgv 1]
  · show ((g₀ * D : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec 2) = v 2
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hD2, hgv 2]

end CFSG.RankThree.GF2n.Smith81.U6Cube

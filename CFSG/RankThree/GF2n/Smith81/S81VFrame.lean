module

public import CFSG.RankThree.GF2n.Smith81.S81VGeomD3a

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary Module Matrix

variable {F : Type} [Field F] {σ : F ≃+* F} {a b : Fin 3 → Fin 6 → F}

@[expose] def cT (σ : F ≃+* F) {ι : Type} (M : Matrix ι ι F) : Matrix ι ι F := (M.map σ).transpose

theorem cT_apply {ι : Type} (M : Matrix ι ι F) (i j : ι) : cT σ M i j = σ (M j i) := rfl

theorem cT_mul {ι : Type} [Fintype ι] (M N : Matrix ι ι F) : cT σ (M * N) = cT σ N * cT σ M := by
  ext i j
  simp only [cT_apply, Matrix.mul_apply, map_sum, map_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem cT_one {ι : Type} [DecidableEq ι] : cT σ (1 : Matrix ι ι F) = 1 := by
  ext i j
  rw [cT_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem cT_add {ι : Type} (M N : Matrix ι ι F) : cT σ (M + N) = cT σ M + cT σ N := by
  ext i j
  simp [cT_apply]

theorem cT_smul {ι : Type} (c : F) (M : Matrix ι ι F) : cT σ (c • M) = σ c • cT σ M := by
  ext i j
  simp [cT_apply, map_mul]

theorem cT_cT (hσ : ∀ c, σ (σ c) = c) {ι : Type} (M : Matrix ι ι F) : cT σ (cT σ M) = M := by
  ext i j
  simp [cT_apply, hσ]

theorem det_cT {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι F) :
    (cT σ M).det = σ M.det := by
  rw [cT, Matrix.det_transpose]
  exact (RingHom.map_det σ.toRingHom M).symm

theorem cT_fromBlocks (A B C D : Matrix (Fin 3) (Fin 3) F) :
    cT σ (Matrix.fromBlocks A B C D) = Matrix.fromBlocks (cT σ A) (cT σ C) (cT σ B) (cT σ D) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [cT_apply]

@[expose] def fam (a b : Fin 3 → Fin 6 → F) : Fin 3 ⊕ Fin 3 → (Fin 6 → F) := Sum.elim a b

@[expose] def Jm (F : Type) [Field F] : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F :=
  Matrix.fromBlocks 0 1 1 0

private theorem fam_inl (i : Fin 3) : fam a b (Sum.inl i) = a i := rfl

private theorem fam_inr (i : Fin 3) : fam a b (Sum.inr i) = b i := rfl

private theorem herm_sum_right_S {ι : Type*} (s : Finset ι) (x : Fin 6 → F) (f : ι → Fin 6 → F) :
    herm σ x (∑ i ∈ s, f i) = ∑ i ∈ s, herm σ x (f i) :=
  map_sum (hermL σ x) f s

private theorem herm_ba_S (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) (i j : Fin 3) :
    herm σ (b i) (a j) = if i = j then 1 else 0 := by
  rw [herm_conj σ hσ (a j) (b i), hf.ab j i]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem herm_fam (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) (p q : Fin 3 ⊕ Fin 3) :
    herm σ (fam a b p) (fam a b q) = Jm F p q := by
  rcases p with i | i <;> rcases q with j | j
  · simp only [fam_inl, Jm, Matrix.fromBlocks_apply₁₁, Matrix.zero_apply]
    exact hf.aa i j
  · simp only [fam_inl, fam_inr, Jm, Matrix.fromBlocks_apply₁₂, Matrix.one_apply]
    exact hf.ab i j
  · simp only [fam_inl, fam_inr, Jm, Matrix.fromBlocks_apply₂₁, Matrix.one_apply]
    exact herm_ba_S hσ hf i j
  · simp only [fam_inr, Jm, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
    exact hf.bb i j

theorem fam_li (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) : LinearIndependent F (fam a b) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hq : ∀ q, ∑ p, c p * Jm F q p = 0 := by
    intro q
    have h1 := congrArg (herm σ (fam a b q)) hc
    rw [herm_zero_right, herm_sum_right_S] at h1
    simpa only [herm_smul_right, herm_fam hσ hf] using h1
  have hinl : ∀ j, c (Sum.inl j) = 0 := by
    intro j
    have h := hq (Sum.inr j)
    rw [Fintype.sum_sum_type] at h
    simpa [Jm, Matrix.one_apply] using h
  have hinr : ∀ j, c (Sum.inr j) = 0 := by
    intro j
    have h := hq (Sum.inl j)
    rw [Fintype.sum_sum_type] at h
    simpa [Jm, Matrix.one_apply] using h
  intro p
  rcases p with j | j
  · exact hinl j
  · exact hinr j

noncomputable def fb (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) :
    Basis (Fin 3 ⊕ Fin 3) F (Fin 6 → F) :=
  basisOfLinearIndependentOfCardEqFinrank (fam_li hσ hf) (by simp)

theorem fb_apply (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) (p : Fin 3 ⊕ Fin 3) :
    fb hσ hf p = fam a b p := by
  rw [fb, coe_basisOfLinearIndependentOfCardEqFinrank]

theorem repr_inl (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) (x : Fin 6 → F) (i : Fin 3) :
    (fb hσ hf).repr x (Sum.inl i) = herm σ (b i) x := by
  have hx : ∑ p, (fb hσ hf).repr x p • fam a b p = x := by
    simpa only [fb_apply] using (fb hσ hf).sum_repr x
  have hJ : ∀ p, herm σ (b i) (fam a b p) = Jm F (Sum.inr i) p :=
    fun p => herm_fam hσ hf (Sum.inr i) p
  have h1 : herm σ (b i) x = ∑ p, (fb hσ hf).repr x p * Jm F (Sum.inr i) p := by
    conv_lhs => rw [← hx]
    rw [herm_sum_right_S]
    exact Finset.sum_congr rfl fun p _ => by rw [herm_smul_right, hJ]
  rw [h1, Fintype.sum_sum_type]
  simp [Jm, Matrix.one_apply]

theorem repr_inr (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) (x : Fin 6 → F) (i : Fin 3) :
    (fb hσ hf).repr x (Sum.inr i) = herm σ (a i) x := by
  have hx : ∑ p, (fb hσ hf).repr x p • fam a b p = x := by
    simpa only [fb_apply] using (fb hσ hf).sum_repr x
  have hJ : ∀ p, herm σ (a i) (fam a b p) = Jm F (Sum.inl i) p :=
    fun p => herm_fam hσ hf (Sum.inl i) p
  have h1 : herm σ (a i) x = ∑ p, (fb hσ hf).repr x p * Jm F (Sum.inl i) p := by
    conv_lhs => rw [← hx]
    rw [herm_sum_right_S]
    exact Finset.sum_congr rfl fun p _ => by rw [herm_smul_right, hJ]
  rw [h1, Fintype.sum_sum_type]
  simp [Jm, Matrix.one_apply]

theorem herm_eq_coords (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) (x y : Fin 6 → F) :
    herm σ x y = (fun p => σ ((fb hσ hf).repr x p)) ⬝ᵥ (Jm F *ᵥ (fb hσ hf).repr y) := by
  have hx : ∑ p, (fb hσ hf).repr x p • fam a b p = x := by
    simpa only [fb_apply] using (fb hσ hf).sum_repr x
  have hy : ∑ p, (fb hσ hf).repr y p • fam a b p = y := by
    simpa only [fb_apply] using (fb hσ hf).sum_repr y
  have step2 : ∀ p, herm σ (fam a b p) y = ∑ q, (fb hσ hf).repr y q * Jm F p q := by
    intro p
    conv_lhs => rw [← hy]
    rw [herm_sum_right_S]
    exact Finset.sum_congr rfl fun q _ => by rw [herm_smul_right, herm_fam hσ hf]
  have step1 : herm σ x y = ∑ p, σ ((fb hσ hf).repr x p) * herm σ (fam a b p) y := by
    have h2 : herm σ y x = ∑ p, (fb hσ hf).repr x p * herm σ y (fam a b p) := by
      conv_lhs => rw [← hx]
      rw [herm_sum_right_S]
      exact Finset.sum_congr rfl fun p _ => herm_smul_right σ _ _ _
    have h3 : ∀ p, σ (herm σ y (fam a b p)) = herm σ (fam a b p) y := fun p => by
      rw [herm_conj σ hσ (fam a b p) y, hσ]
    rw [herm_conj σ hσ y x, h2, map_sum]
    exact Finset.sum_congr rfl fun p _ => by rw [map_mul, h3]
  rw [step1]
  simp only [dotProduct, Matrix.mulVec, step2]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  exact Finset.sum_congr rfl fun q _ => mul_comm _ _

end CFSG.RankThree.GF2n.Smith81.S81V

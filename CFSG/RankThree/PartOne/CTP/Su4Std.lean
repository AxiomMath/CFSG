module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Universal.Unitary.Basic

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.LieType.Universal.Unitary
open scoped MatrixGroups

variable {K : Type} [Field K] (σ : K ≃+* K)

abbrev matS {n : ℕ} (g : SU σ n) : Matrix (Fin n) (Fin n) K :=
  ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

variable {σ}

theorem matS_det {n : ℕ} (g : SU σ n) : (matS σ g).det = 1 := g.2.1

theorem matS_iso {n : ℕ} (g : SU σ n) :
    conjTr σ (matS σ g) * antidiag n * matS σ g = antidiag n := g.2.2

theorem matS_mul {n : ℕ} (g h : SU σ n) : matS σ (g * h) = matS σ g * matS σ h := rfl

theorem matS_one {n : ℕ} : matS σ (1 : SU σ n) = 1 := rfl

theorem matS_inv_mul {n : ℕ} (g : SU σ n) : matS σ g⁻¹ * matS σ g = 1 := by
  rw [← matS_mul, inv_mul_cancel, matS_one]

@[expose] def stabVec {n : ℕ} (σ : K ≃+* K) (v : Fin n → K) : Subgroup (SU σ n) where
  carrier := {g | matS σ g *ᵥ v = v}
  one_mem' := by simp [matS_one]
  mul_mem' := fun {g h} hg hh => by
    show matS σ (g * h) *ᵥ v = v
    rw [matS_mul, ← mulVec_mulVec, hh.out, hg.out]
  inv_mem' := fun {g} hg => by
    show matS σ g⁻¹ *ᵥ v = v
    have h1 : matS σ g *ᵥ v = v := hg
    calc matS σ g⁻¹ *ᵥ v = matS σ g⁻¹ *ᵥ (matS σ g *ᵥ v) := by rw [h1]
      _ = (matS σ g⁻¹ * matS σ g) *ᵥ v := by rw [mulVec_mulVec]
      _ = v := by rw [matS_inv_mul, one_mulVec]

theorem mem_stabVec {n : ℕ} {v : Fin n → K} {g : SU σ n} :
    g ∈ stabVec σ v ↔ matS σ g *ᵥ v = v := Iff.rfl

@[expose] def embMid (N : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, N 0 0, N 0 1, 0; 0, N 1 0, N 1 1, 0; 0, 0, 0, 1]

theorem det_embMid (N : Matrix (Fin 2) (Fin 2) K) : (embMid N).det = N.det := by
  rw [Matrix.det_fin_two]
  simp [embMid, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  ring

@[expose] def midBlock (M : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 2) (Fin 2) K :=
  !![M 1 1, M 1 2; M 2 1, M 2 2]

theorem midBlock_embMid (N : Matrix (Fin 2) (Fin 2) K) : midBlock (embMid N) = N := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [midBlock, embMid]

theorem eq_embMid_of_fix (g : SU σ 4) (h0 : g ∈ stabVec σ (Pi.single 0 1))
    (h3 : g ∈ stabVec σ (Pi.single 3 1)) : matS σ g = embMid (midBlock (matS σ g)) := by
  have c0 : ∀ i, matS σ g i 0 = if i = 0 then 1 else 0 := by
    intro i
    have := congrFun (mem_stabVec.mp h0) i
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at this
    simpa [Pi.single_apply] using this
  have c3 : ∀ i, matS σ g i 3 = if i = 3 then 1 else 0 := by
    intro i
    have := congrFun (mem_stabVec.mp h3) i
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at this
    simpa [Pi.single_apply] using this
  have iso := matS_iso g
  have e01 := congrFun (congrFun iso 0) 1
  have e02 := congrFun (congrFun iso 0) 2
  have e31 := congrFun (congrFun iso 3) 1
  have e32 := congrFun (congrFun iso 3) 2
  simp [conjTr, Matrix.mul_apply, Fin.sum_univ_four, antidiag, Fin.rev, c0, c3] at e01 e02 e31 e32
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embMid, midBlock, c0, c3] <;> simp_all

theorem iso_midBlock (g : SU σ 4) (h0 : g ∈ stabVec σ (Pi.single 0 1))
    (h3 : g ∈ stabVec σ (Pi.single 3 1)) :
    conjTr σ (midBlock (matS σ g)) * antidiag 2 * midBlock (matS σ g) = antidiag 2 := by
  have heq := eq_embMid_of_fix g h0 h3
  have hiso := matS_iso g
  generalize midBlock (matS σ g) = N at heq ⊢
  rw [heq] at hiso
  ext j k
  have e11 := congrFun (congrFun hiso 1) 1
  have e12 := congrFun (congrFun hiso 1) 2
  have e21 := congrFun (congrFun hiso 2) 1
  have e22 := congrFun (congrFun hiso 2) 2
  fin_cases j <;> fin_cases k <;>
    simp [conjTr, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, antidiag, Fin.rev,
      embMid] at e11 e12 e21 e22 ⊢ <;> simp_all

@[expose] noncomputable def lbElt (N : SU σ 2) : SU σ 4 :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (embMid (matS σ N)) (by
      rw [det_embMid, matS_det]
      exact one_ne_zero), by
    refine ⟨?_, ?_⟩
    · show (embMid (matS σ N)).det = 1
      rw [det_embMid, matS_det]
    · show conjTr σ (embMid (matS σ N)) * antidiag 4 * embMid (matS σ N) = antidiag 4
      have hiso := matS_iso N
      have e00 := congrFun (congrFun hiso 0) 0
      have e01 := congrFun (congrFun hiso 0) 1
      have e10 := congrFun (congrFun hiso 1) 0
      have e11 := congrFun (congrFun hiso 1) 1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [conjTr, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, antidiag, Fin.rev,
          embMid] at e00 e01 e10 e11 ⊢ <;> simp_all⟩

theorem matS_lbElt (N : SU σ 2) : matS σ (lbElt N) = embMid (matS σ N) := rfl

theorem embMid_mul (N N' : Matrix (Fin 2) (Fin 2) K) : embMid (N * N') = embMid N * embMid N' := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embMid, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

@[expose] noncomputable def lbEmb (σ : K ≃+* K) : SU σ 2 →* SU σ 4 where
  toFun := lbElt
  map_one' := by
    refine Subtype.ext (Units.ext ?_)
    show embMid (matS σ (1 : SU σ 2)) = matS σ (1 : SU σ 4)
    rw [matS_one, matS_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [embMid]
  map_mul' N N' := by
    refine Subtype.ext (Units.ext ?_)
    show embMid (matS σ (N * N')) = matS σ (lbElt N) * matS σ (lbElt N')
    rw [matS_mul, embMid_mul]
    rfl

theorem lbEmb_injective : Function.Injective (lbEmb σ) := by
  intro N N' h
  have h1 := congrArg (fun g : SU σ 4 => midBlock (matS σ g)) h
  simp only [lbEmb, MonoidHom.coe_mk, OneHom.coe_mk, matS_lbElt, midBlock_embMid] at h1
  exact Subtype.ext (Units.ext h1)

theorem mem_range_lbEmb_of_fix (g : SU σ 4) (h0 : g ∈ stabVec σ (Pi.single 0 1))
    (h3 : g ∈ stabVec σ (Pi.single 3 1)) : g ∈ (lbEmb σ).range := by
  have hdet : (midBlock (matS σ g)).det = 1 := by
    rw [← det_embMid, ← eq_embMid_of_fix g h0 h3, matS_det]
  refine ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (midBlock (matS σ g))
      (by rw [hdet]; exact one_ne_zero), hdet, iso_midBlock g h0 h3⟩, ?_⟩
  refine Subtype.ext (Units.ext ?_)
  show embMid (midBlock (matS σ g)) = matS σ g
  exact (eq_embMid_of_fix g h0 h3).symm

@[expose] def sbMat (σ : K ≃+* K) (N : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  !![N 0 0, N 0 1, 0, 0; N 1 0, N 1 1, 0, 0; 0, 0, σ (N 0 0), -σ (N 0 1);
    0, 0, -σ (N 1 0), σ (N 1 1)]

theorem det_sbMat (σ : K ≃+* K) (N : Matrix (Fin 2) (Fin 2) K) :
    (sbMat σ N).det = N.det * σ N.det := by
  rw [Matrix.det_fin_two, map_sub, map_mul, map_mul]
  simp [sbMat, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem sbMat_mul (σ : K ≃+* K) (N N' : Matrix (Fin 2) (Fin 2) K) :
    sbMat σ (N * N') = sbMat σ N * sbMat σ N' := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sbMat, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, map_add, map_mul] <;> ring1

theorem sbMat_iso (σ : K ≃+* K) (hσ : ∀ c, σ (σ c) = c) (N : SL(2, K)) :
    conjTr σ (sbMat σ (N : Matrix (Fin 2) (Fin 2) K)) * antidiag 4 *
      sbMat σ (N : Matrix (Fin 2) (Fin 2) K) = antidiag 4 := by
  have hdet : (N : Matrix (Fin 2) (Fin 2) K) 0 0 * (N : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (N : Matrix (Fin 2) (Fin 2) K) 0 1 * (N : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
    have := N.2
    rwa [Matrix.det_fin_two] at this
  have hdetσ := congrArg σ hdet
  simp only [map_sub, map_mul, map_one] at hdetσ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, sbMat, Matrix.mul_apply, Fin.sum_univ_four, antidiag, Fin.rev, hσ] <;>
    first | ring1 | linear_combination hdetσ | linear_combination (-1 : K) * hdetσ |
      linear_combination hdet

@[expose] noncomputable def sbElt (σ : K ≃+* K) (hσ : ∀ c, σ (σ c) = c) (N : SL(2, K)) :
    SU σ 4 :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (sbMat σ (N : Matrix (Fin 2) (Fin 2) K)) (by
      rw [det_sbMat, N.2, map_one, one_mul]
      exact one_ne_zero), by
    refine ⟨?_, sbMat_iso σ hσ N⟩
    show (sbMat σ (N : Matrix (Fin 2) (Fin 2) K)).det = 1
    rw [det_sbMat, N.2, map_one, one_mul]⟩

theorem matS_sbElt (σ : K ≃+* K) (hσ : ∀ c, σ (σ c) = c) (N : SL(2, K)) :
    matS σ (sbElt σ hσ N) = sbMat σ (N : Matrix (Fin 2) (Fin 2) K) := rfl

@[expose] noncomputable def sbEmb (σ : K ≃+* K) (hσ : ∀ c, σ (σ c) = c) :
    SL(2, K) →* SU σ 4 where
  toFun := sbElt σ hσ
  map_one' := by
    refine Subtype.ext (Units.ext ?_)
    show sbMat σ (1 : Matrix (Fin 2) (Fin 2) K) = matS σ (1 : SU σ 4)
    rw [matS_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sbMat]
  map_mul' N N' := by
    refine Subtype.ext (Units.ext ?_)
    show sbMat σ ((N : Matrix (Fin 2) (Fin 2) K) * N') =
      matS σ (sbElt σ hσ N) * matS σ (sbElt σ hσ N')
    rw [sbMat_mul]
    rfl

@[expose] def ulBlock (M : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 2) (Fin 2) K :=
  !![M 0 0, M 0 1; M 1 0, M 1 1]

theorem sbEmb_injective (σ : K ≃+* K) (hσ : ∀ c, σ (σ c) = c) :
    Function.Injective (sbEmb σ hσ) := by
  intro N N' h
  have h1 := congrArg (fun g : SU σ 4 => ulBlock (matS σ g)) h
  simp only [sbEmb, MonoidHom.coe_mk, OneHom.coe_mk, matS_sbElt] at h1
  refine Subtype.ext ?_
  ext i j
  have := congrFun (congrFun h1 i) j
  fin_cases i <;> fin_cases j <;> simpa [ulBlock, sbMat] using this

theorem solve_lower {α β γ δ x y z w : K} (hΔ : α * δ - β * γ = 1) (e02 : α * z + γ * x = 0)
    (e03 : α * w + γ * y = 1) (e12 : β * z + δ * x = 1) (e13 : β * w + δ * y = 0) :
    x = α ∧ y = -β ∧ z = -γ ∧ w = δ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (-β) * e02 + α * e12 - x * hΔ
  · linear_combination (-β) * e03 + α * e13 - y * hΔ
  · linear_combination δ * e02 - γ * e12 - z * hΔ
  · linear_combination δ * e03 - γ * e13 - w * hΔ

theorem mem_range_sbEmb_of_blk (σ : K ≃+* K) (hσ : ∀ c, σ (σ c) = c) (g : SU σ 4)
    (hblk : ∀ i j : Fin 4, (i.val < 2 ↔ ¬ j.val < 2) → matS σ g i j = 0)
    (hdet : (ulBlock (matS σ g)).det = 1) : g ∈ (sbEmb σ hσ).range := by
  have b20 : matS σ g 2 0 = 0 := hblk 2 0 (by decide)
  have b21 : matS σ g 2 1 = 0 := hblk 2 1 (by decide)
  have b30 : matS σ g 3 0 = 0 := hblk 3 0 (by decide)
  have b31 : matS σ g 3 1 = 0 := hblk 3 1 (by decide)
  have b02 : matS σ g 0 2 = 0 := hblk 0 2 (by decide)
  have b03 : matS σ g 0 3 = 0 := hblk 0 3 (by decide)
  have b12 : matS σ g 1 2 = 0 := hblk 1 2 (by decide)
  have b13 : matS σ g 1 3 = 0 := hblk 1 3 (by decide)
  have hiso := matS_iso g
  have e02 := congrFun (congrFun hiso 0) 2
  have e03 := congrFun (congrFun hiso 0) 3
  have e12 := congrFun (congrFun hiso 1) 2
  have e13 := congrFun (congrFun hiso 1) 3
  simp [conjTr, Matrix.mul_apply, Fin.sum_univ_four, antidiag, Fin.rev, b20, b21, b30, b31, b02,
    b03, b12, b13] at e02 e03 e12 e13
  have hΔ : σ (matS σ g 0 0) * σ (matS σ g 1 1) - σ (matS σ g 0 1) * σ (matS σ g 1 0) = 1 := by
    have := congrArg σ hdet
    simp only [ulBlock, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, map_sub, map_mul,
      map_one] at this
    exact this
  obtain ⟨hx, hy, hz, hw⟩ := solve_lower (α := σ (matS σ g 0 0)) (β := σ (matS σ g 0 1))
    (γ := σ (matS σ g 1 0)) (δ := σ (matS σ g 1 1)) (x := matS σ g 2 2) (y := matS σ g 2 3)
    (z := matS σ g 3 2) (w := matS σ g 3 3) hΔ (by linear_combination e02)
    (by linear_combination e03) (by linear_combination e12) (by linear_combination e13)
  refine ⟨⟨ulBlock (matS σ g), hdet⟩, ?_⟩
  refine Subtype.ext (Units.ext ?_)
  show sbMat σ (ulBlock (matS σ g)) = matS σ g
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sbMat, ulBlock, hx, hy, hz, hw, b20, b21, b30, b31, b02, b03, b12, b13]

theorem natCard_range_lbEmb : Nat.card (lbEmb σ).range = Nat.card (SU σ 2) :=
  (Nat.card_congr (MonoidHom.ofInjective (lbEmb_injective (σ := σ))).toEquiv).symm

theorem natCard_range_sbEmb (hσ : ∀ c, σ (σ c) = c) :
    Nat.card (sbEmb σ hσ).range = Nat.card SL(2, K) :=
  (Nat.card_congr (MonoidHom.ofInjective (sbEmb_injective σ hσ)).toEquiv).symm

end CFSG.RankThree.PartOne.CTP

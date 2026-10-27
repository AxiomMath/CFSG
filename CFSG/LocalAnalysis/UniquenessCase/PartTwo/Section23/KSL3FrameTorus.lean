module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSL3PointTorusProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SL3FrameMatrices
public import CFSG.Quasithin.H13.PSL3Tools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Vol2 CFSG.Quasithin.Vol2.KGNat
open CFSG.Quasithin.Vol2.KGNat.PointStab
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.LocalAnalysis.UniquenessCase.UC22.SL3Frame
open scoped Matrix Pointwise

@[expose] def IsSL3Frame {H : Type*} [Group H] (Kstar : Subgroup H) (a : Fin 3 → H) : Prop :=
  let C : Fin 3 → Subgroup H → Subgroup H := fun i X => X.map (MulAut.conj (a i)⁻¹).toMonoidHom
  let U := CFSG.Open.pCoreOf 2 Kstar
  a 0 = 1 ∧ (⨆ i, C i U) = ⊤ ∧ (∀ i j, i ≠ j → C i U ⊓ C j U = ⊥) ∧
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ∃ u ∈ C j U ⊓ C i Kstar, ∃ v ∈ C k U ⊓ C i Kstar,
    u ^ 2 = 1 ∧ v ^ 2 = 1 ∧ (u * v) ^ 3 = 1 ∧ u * v ∉ C i U

namespace KSL3FrameAux

variable {K : Type} [Field K] [CharP K 2]

private def sw01 : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], by
    have h : (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K).det = -1 := by
      rw [Matrix.det_fin_three]
      norm_num [Matrix.of_apply]
    rw [h, CharTwo.neg_eq]⟩

private def sw02 : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], by
    have h : (!![0, 0, 1; 0, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) K).det = -1 := by
      rw [Matrix.det_fin_three]
      norm_num [Matrix.of_apply]
    rw [h, CharTwo.neg_eq]⟩

private def sigma (i : Fin 3) : Matrix.SpecialLinearGroup (Fin 3) K :=
  if i = 0 then 1 else if i = 1 then sw01 else sw02

private theorem sigma_zero : sigma (K := K) (0 : Fin 3) = 1 := by simp [sigma]

private theorem sigma_one : sigma (K := K) (1 : Fin 3) = sw01 := by simp [sigma]

private theorem sigma_two : sigma (K := K) (2 : Fin 3) = sw02 := by simp [sigma]

private theorem sw01_mul_self : sw01 (K := K) * sw01 (K := K) = 1 := by
  apply Subtype.ext
  ext a b
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  fin_cases a <;> fin_cases b <;> simp [sw01, Matrix.mul_apply, Fin.sum_univ_three]

private theorem sw02_mul_self : sw02 (K := K) * sw02 (K := K) = 1 := by
  apply Subtype.ext
  ext a b
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  fin_cases a <;> fin_cases b <;> simp [sw02, Matrix.mul_apply, Fin.sum_univ_three]

private theorem sw01_inv : (sw01 (K := K))⁻¹ = sw01 (K := K) :=
  inv_eq_of_mul_eq_one_right sw01_mul_self

private theorem sw02_inv : (sw02 (K := K))⁻¹ = sw02 (K := K) :=
  inv_eq_of_mul_eq_one_right sw02_mul_self

private theorem sigma_mul_self (i : Fin 3) :
    sigma (K := K) i * sigma (K := K) i = 1 := by
  fin_cases i <;> simp [sigma, sw01_mul_self, sw02_mul_self]

private theorem sw01_conj_x01 (t : K) :
    sw01 (K := K) * Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t *
        (sw01 (K := K))⁻¹ =
      Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) t := by
  apply Subtype.ext
  rw [sw01_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [sw01, Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Matrix.vecMul,
      Matrix.vecMul_apply, dotProduct, Fin.sum_univ_three]

private theorem sw01_conj_x02 (t : K) :
    sw01 (K := K) * Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) t *
        (sw01 (K := K))⁻¹ =
      Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) t := by
  apply Subtype.ext
  rw [sw01_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [sw01, Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Matrix.vecMul,
      Matrix.vecMul_apply, dotProduct, Fin.sum_univ_three]

private theorem sw02_conj_x01 (t : K) :
    sw02 (K := K) * Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t *
        (sw02 (K := K))⁻¹ =
      Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) t := by
  apply Subtype.ext
  rw [sw02_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [sw02, Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Matrix.vecMul,
      Matrix.vecMul_apply, dotProduct, Fin.sum_univ_three]

private theorem sw02_conj_x02 (t : K) :
    sw02 (K := K) * Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) t *
        (sw02 (K := K))⁻¹ =
      Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) t := by
  apply Subtype.ext
  rw [sw02_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [sw02, Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Matrix.vecMul,
      Matrix.vecMul_apply, dotProduct, Fin.sum_univ_three]

private theorem sigma_mulVec_e0 (i : Fin 3) :
    ((sigma (K := K) i : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ![1, 0, 0] = Pi.single i 1 := by
  fin_cases i <;>
    (ext j; fin_cases j <;>
      simp [sigma, sw01, sw02, Matrix.mulVec, dotProduct, Fin.sum_univ_three])

private theorem map_conj_sw01_rowT_le :
    (rowT (0 : Fin 3)).map (MulAut.conj (sw01 (K := K))).toMonoidHom ≤ rowT (1 : Fin 3) := by
  rintro x ⟨y, hy, rfl⟩
  change y ∈ Submonoid.closure (rowGen (K := K) (0 : Fin 3)) at hy
  induction hy using Submonoid.closure_induction with
  | mem y hy =>
      obtain ⟨j, h0j, t, rfl⟩ := hy
      fin_cases j
      · exact absurd rfl h0j
      · change sw01 (K := K) * Matrix.SpecialLinearGroup.transvection
          (show (0 : Fin 3) ≠ 1 by decide) t * (sw01 (K := K))⁻¹ ∈ rowT (1 : Fin 3)
        rw [sw01_conj_x01]
        exact transvection_mem_rowT (show (1 : Fin 3) ≠ 0 by decide) t
      · change sw01 (K := K) * Matrix.SpecialLinearGroup.transvection
          (show (0 : Fin 3) ≠ 2 by decide) t * (sw01 (K := K))⁻¹ ∈ rowT (1 : Fin 3)
        rw [sw01_conj_x02]
        exact transvection_mem_rowT (show (1 : Fin 3) ≠ 2 by decide) t
  | one =>
      rw [map_one]
      exact (rowT (1 : Fin 3)).one_mem
  | mul y z _ _ ihy ihz =>
      rw [map_mul]
      exact (rowT (1 : Fin 3)).mul_mem ihy ihz

private theorem map_conj_sw01_rowT_ge :
    rowT (1 : Fin 3) ≤ (rowT (0 : Fin 3)).map (MulAut.conj (sw01 (K := K))).toMonoidHom := by
  intro x hx
  change x ∈ Submonoid.closure (rowGen (K := K) (1 : Fin 3)) at hx
  induction hx using Submonoid.closure_induction with
  | mem x hx =>
      obtain ⟨j, h1j, t, rfl⟩ := hx
      fin_cases j
      · refine ⟨Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t,
          transvection_mem_rowT (show (0 : Fin 3) ≠ 1 by decide) t, ?_⟩
        change sw01 (K := K) * Matrix.SpecialLinearGroup.transvection
          (show (0 : Fin 3) ≠ 1 by decide) t * (sw01 (K := K))⁻¹ =
          Matrix.SpecialLinearGroup.transvection h1j t
        rw [sw01_conj_x01]
      · exact absurd rfl h1j
      · refine ⟨Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) t,
          transvection_mem_rowT (show (0 : Fin 3) ≠ 2 by decide) t, ?_⟩
        change sw01 (K := K) * Matrix.SpecialLinearGroup.transvection
          (show (0 : Fin 3) ≠ 2 by decide) t * (sw01 (K := K))⁻¹ =
          Matrix.SpecialLinearGroup.transvection h1j t
        rw [sw01_conj_x02]
  | one => exact ⟨1, (rowT (0 : Fin 3)).one_mem, map_one _⟩
  | mul x y _ _ ihx ihy =>
      obtain ⟨a, ha, rfl⟩ := ihx
      obtain ⟨b, hb, rfl⟩ := ihy
      exact ⟨a * b, (rowT (0 : Fin 3)).mul_mem ha hb, map_mul _ a b⟩

private theorem map_conj_sw01_rowT :
    (rowT (0 : Fin 3)).map (MulAut.conj (sw01 (K := K))).toMonoidHom = rowT (1 : Fin 3) :=
  le_antisymm map_conj_sw01_rowT_le map_conj_sw01_rowT_ge

private theorem map_conj_sw02_rowT_le :
    (rowT (0 : Fin 3)).map (MulAut.conj (sw02 (K := K))).toMonoidHom ≤ rowT (2 : Fin 3) := by
  rintro x ⟨y, hy, rfl⟩
  change y ∈ Submonoid.closure (rowGen (K := K) (0 : Fin 3)) at hy
  induction hy using Submonoid.closure_induction with
  | mem y hy =>
      obtain ⟨j, h0j, t, rfl⟩ := hy
      fin_cases j
      · exact absurd rfl h0j
      · change sw02 (K := K) * Matrix.SpecialLinearGroup.transvection
          (show (0 : Fin 3) ≠ 1 by decide) t * (sw02 (K := K))⁻¹ ∈ rowT (2 : Fin 3)
        rw [sw02_conj_x01]
        exact transvection_mem_rowT (show (2 : Fin 3) ≠ 1 by decide) t
      · change sw02 (K := K) * Matrix.SpecialLinearGroup.transvection
          (show (0 : Fin 3) ≠ 2 by decide) t * (sw02 (K := K))⁻¹ ∈ rowT (2 : Fin 3)
        rw [sw02_conj_x02]
        exact transvection_mem_rowT (show (2 : Fin 3) ≠ 0 by decide) t
  | one =>
      rw [map_one]
      exact (rowT (2 : Fin 3)).one_mem
  | mul y z _ _ ihy ihz =>
      rw [map_mul]
      exact (rowT (2 : Fin 3)).mul_mem ihy ihz

private theorem map_conj_sw02_rowT_ge :
    rowT (2 : Fin 3) ≤ (rowT (0 : Fin 3)).map (MulAut.conj (sw02 (K := K))).toMonoidHom := by
  intro x hx
  change x ∈ Submonoid.closure (rowGen (K := K) (2 : Fin 3)) at hx
  induction hx using Submonoid.closure_induction with
  | mem x hx =>
      obtain ⟨j, h2j, t, rfl⟩ := hx
      fin_cases j
      · refine ⟨Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) t,
          transvection_mem_rowT (show (0 : Fin 3) ≠ 2 by decide) t, ?_⟩
        change sw02 (K := K) * Matrix.SpecialLinearGroup.transvection
          (show (0 : Fin 3) ≠ 2 by decide) t * (sw02 (K := K))⁻¹ =
          Matrix.SpecialLinearGroup.transvection h2j t
        rw [sw02_conj_x02]
      · refine ⟨Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t,
          transvection_mem_rowT (show (0 : Fin 3) ≠ 1 by decide) t, ?_⟩
        change sw02 (K := K) * Matrix.SpecialLinearGroup.transvection
          (show (0 : Fin 3) ≠ 1 by decide) t * (sw02 (K := K))⁻¹ =
          Matrix.SpecialLinearGroup.transvection h2j t
        rw [sw02_conj_x01]
      · exact absurd rfl h2j
  | one => exact ⟨1, (rowT (0 : Fin 3)).one_mem, map_one _⟩
  | mul x y _ _ ihx ihy =>
      obtain ⟨a, ha, rfl⟩ := ihx
      obtain ⟨b, hb, rfl⟩ := ihy
      exact ⟨a * b, (rowT (0 : Fin 3)).mul_mem ha hb, map_mul _ a b⟩

private theorem map_conj_sw02_rowT :
    (rowT (0 : Fin 3)).map (MulAut.conj (sw02 (K := K))).toMonoidHom = rowT (2 : Fin 3) :=
  le_antisymm map_conj_sw02_rowT_le map_conj_sw02_rowT_ge

private theorem sigma_conj_rowT (i : Fin 3) :
    (rowT (0 : Fin 3)).map (MulAut.conj (sigma (K := K) i)).toMonoidHom = rowT i := by
  fin_cases i
  · simp only [sigma]
    ext x
    simp [Subgroup.mem_map]
  · simpa [sigma_one] using map_conj_sw01_rowT (K := K)
  · simpa [sigma_two] using map_conj_sw02_rowT (K := K)

private theorem transvection_zero_eq_uSL {j : Fin 3} (h0j : (0 : Fin 3) ≠ j) (t : K) :
    ∃ a b : K, Matrix.SpecialLinearGroup.transvection h0j t = uSL a b 0 := by
  fin_cases j
  · exact absurd rfl h0j
  · exact ⟨t, 0, by
      ext i k
      fin_cases i <;> fin_cases k <;>
        simp [uSL, uMat, Matrix.SpecialLinearGroup.transvection_coe]⟩
  · exact ⟨0, t, by
      ext i k
      fin_cases i <;> fin_cases k <;>
        simp [uSL, uMat, Matrix.SpecialLinearGroup.transvection_coe]⟩

private theorem uSL_eq_transvection01 (a : K) :
    uSL a 0 0 = Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) a := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [uSL, uMat, Matrix.SpecialLinearGroup.transvection_coe]

private theorem uSL_eq_transvection02 (b : K) :
    uSL 0 b 0 = Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) b := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [uSL, uMat, Matrix.SpecialLinearGroup.transvection_coe]

private theorem mem_rowT_zero_iff {x : Matrix.SpecialLinearGroup (Fin 3) K} :
    x ∈ rowT (0 : Fin 3) ↔ ∃ a b : K, x = uSL a b 0 := by
  constructor
  · intro hx
    rw [mem_rowT] at hx
    induction hx using Submonoid.closure_induction with
    | mem x hx =>
        obtain ⟨j, h0j, t, rfl⟩ := hx
        exact transvection_zero_eq_uSL h0j t
    | one => exact ⟨0, 0, by rw [uSL_zero]⟩
    | mul x y _ _ ihx ihy =>
        obtain ⟨a, b, rfl⟩ := ihx
        obtain ⟨a', b', rfl⟩ := ihy
        refine ⟨a + a', b + b', ?_⟩
        simpa [uSL_mul]
  · rintro ⟨a, b, rfl⟩
    have h1 : uSL a 0 0 ∈ rowT (0 : Fin 3) := by
      rw [uSL_eq_transvection01]
      exact transvection_mem_rowT _ a
    have h2 : uSL 0 b 0 ∈ rowT (0 : Fin 3) := by
      rw [uSL_eq_transvection02]
      exact transvection_mem_rowT _ b
    have hmul : uSL a b 0 = uSL a 0 0 * uSL 0 b 0 := by
      simpa [uSL_mul]
    rw [hmul]
    exact (rowT (0 : Fin 3)).mul_mem h1 h2

private theorem sigma_inv_eq (i : Fin 3) :
    (sigma (K := K) i)⁻¹ = sigma (K := K) i :=
  inv_eq_of_mul_eq_one_right (sigma_mul_self i)

private theorem sigma_mulVec_ei (i : Fin 3) :
    (((sigma (K := K) i : Matrix.SpecialLinearGroup (Fin 3) K)) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single i 1 = ![1, 0, 0] := by
  calc (((sigma (K := K) i : Matrix.SpecialLinearGroup (Fin 3) K)) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single i 1
      = (((sigma (K := K) i : Matrix.SpecialLinearGroup (Fin 3) K)) :
          Matrix (Fin 3) (Fin 3) K) *ᵥ
          ((((sigma (K := K) i : Matrix.SpecialLinearGroup (Fin 3) K)) :
            Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]) := by
        rw [sigma_mulVec_e0]
    _ = (((((sigma (K := K) i : Matrix.SpecialLinearGroup (Fin 3) K)) :
          Matrix (Fin 3) (Fin 3) K) *
          (((sigma (K := K) i : Matrix.SpecialLinearGroup (Fin 3) K)) :
            Matrix (Fin 3) (Fin 3) K)) *ᵥ ![1, 0, 0]) := by
        rw [Matrix.mulVec_mulVec]
    _ = ((((sigma (K := K) i * sigma (K := K) i :
            Matrix.SpecialLinearGroup (Fin 3) K)) :
          Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]) := by
        rw [← Matrix.SpecialLinearGroup.coe_mul]
    _ = (((1 : Matrix.SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]) := by rw [sigma_mul_self]
    _ = ![1, 0, 0] := by rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

private theorem conj_sigma_mem_stabE0_of_mem_vecStab (i : Fin 3)
    {A : Matrix.SpecialLinearGroup (Fin 3) K} (hA : A ∈ vecStab i) :
    sigma (K := K) i * A * (sigma (K := K) i)⁻¹ ∈ stabE0 K := by
  rw [mem_stabE0]
  have hAe : (A : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single i 1 = Pi.single i 1 :=
    (mem_vecStab).mp hA
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [sigma_inv_eq, sigma_mulVec_e0, hAe, sigma_mulVec_ei]

private theorem transvection_sq {j k : Fin 3} (hjk : j ≠ k) :
    Matrix.SpecialLinearGroup.transvection hjk (1 : K) *
      Matrix.SpecialLinearGroup.transvection hjk 1 = 1 := by
  have h := Matrix.SpecialLinearGroup.transvection_mul_neg hjk (1 : K)
  simpa [CharTwo.neg_eq] using h

private theorem transvection_mul_symm_not_mem_rowT {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Matrix.SpecialLinearGroup.transvection hjk (1 : K) *
      Matrix.SpecialLinearGroup.transvection hjk.symm 1 ∉ rowT i := by
  intro hmem
  have hrow := congrFun (rowT_row_eq_one hmem (a := j) hij.symm) k
  have hentry : ((Matrix.SpecialLinearGroup.transvection hjk (1 : K) *
      Matrix.SpecialLinearGroup.transvection hjk.symm 1 :
        Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) j k = 1 := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
      [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply]
  simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply, if_neg hjk] at hrow
  rw [hentry] at hrow
  exact one_ne_zero hrow

private theorem tSL_diag_eq (c : K) (hc0 : c ≠ 0) :
    (((tSL ((Units.mk0 c hc0)⁻¹ * (Units.mk0 c hc0)⁻¹,
      Units.mk0 c hc0) : Matrix.SpecialLinearGroup (Fin 3) K)) :
        Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal (fun l : Fin 3 => if l = 0 then c⁻¹ * c⁻¹ else c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tSL, tFun, tMat, Matrix.diagonal, Matrix.of_apply, hc0]

private theorem stdLine_eq_span_e0 : stdLine K = Submodule.span K {![1, 0, 0]} := by
  ext x
  rw [mem_stdLine, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨x 0, ?_⟩
    ext i
    fin_cases i <;> simp [h1, h2]
  · rintro ⟨c, rfl⟩
    simp

private theorem mem_stabilizer_flagSpace_one_iff
    (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    A ∈ stabilizer (flagSpace 3 K 1) ↔
      ∃ c : K, (A : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = c • ![1, 0, 0] := by
  rw [stdLine_eq_flagSpace.symm, mem_stabilizer, stdLine_eq_span_e0, Submodule.map_span]
  simp only [Set.image_singleton]
  constructor
  · intro h
    have hmem : (A : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] ∈
        Submodule.span K {![1, 0, 0]} := by
      rw [← h]
      exact Submodule.subset_span (Set.mem_singleton _)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton).mp hmem
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      intro h0
      have hcol : ∀ i, (A : Matrix (Fin 3) (Fin 3) K) i 0 = 0 := by
        intro i
        have := congrFun hc i
        simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h0] using this
      have hdet := Matrix.det_eq_zero_of_column_eq_zero (0 : Fin 3) hcol
      rw [A.2] at hdet
      exact one_ne_zero hdet
    have hspan : Submodule.span K {(A : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]} =
        Submodule.span K {![1, 0, 0]} := by
      rw [hc]
      exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc0) ![1, 0, 0]
    simpa [Matrix.mulVecLin] using hspan

private theorem mem_vecStab_of_diagonal {A : Matrix.SpecialLinearGroup (Fin 3) K}
    {d : Fin 3 → K} (hA : (A : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal d)
    {i : Fin 3} (hd : d i = 1) : A ∈ vecStab i := by
  rw [mem_vecStab, hA]
  ext a
  rw [Matrix.mulVec_diagonal]
  by_cases hai : a = i <;> simp [hai, hd, Pi.single_apply]

private theorem conj_sigma_diagonal_mem_stabilizer
    {A : Matrix.SpecialLinearGroup (Fin 3) K} {d : Fin 3 → K}
    (hA : (A : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal d) (i : Fin 3) :
    sigma (K := K) i * A * (sigma (K := K) i)⁻¹ ∈ stabilizer (flagSpace 3 K 1) := by
  rw [mem_stabilizer_flagSpace_one_iff]
  refine ⟨d i, ?_⟩
  have hAe : (A : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single i 1 = d i • Pi.single i 1 := by
    rw [hA]
    ext a
    rw [Matrix.mulVec_diagonal]
    by_cases hai : a = i <;> simp [hai, Pi.single_apply]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [sigma_inv_eq, sigma_mulVec_e0, hAe, Matrix.mulVec_smul, sigma_mulVec_ei]

private theorem conj_sigma_diagonal_mem_stabE0
    {A : Matrix.SpecialLinearGroup (Fin 3) K} {d : Fin 3 → K}
    (hA : (A : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal d) {i : Fin 3} (hd : d i = 1) :
    sigma (K := K) i * A * (sigma (K := K) i)⁻¹ ∈ stabE0 K :=
  conj_sigma_mem_stabE0_of_mem_vecStab i (mem_vecStab_of_diagonal hA hd)

private theorem mem_map_conj_sigma_map {H : Type} [Group H]
    (Φ : Matrix.SpecialLinearGroup (Fin 3) K →* H) (i : Fin 3)
    {X : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)}
    {A : Matrix.SpecialLinearGroup (Fin 3) K}
    (hA : sigma (K := K) i * A * (sigma (K := K) i)⁻¹ ∈ X) :
    Φ A ∈ (X.map (MulAut.conj (sigma (K := K) i)).toMonoidHom).map Φ := by
  refine Subgroup.mem_map.mpr ⟨A, ?_, rfl⟩
  refine Subgroup.mem_map.mpr ⟨sigma (K := K) i * A * (sigma (K := K) i)⁻¹, hA, ?_⟩
  change (MulAut.conj (sigma (K := K) i)) (sigma (K := K) i * A * (sigma (K := K) i)⁻¹) = A
  rw [MulAut.conj_apply, sigma_inv_eq]
  calc sigma (K := K) i * (sigma (K := K) i * A * sigma (K := K) i) * sigma (K := K) i
      = (sigma (K := K) i * sigma (K := K) i) * A *
          (sigma (K := K) i * sigma (K := K) i) := by group
    _ = A := by rw [sigma_mul_self]; group

private theorem map_conj_inv_eq_map_conj_sigma_map {H : Type} [Group H]
    (Φ : Matrix.SpecialLinearGroup (Fin 3) K →* H) (a : Fin 3 → H)
    (ha : ∀ i, a i = (Φ (sigma (K := K) i))⁻¹)
    (X : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)) (i : Fin 3) :
    (X.map Φ).map (MulAut.conj (a i)⁻¹).toMonoidHom =
      (X.map (MulAut.conj (sigma (K := K) i)).toMonoidHom).map Φ := by
  have hpoint : ∀ A : Matrix.SpecialLinearGroup (Fin 3) K,
      (MulAut.conj (a i)⁻¹).toMonoidHom (Φ A) =
        Φ (MulAut.conj (sigma (K := K) i) A) := by
    intro A
    change MulAut.conj (a i)⁻¹ (Φ A) = Φ (MulAut.conj (sigma (K := K) i) A)
    rw [MulAut.conj_apply, MulAut.conj_apply, ha i]
    simp only [inv_inv, map_mul, map_inv]
  have hconj : (MulAut.conj (a i)⁻¹).toMonoidHom.comp Φ =
      Φ.comp (MulAut.conj (sigma (K := K) i)).toMonoidHom := MonoidHom.ext hpoint
  rw [Subgroup.map_map X (MulAut.conj (a i)⁻¹).toMonoidHom Φ, hconj,
    ← Subgroup.map_map X Φ (MulAut.conj (sigma (K := K) i)).toMonoidHom]

private theorem frame_sup_eq_top {H : Type} [Group H] (Kstar : Subgroup H)
    (Φ : Matrix.SpecialLinearGroup (Fin 3) K →* H) (a : Fin 3 → H)
    (hCU : ∀ i, (CFSG.Open.pCoreOf 2 Kstar).map (MulAut.conj (a i)⁻¹).toMonoidHom =
      (rowT i).map Φ)
    (hΦ_surj : Function.Surjective Φ) :
    (⨆ i, (CFSG.Open.pCoreOf 2 Kstar).map (MulAut.conj (a i)⁻¹).toMonoidHom) = ⊤ := by
  calc (⨆ i, (CFSG.Open.pCoreOf 2 Kstar).map (MulAut.conj (a i)⁻¹).toMonoidHom)
      = ⨆ i, (rowT i).map Φ := iSup_congr hCU
    _ = ((⨆ i, rowT i)).map Φ :=
        (Subgroup.map_iSup (f := Φ) (s := fun i => rowT i)).symm
    _ = (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)).map Φ := by
        change Subgroup.map Φ (⨆ i, rowT i) = Subgroup.map Φ ⊤
        rw [iSup_rowT_eq_top]
    _ = ⊤ := by
        rw [Subgroup.map_top]
        exact MonoidHom.range_eq_top.mpr hΦ_surj

private theorem frame_pairwise_bot {H : Type} [Group H] (Kstar : Subgroup H)
    (Φ : Matrix.SpecialLinearGroup (Fin 3) K →* H) (a : Fin 3 → H)
    (hCU : ∀ i, (CFSG.Open.pCoreOf 2 Kstar).map (MulAut.conj (a i)⁻¹).toMonoidHom =
      (rowT i).map Φ)
    (hΦ_inj : Function.Injective Φ) :
    ∀ i j, i ≠ j → (CFSG.Open.pCoreOf 2 Kstar).map (MulAut.conj (a i)⁻¹).toMonoidHom ⊓
      (CFSG.Open.pCoreOf 2 Kstar).map (MulAut.conj (a j)⁻¹).toMonoidHom = ⊥ := by
  intro i j hij
  rw [hCU i, hCU j, ← Subgroup.map_inf _ _ Φ hΦ_inj, rowT_inf_rowT_eq_bot hij]
  exact Subgroup.map_bot Φ

private theorem frame_transvection_mem {H : Type} [Group H] (Kstar : Subgroup H)
    (Φ : Matrix.SpecialLinearGroup (Fin 3) K →* H) (a : Fin 3 → H)
    (hCU : ∀ i, (CFSG.Open.pCoreOf 2 Kstar).map (MulAut.conj (a i)⁻¹).toMonoidHom =
      (rowT i).map Φ)
    (hCK : ∀ i, Kstar.map (MulAut.conj (a i)⁻¹).toMonoidHom =
      ((stabE0 K).map (MulAut.conj (sigma (K := K) i)).toMonoidHom).map Φ)
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Φ (Matrix.SpecialLinearGroup.transvection hjk (1 : K)) ∈
        (CFSG.Open.pCoreOf 2 Kstar).map (MulAut.conj (a j)⁻¹).toMonoidHom ⊓
          Kstar.map (MulAut.conj (a i)⁻¹).toMonoidHom ∧
      Φ (Matrix.SpecialLinearGroup.transvection hjk.symm 1) ∈
        (CFSG.Open.pCoreOf 2 Kstar).map (MulAut.conj (a k)⁻¹).toMonoidHom ⊓
          Kstar.map (MulAut.conj (a i)⁻¹).toMonoidHom := by
  constructor
  · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hCU j]
      exact Subgroup.mem_map.mpr ⟨_, transvection_mem_rowT hjk 1, rfl⟩
    · rw [hCK i]
      exact mem_map_conj_sigma_map Φ i
        (conj_sigma_mem_stabE0_of_mem_vecStab i (transvection_mem_vecStab hjk hij hik 1))
  · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hCU k]
      exact Subgroup.mem_map.mpr ⟨_, transvection_mem_rowT hjk.symm 1, rfl⟩
    · rw [hCK i]
      exact mem_map_conj_sigma_map Φ i
        (conj_sigma_mem_stabE0_of_mem_vecStab i
          (transvection_mem_vecStab hjk.symm hik hij 1))

private theorem frame_transvection_props {H : Type} [Group H] (Kstar : Subgroup H)
    (Φ : Matrix.SpecialLinearGroup (Fin 3) K →* H) (a : Fin 3 → H)
    (hCU : ∀ i, (CFSG.Open.pCoreOf 2 Kstar).map (MulAut.conj (a i)⁻¹).toMonoidHom =
      (rowT i).map Φ)
    (hΦ_inj : Function.Injective Φ) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (Φ (Matrix.SpecialLinearGroup.transvection hjk (1 : K))) ^ 2 = 1 ∧
      (Φ (Matrix.SpecialLinearGroup.transvection hjk.symm 1)) ^ 2 = 1 ∧
      (Φ (Matrix.SpecialLinearGroup.transvection hjk (1 : K)) *
        Φ (Matrix.SpecialLinearGroup.transvection hjk.symm 1)) ^ 3 = 1 ∧
      Φ (Matrix.SpecialLinearGroup.transvection hjk (1 : K)) *
        Φ (Matrix.SpecialLinearGroup.transvection hjk.symm 1) ∉
        (CFSG.Open.pCoreOf 2 Kstar).map (MulAut.conj (a i)⁻¹).toMonoidHom := by
  have hu0_sq : Matrix.SpecialLinearGroup.transvection hjk (1 : K) *
      Matrix.SpecialLinearGroup.transvection hjk (1 : K) = 1 := transvection_sq hjk
  have hv0_sq : Matrix.SpecialLinearGroup.transvection hjk.symm (1 : K) *
      Matrix.SpecialLinearGroup.transvection hjk.symm 1 = 1 := transvection_sq hjk.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← map_pow, show Matrix.SpecialLinearGroup.transvection hjk (1 : K) ^ 2 = 1 by
      rw [pow_two]; exact hu0_sq, map_one]
  · rw [← map_pow, show Matrix.SpecialLinearGroup.transvection hjk.symm (1 : K) ^ 2 = 1 by
      rw [pow_two]; exact hv0_sq, map_one]
  · rw [← map_mul, ← map_pow,
      show (Matrix.SpecialLinearGroup.transvection hjk (1 : K) *
        Matrix.SpecialLinearGroup.transvection hjk.symm 1) ^ 3 = 1 from
        CFSG.Quasithin.H13.PSL3.transvection_mul_transvection_pow_three hjk, map_one]
  · rw [hCU i, ← map_mul]
    intro hmem
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hmem
    refine transvection_mul_symm_not_mem_rowT (K := K) hij hik hjk ?_
    rwa [← hΦ_inj hxeq]

private theorem frame_transvection_clause {H : Type} [Group H] (Kstar : Subgroup H)
    (Φ : Matrix.SpecialLinearGroup (Fin 3) K →* H) (a : Fin 3 → H)
    (hCU : ∀ i, (CFSG.Open.pCoreOf 2 Kstar).map (MulAut.conj (a i)⁻¹).toMonoidHom =
      (rowT i).map Φ)
    (hCK : ∀ i, Kstar.map (MulAut.conj (a i)⁻¹).toMonoidHom =
      ((stabE0 K).map (MulAut.conj (sigma (K := K) i)).toMonoidHom).map Φ)
    (hΦ_inj : Function.Injective Φ) :
    ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      ∃ u ∈ (CFSG.Open.pCoreOf 2 Kstar).map (MulAut.conj (a j)⁻¹).toMonoidHom ⊓
          Kstar.map (MulAut.conj (a i)⁻¹).toMonoidHom,
        ∃ v ∈ (CFSG.Open.pCoreOf 2 Kstar).map (MulAut.conj (a k)⁻¹).toMonoidHom ⊓
          Kstar.map (MulAut.conj (a i)⁻¹).toMonoidHom,
          u ^ 2 = 1 ∧ v ^ 2 = 1 ∧ (u * v) ^ 3 = 1 ∧
            u * v ∉ (CFSG.Open.pCoreOf 2 Kstar).map
              (MulAut.conj (a i)⁻¹).toMonoidHom := by
  intro i j k hij hik hjk
  obtain ⟨hu, hv⟩ := frame_transvection_mem Kstar Φ a hCU hCK hij hik hjk
  obtain ⟨hu2, hv2, huv3, huv_not⟩ :=
    frame_transvection_props Kstar Φ a hCU hΦ_inj hij hik hjk
  exact ⟨_, hu, _, hv, hu2, hv2, huv3, huv_not⟩

end KSL3FrameAux

variable {K : Type} [Field K] [CharP K 2] [Finite K]
  {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)}
  {ρ : ↥(StatedSL 3 K) →* ↥H} {f : W → Fin 3 → K}

private theorem mem_stabW_pre_iff
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) (S : Submodule K (Fin 3 → K))
    (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    ((rho3 ρ A : ↥H) : MulAut W) ∈ Ch11.SecA.stabW (hf.pre (gmap g S).toAddSubgroup) ↔
      ∀ y : Fin 3 → K, y ∈ gmap g S ↔
        (A : Matrix (Fin 3) (Fin 3) K) *ᵥ y ∈ gmap g S := by
  rw [IsCoord.rho3_mem_stabW_iff hf (hf.le_pre _) A, hf.img_pre]
  rfl

private theorem map_stabilizer_flagSpace_eq_setStab
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) (d : ℕ) :
    (stabilizer (flagSpace 3 K d)).map
        ((rho3 ρ).comp (MulAut.conj g).toMonoidHom) =
      setStab H (hf.pre (gmap g (flagSpace 3 K d)).toAddSubgroup) := by
  rw [setStab_eq]
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨(rho3 ρ (g * A * g⁻¹)).2, ?_⟩
    change ((rho3 ρ (g * A * g⁻¹) : ↥H) : MulAut W) ∈
      Ch11.SecA.stabW (hf.pre (gmap g (flagSpace 3 K d)).toAddSubgroup)
    rw [mem_stabW_pre_iff hf g (flagSpace 3 K d) (g * A * g⁻¹)]
    intro y
    rw [mem_gmap, mem_gmap, conj_mulVec]
    simpa only [Matrix.SpecialLinearGroup.coe_inv] using
      mem_iff_of_mem_stabilizer hA ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) *ᵥ y)
  · rintro ⟨-, hx⟩
    obtain ⟨A, hA⟩ := (rho3_bijective hf).2 x
    rw [← hA] at hx
    have hxs := (mem_stabW_pre_iff hf g (flagSpace 3 K d) A).mp hx
    have hB : g⁻¹ * A * g ∈ stabilizer (flagSpace 3 K d) := by
      refine mem_stabilizer_of_iff fun y => ?_
      have h1 := hxs ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ y)
      rw [mem_gmap, mem_gmap, ginv_g_mulVec, mulVec_gconj] at h1
      exact h1
    refine ⟨g⁻¹ * A * g, hB, ?_⟩
    change rho3 ρ (g * (g⁻¹ * A * g) * g⁻¹) = x
    rw [show g * (g⁻¹ * A * g) * g⁻¹ = A by group, hA]

theorem stabilizer_preLine_eq_map_stabilizer
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (h : Matrix.SpecialLinearGroup (Fin 3) K) :
    MulAction.stabilizer ↥H ((preLine (W := W) hf h : Subgroup W) : Set W) =
      (stabilizer (flagSpace 3 K 1)).map
        ((rho3 ρ).comp (MulAut.conj h).toMonoidHom) := by
  have hP : MulAction.stabilizer ↥H ((preLine hf h : Subgroup W) : Set W) =
      setStab H (preLine hf h) := rfl
  rw [hP, preLine, ← map_stabilizer_flagSpace_eq_setStab hf h 1]

theorem hinf_stabilizer_eq_map_stabE0
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (h : Matrix.SpecialLinearGroup (Fin 3) K) :
    Hinf (MulAction.stabilizer ↥H ((preLine (W := W) hf h : Subgroup W) : Set W)) =
      (stabE0 K).map ((rho3 ρ).comp (MulAut.conj h).toMonoidHom) := by
  obtain ⟨e, he⟩ := exists_equiv_stabE0 hSL hf h
  ext z
  rw [mem_hinf_stabilizer_iff hf h z]
  constructor
  · intro hz
    obtain ⟨B, hB⟩ := e.surjective ⟨(z : MulAut W), hz⟩
    refine ⟨B, B.2, ?_⟩
    apply Subtype.ext
    change (((rho3 ρ) (h * (B : Matrix.SpecialLinearGroup (Fin 3) K) * h⁻¹) : ↥H) :
      MulAut W) = (z : MulAut W)
    rw [← he B, hB]
  · rintro ⟨B, hB, rfl⟩
    change (((rho3 ρ).comp (MulAut.conj h).toMonoidHom) B : MulAut W) ∈
      perfectCore (H ⊓ Ch11.SecA.stabW
        (hf.pre (gmap h (flagSpace 3 K 1)).toAddSubgroup))
    rw [show (((rho3 ρ).comp (MulAut.conj h).toMonoidHom) B : MulAut W) =
      (e ⟨B, hB⟩ : MulAut W) from (he ⟨B, hB⟩).symm]
    exact (e ⟨B, hB⟩).2

theorem pCoreOf_hinf_eq_map_rowT
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (h : Matrix.SpecialLinearGroup (Fin 3) K) :
    CFSG.Open.pCoreOf 2
        (Hinf (MulAction.stabilizer ↥H ((preLine (W := W) hf h : Subgroup W) : Set W))) =
      (rowT (0 : Fin 3)).map ((rho3 ρ).comp (MulAut.conj h).toMonoidHom) := by
  ext z
  rw [mem_pCore_hinf_iff_exists_uSL hSL hf h z]
  constructor
  · rintro ⟨a, b, rfl⟩
    refine ⟨uSL a b 0, (KSL3FrameAux.mem_rowT_zero_iff).mpr ⟨a, b, rfl⟩, ?_⟩
    rfl
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, b, rfl⟩ := (KSL3FrameAux.mem_rowT_zero_iff).mp hx
    exact ⟨a, b, rfl⟩

theorem map_conj_mul_eq_map_conj {G : Type*} [Group G] {X : Subgroup G} {h u : G} (hu : u ∈ X) :
    X.map (MulAut.conj (h * u)).toMonoidHom = X.map (MulAut.conj h).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨u * y * u⁻¹, X.mul_mem (X.mul_mem hu hy) (X.inv_mem hu), by
      change MulAut.conj h (MulAut.conj u y) = MulAut.conj (h * u) y
      simp only [MulAut.conj_apply]
      group⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨u⁻¹ * y * u, X.mul_mem (X.mul_mem (X.inv_mem hu) hy) hu, by
      change MulAut.conj (h * u) (u⁻¹ * y * u) = MulAut.conj h y
      simp only [MulAut.conj_apply]
      group⟩

open KSL3FrameAux

private theorem frame_t_ne_one {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1) (k : Fin 3) :
    (fun l : Fin 3 => if l = 0 then c⁻¹ * c⁻¹ else c) k ≠ 1 := by
  by_cases hk0 : k = 0
  · subst hk0
    simp only [if_pos rfl]
    intro h
    have h2 : c * c = 1 := by
      have h' := congrArg (fun x : K => x⁻¹) h
      simpa [mul_inv_rev, inv_inv, hc0] using h'
    have h2' : c ^ 2 = 1 := by simpa [pow_two] using h2
    rcases sq_eq_one_iff.mp h2' with h3 | h3
    · exact hc1 h3
    · rw [h3, CharTwo.neg_eq] at hc1
      exact hc1 rfl
  · simp only [if_neg hk0]
    exact hc1

private theorem odd_card_sub_one {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 3 ≤ n) :
    Odd (Nat.card K - 1) := by
  rw [hK]
  have hn0 : n ≠ 0 := by omega
  exact Nat.Even.sub_odd Nat.one_le_two_pow
    (Even.pow_of_ne_zero (a := (2 : ℕ)) ⟨1, by norm_num⟩ hn0) (by norm_num : Odd 1)

private theorem frame_torus_decomposition [Fintype K] (Kstar Pℓ : Subgroup ↥H)
    (Φ : Matrix.SpecialLinearGroup (Fin 3) K →* ↥H) (a : Fin 3 → ↥H) {g : ↥H}
    (hCU : ∀ i, (CFSG.Open.pCoreOf 2 Kstar).map (MulAut.conj (a i)⁻¹).toMonoidHom =
      (rowT i).map Φ)
    (hCK : ∀ i, Kstar.map (MulAut.conj (a i)⁻¹).toMonoidHom =
      ((stabE0 K).map (MulAut.conj (sigma (K := K) i)).toMonoidHom).map Φ)
    (hCP : ∀ i, Pℓ.map (MulAut.conj (a i)⁻¹).toMonoidHom =
      ((stabilizer (flagSpace 3 K 1)).map
        (MulAut.conj (sigma (K := K) i)).toMonoidHom).map Φ)
    (hΦ_inj : Function.Injective Φ) {T : Matrix.SpecialLinearGroup (Fin 3) K} {c : K}
    (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (hTdiag : (T : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal (fun l => if l = 0 then c⁻¹ * c⁻¹ else c))
    (hΦT : Φ T = g) {n : ℕ} (hn : 3 ≤ n) (hK : Nat.card K = 2 ^ n) :
    ∀ i j, i ≠ j →
      ∃ y ∈ (CFSG.Open.pCoreOf 2 Kstar).map (MulAut.conj (a i)⁻¹).toMonoidHom ⊔
          (CFSG.Open.pCoreOf 2 Kstar).map (MulAut.conj (a j)⁻¹).toMonoidHom,
        ∃ κ ∈ Kstar.map (MulAut.conj (a i)⁻¹).toMonoidHom ⊓
          Pℓ.map (MulAut.conj (a j)⁻¹).toMonoidHom,
          g = y * κ ∧
            κ ∉ (CFSG.Open.pCoreOf 2 Kstar).map (MulAut.conj (a i)⁻¹).toMonoidHom ∧
              ∃ r, Odd r ∧ κ ^ r = 1 := by
  intro i j hij
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (show 2 < 3 by decide)
  have hik : i ≠ k := hki.symm
  have hjk : j ≠ k := hkj.symm
  let t : Fin 3 → K := fun l => if l = 0 then c⁻¹ * c⁻¹ else c
  let dκ : Fin 3 → K := fun l => if l = i then 1 else if l = j then t i * t j else t l
  have hTdiag' : (T : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal t := hTdiag
  have hκdiag : (kappa i j hij t T : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal dκ :=
    kappa_coe hij hTdiag'
  have hdκi : dκ i = 1 := by simp [dκ]
  have htk : t k ≠ 1 := frame_t_ne_one hc0 hc1 k
  refine ⟨Φ (rowProd i j hij (t i)), ?_, Φ (kappa i j hij t T), ?_, ?_, ?_, ?_⟩
  · rw [hCU i, hCU j, ← Subgroup.map_sup]
    exact Subgroup.mem_map.mpr ⟨rowProd i j hij (t i), rowProd_mem_rowT_sup hij (t i), rfl⟩
  · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hCK i]
      exact mem_map_conj_sigma_map Φ i (conj_sigma_diagonal_mem_stabE0 hκdiag hdκi)
    · rw [hCP j]
      exact mem_map_conj_sigma_map Φ j (conj_sigma_diagonal_mem_stabilizer hκdiag j)
  · rw [← hΦT, ← map_mul, ← diagonal_eq_rowProd_mul_kappa hij hTdiag']
  · intro hmem
    rw [hCU i] at hmem
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hmem
    have hx' : kappa i j hij t T ∈ rowT i := hΦ_inj hxeq ▸ hx
    exact kappa_not_mem_rowT hij hik hjk hTdiag' htk hx'
  · refine ⟨Nat.card K - 1, odd_card_sub_one hK hn, ?_⟩
    have h := congrArg Φ (kappa_pow_card_sub_one hij hTdiag')
    simpa using h

private theorem map_comp_conj_eq_map_comp_conj_mul (Φ₀ : Matrix.SpecialLinearGroup (Fin 3) K →* ↥H)
    (X : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K))
    {h u : Matrix.SpecialLinearGroup (Fin 3) K} (hu : u ∈ X) :
    X.map (Φ₀.comp (MulAut.conj h).toMonoidHom) =
      X.map (Φ₀.comp (MulAut.conj (h * u)).toMonoidHom) := by
  calc X.map (Φ₀.comp (MulAut.conj h).toMonoidHom)
      = (X.map (MulAut.conj h).toMonoidHom).map Φ₀ :=
        (Subgroup.map_map X Φ₀ (MulAut.conj h).toMonoidHom).symm
    _ = (X.map (MulAut.conj (h * u)).toMonoidHom).map Φ₀ := by
        rw [map_conj_mul_eq_map_conj hu]
    _ = X.map (Φ₀.comp (MulAut.conj (h * u)).toMonoidHom) :=
        Subgroup.map_map X Φ₀ (MulAut.conj (h * u)).toMonoidHom

private theorem point_stabilizer_data
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    {h : Matrix.SpecialLinearGroup (Fin 3) K} {ℓ : Subgroup W}
    (hℓ : ℓ = preLine (W := W) hf h)
    {Pℓ : Subgroup ↥H} (hPℓ : Pℓ = MulAction.stabilizer ↥H (ℓ : Set W))
    {Kstar : Subgroup ↥H} (hKst : Kstar = Hinf Pℓ) :
    Kstar = Hinf (MulAction.stabilizer ↥H
        ((preLine (W := W) hf h : Subgroup W) : Set W)) ∧
      Pℓ = MulAction.stabilizer ↥H ((preLine (W := W) hf h : Subgroup W) : Set W) := by
  have hpre : MulAction.stabilizer ↥H (ℓ : Set W) =
      MulAction.stabilizer ↥H ((preLine (W := W) hf h : Subgroup W) : Set W) := by rw [hℓ]
  exact ⟨by rw [hKst, hPℓ, hpre], by rw [hPℓ, hpre]⟩

private theorem exists_torus_normal_form
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    {h : Matrix.SpecialLinearGroup (Fin 3) K} {Kstar : Subgroup ↥H} {g : ↥H}
    (hKstar : Kstar = Hinf (MulAction.stabilizer ↥H
      ((preLine (W := W) hf h : Subgroup W) : Set W)))
    (hcomm : ∀ k ∈ Kstar, g * k * g⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 Kstar)
    (hodd : Odd (orderOf g)) (hg3 : g ^ 3 ≠ 1) :
    ∃ (M : Matrix.SpecialLinearGroup (Fin 3) K) (c : K) (a b : K) (hc0 : c ≠ 0),
      rho3 ρ M = g ∧ c ^ 3 ≠ 1 ∧ c ≠ 1 ∧
      h⁻¹ * M * h = tSL ((Units.mk0 c hc0)⁻¹ * (Units.mk0 c hc0)⁻¹, Units.mk0 c hc0) *
        uSL a b 0 := by
  obtain ⟨M, hgM⟩ := (rho3_bijective hf).2 g
  have hgPℓM : (rho3 ρ M : ↥H) ∈ MulAction.stabilizer ↥H
      ((preLine (W := W) hf h : Subgroup W) : Set W) := by
    rw [hgM]
    exact mem_stabilizer_of_commutator hSL hf hKstar hcomm
  have hgStab : ((rho3 ρ M : ↥H) : MulAut W) ∈ Ch11.SecA.stabW (preLine hf h) := by
    change (rho3 ρ M : ↥H) ∈ setStab H (preLine hf h) at hgPℓM
    rw [setStab_eq, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hgPℓM
    exact hgPℓM.2
  obtain ⟨μ, hμ0, hDe0⟩ := exists_smul_e0_of_mem_stabW hf h M rfl hgStab
  have hcommM : ∀ k ∈ Hinf (MulAction.stabilizer ↥H
      ((preLine (W := W) hf h : Subgroup W) : Set W)),
      (rho3 ρ M) * k * (rho3 ρ M)⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2
        (Hinf (MulAction.stabilizer ↥H ((preLine (W := W) hf h : Subgroup W) : Set W))) := by
    intro k hk
    have hk' : k ∈ Kstar := by rwa [← hKstar] at hk
    simpa [hKstar, hgM] using hcomm k hk'
  obtain ⟨c, hclev⟩ := exists_smul_one_lev hSL hf h M hcommM hDe0 hμ0 rfl
  have hoddM : Odd (orderOf (rho3 ρ M)) := by rwa [hgM]
  have hg3M : (rho3 ρ M) ^ 3 ≠ 1 := by rwa [hgM]
  obtain ⟨-, hc0, hc3, hc1, -⟩ :=
    kSL3PointTorus_scalar_properties hf rfl hDe0 hclev hoddM hg3M
  have hμc : μ * c ^ 2 = 1 := mu_mul_sq_of_line_lev hDe0 hclev
  obtain ⟨a, b, hD⟩ := eq_tSL_mul_uSL hDe0 hclev hμc hc0
  exact ⟨M, c, a, b, hc0, hgM, hc3, hc1, hD⟩

private theorem exists_torus_factorization {M h T : Matrix.SpecialLinearGroup (Fin 3) K}
    {c a b : K} (hc0 : c ≠ 0)
    (hT : T = tSL ((Units.mk0 c hc0)⁻¹ * (Units.mk0 c hc0)⁻¹, Units.mk0 c hc0))
    (hc3 : c ^ 3 ≠ 1) (hD : h⁻¹ * M * h = T * uSL a b 0) :
    ∃ u : Matrix.SpecialLinearGroup (Fin 3) K,
      (h * u)⁻¹ * M * (h * u) = T ∧
        u = uSL (-(a / (1 + c ^ 3))) (-(b / (1 + c ^ 3))) 0 := by
  let N : Matrix.SpecialLinearGroup (Fin 3) K :=
    uSL (a / (1 + c ^ 3)) (b / (1 + c ^ 3)) 0
  have hN : N * (T * uSL a b 0) * N⁻¹ = T := by
    rw [hT]
    exact conj_tSL_mul_uSL hc0 hc3 a b
  refine ⟨N⁻¹, ?_, ?_⟩
  · have h1 : (h * N⁻¹)⁻¹ * M * (h * N⁻¹) = N * (h⁻¹ * M * h) * N⁻¹ := by group
    rw [h1, hD]
    exact hN
  · rw [uSL_inv]
    simp [N]

private theorem torus_unit_props {u : Matrix.SpecialLinearGroup (Fin 3) K} {c a b : K}
    (hu : u = uSL (-(a / (1 + c ^ 3))) (-(b / (1 + c ^ 3))) 0) :
    ((u : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = ![1, 0, 0]) ∧ u ∈ stabE0 K ∧
      u ∈ rowT (0 : Fin 3) ∧ u ∈ stabilizer (flagSpace 3 K 1) := by
  have hu_e0 : ((u : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = ![1, 0, 0] := by
    rw [hu, coe_uSL]
    exact uMat_mulVec_e0 _ _ _
  refine ⟨hu_e0, ?_, ?_, ?_⟩
  · rw [hu]
    exact uSL_mem_stabE0 _ _ _
  · exact (KSL3FrameAux.mem_rowT_zero_iff).mpr
      ⟨-(a / (1 + c ^ 3)), -(b / (1 + c ^ 3)), hu⟩
  · rw [KSL3FrameAux.mem_stabilizer_flagSpace_one_iff]
    exact ⟨1, by rw [hu_e0]; simp⟩

private theorem frame_transport_data
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ ρ f)
    (Kstar Pℓ : Subgroup ↥H) {h u : Matrix.SpecialLinearGroup (Fin 3) K}
    (hKstar_eq : Kstar = Hinf (MulAction.stabilizer ↥H
      ((preLine (W := W) hf h : Subgroup W) : Set W)))
    (hP' : Pℓ = MulAction.stabilizer ↥H
      ((preLine (W := W) hf h : Subgroup W) : Set W))
    (hu_rowT : u ∈ rowT (0 : Fin 3)) (hu_stabE0 : u ∈ stabE0 K)
    (hu_stab : u ∈ stabilizer (flagSpace 3 K 1))
    {M T : Matrix.SpecialLinearGroup (Fin 3) K} {g : ↥H}
    (hh'D : (h * u)⁻¹ * M * (h * u) = T) (hgM : rho3 ρ M = g) :
    ∃ (Φ : Matrix.SpecialLinearGroup (Fin 3) K →* ↥H) (a : Fin 3 → ↥H),
      Function.Injective Φ ∧ Function.Surjective Φ ∧ Φ T = g ∧ a 0 = 1 ∧
        CFSG.Open.pCoreOf 2 Kstar = (rowT (0 : Fin 3)).map Φ ∧
        Kstar = (stabE0 K).map Φ ∧
        Pℓ = (stabilizer (flagSpace 3 K 1)).map Φ ∧
        (∀ i, (CFSG.Open.pCoreOf 2 Kstar).map (MulAut.conj (a i)⁻¹).toMonoidHom =
          (rowT i).map Φ) ∧
        (∀ i, Kstar.map (MulAut.conj (a i)⁻¹).toMonoidHom =
          ((stabE0 K).map (MulAut.conj (sigma (K := K) i)).toMonoidHom).map Φ) ∧
        ∀ i, Pℓ.map (MulAut.conj (a i)⁻¹).toMonoidHom =
          ((stabilizer (flagSpace 3 K 1)).map
            (MulAut.conj (sigma (K := K) i)).toMonoidHom).map Φ := by
  let Φ : Matrix.SpecialLinearGroup (Fin 3) K →* ↥H :=
    (rho3 ρ).comp (MulAut.conj (h * u)).toMonoidHom
  have hΦ_apply (A : Matrix.SpecialLinearGroup (Fin 3) K) :
      Φ A = rho3 ρ ((h * u) * A * (h * u)⁻¹) := rfl
  have hΦ_inj : Function.Injective Φ :=
    (rho3_bijective hf).1.comp (MulAut.conj (h * u)).injective
  have hΦ_surj : Function.Surjective Φ :=
    (rho3_bijective hf).2.comp (MulAut.conj (h * u)).surjective
  have hΦT : Φ T = g := by
    rw [hΦ_apply]
    have h1 : (h * u) * T * (h * u)⁻¹ = M := by rw [← hh'D]; group
    rw [h1, hgM]
  let a : Fin 3 → ↥H := fun i => (Φ (sigma (K := K) i))⁻¹
  have hU : CFSG.Open.pCoreOf 2 Kstar = (rowT (0 : Fin 3)).map Φ := by
    rw [hKstar_eq, pCoreOf_hinf_eq_map_rowT hSL hf h]
    exact map_comp_conj_eq_map_comp_conj_mul (rho3 ρ) (rowT 0) hu_rowT
  have hKstar : Kstar = (stabE0 K).map Φ := by
    rw [hKstar_eq, hinf_stabilizer_eq_map_stabE0 hSL hf h]
    exact map_comp_conj_eq_map_comp_conj_mul (rho3 ρ) (stabE0 K) hu_stabE0
  have hP : Pℓ = (stabilizer (flagSpace 3 K 1)).map Φ := by
    rw [hP', stabilizer_preLine_eq_map_stabilizer hf h]
    exact map_comp_conj_eq_map_comp_conj_mul (rho3 ρ) (stabilizer (flagSpace 3 K 1)) hu_stab
  have ha : ∀ i, a i = (Φ (sigma (K := K) i))⁻¹ := fun _ => rfl
  have hCU (i : Fin 3) : (CFSG.Open.pCoreOf 2 Kstar).map
      (MulAut.conj (a i)⁻¹).toMonoidHom = (rowT i).map Φ := by
    rw [hU, map_conj_inv_eq_map_conj_sigma_map Φ a ha (rowT 0) i, sigma_conj_rowT]
  have hCK (i : Fin 3) : Kstar.map (MulAut.conj (a i)⁻¹).toMonoidHom =
      ((stabE0 K).map (MulAut.conj (sigma (K := K) i)).toMonoidHom).map Φ := by
    rw [hKstar, map_conj_inv_eq_map_conj_sigma_map Φ a ha (stabE0 K) i]
  have hCP (i : Fin 3) : Pℓ.map (MulAut.conj (a i)⁻¹).toMonoidHom =
      ((stabilizer (flagSpace 3 K 1)).map
        (MulAut.conj (sigma (K := K) i)).toMonoidHom).map Φ := by
    rw [hP, map_conj_inv_eq_map_conj_sigma_map Φ a ha (stabilizer (flagSpace 3 K 1)) i]
  have ha0 : a 0 = 1 := by
    show (Φ (sigma (K := K) 0))⁻¹ = 1
    rw [sigma_zero, map_one, inv_one]
  exact ⟨Φ, a, hΦ_inj, hΦ_surj, hΦT, ha0, hU, hKstar, hP, hCU, hCK, hCP⟩

theorem kSL3FrameTorus_holds :
    ∀ (W : Type) [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (n : ℕ),
      IsSLn ↥H 3 n → CFSG.Quasithin.BinaryNaturalSL H ⊤ ⊥ 3 n → 3 ≤ n →
        letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
        letI : MulAction ↥H W := MulAction.compHom W H.subtype
        letI : MulAction ↥H (Set W) := Set.mulActionSet
        ∀ S : Sylow 2 ↥H,
          letI : MulDistribMulAction ↥S W :=
            MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
          let ℓ : Subgroup W := fixedPointSubgroup ↥S W
          let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
          let Kstar : Subgroup ↥H := Hinf Pℓ
          let U : Subgroup ↥H := CFSG.Open.pCoreOf 2 Kstar
          ∀ g : ↥H, Odd (orderOf g) → g ^ 3 ≠ 1 →
            (∀ k ∈ Kstar, g * k * g⁻¹ * k⁻¹ ∈ U) →
            ∃ a : Fin 3 → ↥H, IsSL3Frame Kstar a ∧
              (∀ i, g ∈ Pℓ.map (MulAut.conj (a i)⁻¹).toMonoidHom) ∧
              ∀ i j, i ≠ j →
                ∃ y ∈ U.map (MulAut.conj (a i)⁻¹).toMonoidHom ⊔
                  U.map (MulAut.conj (a j)⁻¹).toMonoidHom,
                ∃ κ ∈ Kstar.map (MulAut.conj (a i)⁻¹).toMonoidHom ⊓
                  Pℓ.map (MulAut.conj (a j)⁻¹).toMonoidHom,
                  g = y * κ ∧ κ ∉ U.map (MulAut.conj (a i)⁻¹).toMonoidHom ∧
                    ∃ r, Odd r ∧ κ ^ r = 1 := by
  intro W _ _ H n hSLn hnat hn S ℓ Pℓ Kstar _ g hodd hg3 hcomm
  obtain ⟨K, hfield, hfinite, hK, ρ, hρ⟩ := hnat
  letI : Field K := hfield
  letI : Finite K := hfinite
  haveI : Fintype K := Fintype.ofFinite K
  letI : CharP K 2 := charP_two_of_card (by omega) hK
  haveI : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤ :=
    commutator_SL2_eq_top (four_le_card (by omega) hK)
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat (StatedSL 3 K)) hρ
  obtain ⟨h, hh⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf
    (CFSG.Quasithin.A4.isSylowTwoOf_map H S)
  obtain ⟨hKstar_eq, hP'⟩ := point_stabilizer_data hSL hf
    (fixedPointSubgroup_eq_preLine hf hh) rfl rfl
  obtain ⟨M, c, a₀, b, hc0, hgM, hc3, hc1, hD⟩ :=
    exists_torus_normal_form hSL hf hKstar_eq hcomm hodd hg3
  let T : Matrix.SpecialLinearGroup (Fin 3) K :=
    tSL ((Units.mk0 c hc0)⁻¹ * (Units.mk0 c hc0)⁻¹, Units.mk0 c hc0)
  obtain ⟨u, hh'D, hu_eq⟩ := exists_torus_factorization hc0 rfl hc3 hD
  obtain ⟨-, hu_stabE0, hu_rowT, hu_stab⟩ := torus_unit_props hu_eq
  obtain ⟨Φ, a, hΦ_inj, hΦ_surj, hΦT, ha0, hU, hKstar, hP, hCU, hCK, hCP⟩ :=
    frame_transport_data hSL hf Kstar Pℓ hKstar_eq hP' hu_rowT hu_stabE0 hu_stab hh'D hgM
  let t : Fin 3 → K := fun l => if l = 0 then c⁻¹ * c⁻¹ else c
  have hTdiag : (T : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal t :=
    KSL3FrameAux.tSL_diag_eq c hc0
  have hframe : IsSL3Frame Kstar a := by
    dsimp only [IsSL3Frame]
    refine ⟨ha0, frame_sup_eq_top Kstar Φ a hCU hΦ_surj,
      frame_pairwise_bot Kstar Φ a hCU hΦ_inj,
      frame_transvection_clause Kstar Φ a hCU hCK hΦ_inj⟩
  refine ⟨a, hframe, ?_, ?_⟩
  · intro i
    rw [← hΦT]
    exact hCP i ▸ mem_map_conj_sigma_map Φ i (conj_sigma_diagonal_mem_stabilizer hTdiag i)
  · exact frame_torus_decomposition Kstar Pℓ Φ a hCU hCK hCP hΦ_inj hc0 hc1 hTdiag hΦT hn hK

end CFSG.LocalAnalysis.UniquenessCase.UC22

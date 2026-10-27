module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3Block
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBasic

public section

namespace CFSG.Quasithin

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L

namespace QA12

variable {K : Type} [Field K]

omit [Field K] in
theorem exists_finset_card_four {K : Type} [Finite K] (hK : 4 ≤ Nat.card K) :
    ∃ s : Finset K, s.card = 4 := by
  have := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card] at hK
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4) (by
    simpa using hK)
  exact ⟨s, hs⟩

theorem exists_unit_ne_one [Finite K] (hK : 4 ≤ Nat.card K) : ∃ u : Kˣ, u ≠ 1 := by
  have h : 1 < Nat.card Kˣ := by
    rw [Nat.card_units]
    omega
  have : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.mp h
  exact exists_ne 1

@[expose] def dSL (u : Kˣ) : SpecialLinearGroup (Fin 2) K :=
  ⟨Matrix.diagonal ![(u : K), ((u⁻¹ : Kˣ) : K)], by
    simp [Matrix.det_diagonal, Fin.prod_univ_two]⟩

theorem dSL_one : dSL (1 : Kˣ) = (1 : SpecialLinearGroup (Fin 2) K) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [dSL, Matrix.diagonal]

theorem dSL_mul (u v : Kˣ) : dSL (u * v) = dSL u * dSL v := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [dSL, Matrix.diagonal, Matrix.mul_apply, mul_comm]

@[expose] def dHom : Kˣ →* SpecialLinearGroup (Fin 2) K where
  toFun := dSL
  map_one' := dSL_one
  map_mul' := dSL_mul

@[expose] noncomputable def tHom : Kˣ →* SpecialLinearGroup (Fin 3) K :=
  (embSL 0).comp dHom

theorem coe_tHom (u : Kˣ) :
    ((tHom u : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, 0, 0; 0, (u : K), 0; 0, 0, ((u⁻¹ : Kˣ) : K)] := by
  have e : tHom u = embSL 0 (dSL u) := rfl
  rw [e, coe_embSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embMat, dSL]

theorem tHom_mem_upperTriangular (u : Kˣ) : tHom u ∈ upperTriangular 3 K := by
  intro i j hij
  rw [coe_tHom]
  fin_cases i <;> fin_cases j <;> simp at hij ⊢

section Finite

variable [Finite K]

omit [Finite K] in
theorem tHom_mem_perfectCore (hK : ∃ s : Finset K, s.card = 4) (u : Kˣ) :
    tHom u ∈ perfectCore (Q3 K 0) :=
  embSL_mem_perfectCore hK 0 _

theorem det_block_one {m : SpecialLinearGroup (Fin 3) K} (hm : m ∈ perfectCore (Q3 K 1)) :
    (m : Matrix (Fin 3) (Fin 3) K) 0 0 * (m : Matrix (Fin 3) (Fin 3) K) 1 1 -
      (m : Matrix (Fin 3) (Fin 3) K) 0 1 * (m : Matrix (Fin 3) (Fin 3) K) 1 0 = 1 := by
  have h := (blk3 1 ⟨m, hm⟩).2
  rw [blk3_coe, Matrix.det_fin_two] at h
  simpa [blkAt_apply] using h

theorem eq_sq_of_tHom_eq_mul {u c : Kˣ} {m z : SpecialLinearGroup (Fin 3) K}
    (hm : m ∈ perfectCore (Q3 K 1))
    (hz : (z : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) (c : K)) (h : tHom u = m * z) :
    (u : K) = (c : K) ^ 2 := by
  have hdet := det_block_one hm
  have hmat : (tHom u : Matrix (Fin 3) (Fin 3) K) = (m : Matrix (Fin 3) (Fin 3) K) *
      scalar (Fin 3) (c : K) := by
    have h' := congrArg (fun x : SpecialLinearGroup (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) h
    simpa [Matrix.SpecialLinearGroup.coe_mul, hz] using h'
  rw [coe_tHom] at hmat
  have e00 := congrFun (congrFun hmat 0) 0
  have e11 := congrFun (congrFun hmat 1) 1
  have e01 := congrFun (congrFun hmat 0) 1
  have e10 := congrFun (congrFun hmat 1) 0
  simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply] at e00 e11 e01 e10
  have hc : (c : K) ≠ 0 := c.ne_zero
  rw [e01, e10] at hdet
  have h00 : (m : Matrix (Fin 3) (Fin 3) K) 0 0 = (c : K)⁻¹ := by
    field_simp
    linear_combination e00.symm
  have h11 : (m : Matrix (Fin 3) (Fin 3) K) 1 1 = (u : K) * (c : K)⁻¹ := by
    field_simp
    linear_combination e11.symm
  rw [h00, h11] at hdet
  field_simp at hdet
  linear_combination hdet

omit [Finite K] in
theorem exists_scalar_mul_tHom {d : SpecialLinearGroup (Fin 3) K} (hd : d ∈ diagSL 3 K)
    (hcube : ∀ a : K, a ≠ 0 → a ^ 3 = 1) :
    ∃ (c : Kˣ) (hc : c ^ 3 = 1) (u : Kˣ), d = scalarElement c hc * tHom u := by
  have hd' := mem_diagSL.mp hd
  have hdiag : Matrix.diagonal (Matrix.diag (d : Matrix (Fin 3) (Fin 3) K)) = d :=
    hd'.diagonal_diag
  have hdet : (d : Matrix (Fin 3) (Fin 3) K) 0 0 * (d : Matrix (Fin 3) (Fin 3) K) 1 1 *
      (d : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    have h := d.2
    rw [← hdiag, Matrix.det_diagonal, Fin.prod_univ_three] at h
    simpa using h
  obtain ⟨a, ha_def⟩ : ∃ a : K, (d : Matrix (Fin 3) (Fin 3) K) 0 0 = a := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b : K, (d : Matrix (Fin 3) (Fin 3) K) 1 1 = b := ⟨_, rfl⟩
  obtain ⟨c, hc_def⟩ : ∃ c : K, (d : Matrix (Fin 3) (Fin 3) K) 2 2 = c := ⟨_, rfl⟩
  rw [ha_def, hb_def, hc_def] at hdet
  have ha : a ≠ 0 := fun h => by simp [h] at hdet
  have hb : b ≠ 0 := fun h => by simp [h] at hdet
  have hc3 : (Units.mk0 a ha) ^ 3 = 1 := Units.ext (by simpa using hcube a ha)
  refine ⟨Units.mk0 a ha, hc3, Units.mk0 (b / a) (div_ne_zero hb ha), ?_⟩
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement, coe_tHom]
  have h3 := hcube a ha
  have hbc : b * c = a ^ 2 := by
    apply mul_left_cancel₀ ha
    linear_combination hdet - h3
  have hcc : c = a * (a / b) := by
    field_simp
    linear_combination hbc
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  all_goals first
    | exact ha_def
    | (rw [hb_def]; field_simp)
    | (rw [hc_def]; exact hcc)
    | exact hd' (by decide)

end Finite

end QA12

end CFSG.Quasithin

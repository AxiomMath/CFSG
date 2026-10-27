module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofSeitzExact
public import CFSG.LieType.SeitzGeneration.UnitaryHeisSeed
public import CFSG.LieType.SeitzGeneration.OuterCirc

public section

namespace CFSG.RankThree.PartTwo.Sec19

open Matrix CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem circ_column_facts (α c0 c1 c2 : K) :
    circMat α c0 c1 c2 *ᵥ ![1, 0, 0] = ![c0, c1, c2] ∧
      circMat α c0 c1 c2 *ᵥ ![0, 1, 0] = ![α * c2, c0, c1] ∧
      circMat α c0 c1 c2 *ᵥ ![0, 0, 1] = ![α * c1, α * c2, c0] := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i <;> fin_cases i <;>
    simp [circMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem norm_sum_mulVec_of_unitary (h : UnitaryFieldData ℓ f K) {P : Matrix (Fin 3) (Fin 3) K}
    (hP : (P.map h.bar)ᵀ * P = 1) (v : Fin 3 → K) :
    h.bar ((P *ᵥ v) 0) * (P *ᵥ v) 0 + h.bar ((P *ᵥ v) 1) * (P *ᵥ v) 1 +
        h.bar ((P *ᵥ v) 2) * (P *ᵥ v) 2 =
      h.bar (v 0) * v 0 + h.bar (v 1) * v 1 + h.bar (v 2) * v 2 := by
  have e00 : h.bar (P 0 0) * P 0 0 + h.bar (P 1 0) * P 1 0 + h.bar (P 2 0) * P 2 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrFun (congrFun hP 0) 0
  have e01 : h.bar (P 0 0) * P 0 1 + h.bar (P 1 0) * P 1 1 + h.bar (P 2 0) * P 2 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrFun (congrFun hP 0) 1
  have e02 : h.bar (P 0 0) * P 0 2 + h.bar (P 1 0) * P 1 2 + h.bar (P 2 0) * P 2 2 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrFun (congrFun hP 0) 2
  have e10 : h.bar (P 0 1) * P 0 0 + h.bar (P 1 1) * P 1 0 + h.bar (P 2 1) * P 2 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrFun (congrFun hP 1) 0
  have e11 : h.bar (P 0 1) * P 0 1 + h.bar (P 1 1) * P 1 1 + h.bar (P 2 1) * P 2 1 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrFun (congrFun hP 1) 1
  have e12 : h.bar (P 0 1) * P 0 2 + h.bar (P 1 1) * P 1 2 + h.bar (P 2 1) * P 2 2 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrFun (congrFun hP 1) 2
  have e20 : h.bar (P 0 2) * P 0 0 + h.bar (P 1 2) * P 1 0 + h.bar (P 2 2) * P 2 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrFun (congrFun hP 2) 0
  have e21 : h.bar (P 0 2) * P 0 1 + h.bar (P 1 2) * P 1 1 + h.bar (P 2 2) * P 2 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrFun (congrFun hP 2) 1
  have e22 : h.bar (P 0 2) * P 0 2 + h.bar (P 1 2) * P 1 2 + h.bar (P 2 2) * P 2 2 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using congrFun (congrFun hP 2) 2
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, map_add, map_mul]
  linear_combination (h.bar (v 0) * v 0) * e00 + (h.bar (v 0) * v 1) * e01 +
    (h.bar (v 0) * v 2) * e02 + (h.bar (v 1) * v 0) * e10 + (h.bar (v 1) * v 1) * e11 +
    (h.bar (v 1) * v 2) * e12 + (h.bar (v 2) * v 0) * e20 + (h.bar (v 2) * v 1) * e21 +
    (h.bar (v 2) * v 2) * e22

theorem col_norm_sum (h : UnitaryFieldData ℓ f K) (y : unitarySU ℓ f K 3) (v : Fin 3 → K)
    (hv : h.bar (v 0) * v 0 + h.bar (v 1) * v 1 + h.bar (v 2) * v 2 = 1) :
    h.bar ((((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) 0) *
        (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) 0 +
      h.bar ((((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) 1) *
        (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) 1 +
      h.bar ((((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) 2) *
        (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) 2 = 1 := by
  have hU := ((mem_unitarySU_iff h).1 y.2).2
  exact (norm_sum_mulVec_of_unitary h hU v).trans hv

theorem exists_coord_homology (h : UnitaryFieldData ℓ f K) {a : K} (ha : orderOf a = ℓ ^ f + 1)
    (j : Fin 3) :
    ∃ g : unitarySU ℓ f K 3,
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        homMat h a (a⁻¹ ^ 2 - a) (Pi.single j 1) := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [orderOf_zero] at ha
    omega
  have hna : h.bar a * a = 1 := by
    rw [bar_mul_self_eq_pow, ← ha]
    exact pow_orderOf_eq_one a
  have hinvN : ∀ x : K, h.bar x * x = 1 → h.bar x⁻¹ * x⁻¹ = 1 := fun x hx => by
    rw [map_inv₀, ← mul_inv, hx, inv_one]
  have hsqN : ∀ x : K, h.bar x * x = 1 → h.bar (x ^ 2) * x ^ 2 = 1 := fun x hx => by
    rw [map_pow, ← mul_pow, hx, one_pow]
  obtain ⟨g, hg⟩ := exists_homology_su h (ρ := a) (lam := a⁻¹ ^ 2) (n := 1) (Pi.single j 1)
    hna (hsqN _ (hinvN a hna)) (by field_simp) one_ne_zero
    (by fin_cases j <;> simp [Pi.single_apply])
  exact ⟨g, by rw [hg, div_one]⟩

theorem conj_homology_mem (h : UnitaryFieldData ℓ f K) {Q : Subgroup (unitarySU ℓ f K 3)}
    {a κ : K} {y g : unitarySU ℓ f K 3} (hyQ : y ∈ Q) (hgQ : g ∈ Q) {v : Fin 3 → K}
    (hg : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = homMat h a κ v) :
    ∃ g' ∈ Q, ((g' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a κ (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) := by
  have hyU := ((mem_unitarySU_iff h).1 y.2).2
  have hyP : ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ = 1 :=
    mul_eq_one_comm.2 hyU
  refine ⟨y * g * y⁻¹, Q.mul_mem (Q.mul_mem hyQ hgQ) (Q.inv_mem hyQ), ?_⟩
  have e : (((y * g * y⁻¹ : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ := by
    rw [← val_inv_eq_star h y]
    rfl
  rw [e, hg]
  exact conj_homMat h v hyP

theorem circ_mem_exactClosure {w α : K} {y : unitarySU ℓ f K 3} {c0 c1 c2 : K}
    (hy : ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = circMat α c0 c1 c2) :
    y ∈ Subgroup.closure (outerHeisExactFix ℓ f K w α) := by
  have hCm : heisC α ∈ outerHeisLines w α := Set.mem_insert _ _
  have hcomm : ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * heisC α =
      heisC α * ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [hy]
    exact circMat_comm α c0 c1 c2
  exact Subgroup.subset_closure ⟨heisC α, hCm, hcomm⟩

theorem coord_homology_mem_exactClosure (h : UnitaryFieldData ℓ f K) {w a α : K}
    (hw3 : w ^ 3 = 1) {g : unitarySU ℓ f K 3} (j : Fin 3)
    (hg : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) (Pi.single j 1)) :
    g ∈ Subgroup.closure (outerHeisExactFix ℓ f K w α) := by
  have hD' : heisD w = hD w := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [heisD, hD]
  have hDm : heisD w ∈ outerHeisLines w α := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hcomm : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * heisD w =
      heisD w * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [hg, hD']
    exact homMat_unit_comm_hD h _ _ w j
  exact Subgroup.subset_closure ⟨heisD w, hDm, hcomm⟩

end CFSG.RankThree.PartTwo.Sec19

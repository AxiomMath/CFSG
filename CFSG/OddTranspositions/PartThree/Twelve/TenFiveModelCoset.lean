module

public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveModelGen
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveModelSign
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveModelSpan
public import CFSG.Sporadic.Th.Max3.Data

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal

theorem exists_fiveReflOf_orth_sign_not {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    {c : Fin (k + 1) → ZMod 5} (hc : c ≠ 0) :
    ∃ u : Fin (k + 1) → ZMod 5, fiveForm k ε u u ≠ 0 ∧
      (IsSquare (fiveForm k ε u u) ↔ (!π) = true) ∧ fiveForm k ε u c = 0 := by
  let d : ZMod 5 := if π then 2 else 1
  have hd0 : d ≠ 0 := by unfold d; split_ifs <;> decide
  have he0 : fiveForm k ε (Pi.single (0 : Fin (k + 1)) 1) (Pi.single (0 : Fin (k + 1)) 1) ≠ 0 := by
    rw [fiveForm_single_single, if_pos rfl, fiveWeight_zero k ε (by omega)]
    decide
  obtain ⟨u, -, huc, huu⟩ := exists_fiveForm_orth_eq (k := k) hk ε he0 c hd0
  refine ⟨u, ?_, ?_, huc⟩
  · rw [huu]; exact hd0
  · rw [huu]
    unfold d
    cases π <;> simp [isSquare_one_zmod5, not_isSquare_two_zmod5]

theorem fiveReflOf_mem_closure_union {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    {c u w : Fin (k + 1) → ZMod 5}
    (hu : fiveForm k ε u u ≠ 0) (huπ : IsSquare (fiveForm k ε u u) ↔ (!π) = true)
    (huc : fiveForm k ε u c = 0)
    (hw : fiveForm k ε w w ≠ 0) (hwc : fiveForm k ε w c = 0) :
    fiveReflOf k ε w ∈
      Subgroup.closure (fiveReflectionsFixing k ε π c ∪ {fiveReflOf k ε u}) := by
  by_cases hsign : IsSquare (fiveForm k ε w w) ↔ π = true
  · apply Subgroup.subset_closure
    left
    refine ⟨fiveReflOf_mem hw hsign, ?_⟩
    rw [fiveReflOf_mulVec, fiveForm_comm k ε c w, hwc, mul_zero, zero_mul, zero_smul]
    simp
  · have hsign' : IsSquare (fiveForm k ε w w) ↔ (!π) = true := by
      by_cases hsq : IsSquare (fiveForm k ε w w) <;> cases π <;> simp_all
    have hL : fiveReflOf k ε w * fiveReflOf k ε u ∈
        Subgroup.closure (fiveReflectionsFixing k ε π c) :=
      fiveReflOf_mul_mem_closure_fiveReflectionsFixing hk ε π c hw hsign' hu huπ hwc huc
    have hru : fiveReflOf k ε u * fiveReflOf k ε u = 1 := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_one]
      exact fiveReflMatrix_mul_self k ε u
    have hr : fiveReflOf k ε w =
        (fiveReflOf k ε w * fiveReflOf k ε u) * fiveReflOf k ε u := by
      rw [mul_assoc, hru, mul_one]
    rw [hr]
    exact Subgroup.mul_mem _
      (Subgroup.closure_mono (fun x hx => Or.inl hx) hL)
      (Subgroup.subset_closure (Set.mem_union_right _ rfl))

end CFSG.OddTranspositions.PartThree

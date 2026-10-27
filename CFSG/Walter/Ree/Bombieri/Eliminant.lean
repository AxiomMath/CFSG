module

public import CFSG.Walter.Ree.Bombieri.MatrixDef
public import CFSG.Walter.Ree.Bombieri.DetDegree

public section

namespace CFSG.Walter.Ree.Bombieri

namespace Elim

open MvPolynomial

abbrev M6 := MvPolynomial (Fin 6) (ZMod 3)

abbrev A5 := MvPolynomial (Fin 5) (ZMod 3)

@[expose] noncomputable def varsP : ℕ → M6
  | 0 => X 1 | 1 => X 2 | 2 => X 3 | 3 => X 4 | 4 => X 0 | _ => 0

@[expose] noncomputable def varsP' : ℕ → M6
  | 0 => X 2 | 1 => X 3 | 2 => X 4 | 3 => X 5 | 4 => X 0 | _ => 0

noncomputable def Pmv : M6 := (matOf varsP).det

noncomputable def Pmv' : M6 := (matOf varsP').det

theorem Pmv_eq : Pmv = (matOf varsP).det := by rw [Pmv]

theorem Pmv'_eq : Pmv' = (matOf varsP').det := by rw [Pmv']

@[expose] def dvP (v : ℕ) : ℕ → ℕ
  | 0 => if v = 1 then 1 else 0
  | 1 => if v = 2 then 1 else 0
  | 2 => if v = 3 then 1 else 0
  | 3 => if v = 4 then 1 else 0
  | 4 => if v = 0 then 1 else 0
  | _ => 0

@[expose] def dvP' (v : ℕ) : ℕ → ℕ
  | 0 => if v = 2 then 1 else 0
  | 1 => if v = 3 then 1 else 0
  | 2 => if v = 4 then 1 else 0
  | 3 => if v = 5 then 1 else 0
  | 4 => if v = 0 then 1 else 0
  | _ => 0

@[expose] def daOf (dv : ℕ → ℕ) : ℕ → ℕ := fun k => (atomDef k).degB dv fun _ => 0

@[expose] def entDeg (dv : ℕ → ℕ) (i j : Fin 12) : ℕ := (ent i j).degB dv (daOf dv)

theorem degreeOf_matOf_le {ρ : ℕ → M6} {v : Fin 6} {dv : ℕ → ℕ}
    (hρ : ∀ i, (ρ i).degreeOf v ≤ dv i) (i j : Fin 12) :
    ((matOf ρ) i j).degreeOf v ≤ entDeg dv i j := by
  refine PE.degreeOf_eval_le v hρ (fun k => ?_) (ent i j)
  exact PE.degreeOf_eval_le v hρ (fun _ => by simp) (atomDef k)

theorem degreeOf_det_matOf_le {ρ : ℕ → M6} {v : Fin 6} {dv : ℕ → ℕ}
    (hρ : ∀ i, (ρ i).degreeOf v ≤ dv i) (r k : Fin 12 → ℕ)
    (h : ∀ i j, entDeg dv i j ≤ r i + k j) :
    (matOf ρ).det.degreeOf v ≤ ∑ i, r i + ∑ j, k j :=
  degreeOf_det_le v _ r k fun i j => (degreeOf_matOf_le hρ i j).trans (h i j)

theorem degreeOf_varsP (v : Fin 6) (i : ℕ) : (varsP i).degreeOf v ≤ dvP v i := by
  fin_cases v <;> rcases i with _ | _ | _ | _ | _ | i <;> simp [varsP, dvP, degreeOf_X]

theorem degreeOf_varsP' (v : Fin 6) (i : ℕ) : (varsP' i).degreeOf v ≤ dvP' v i := by
  fin_cases v <;> rcases i with _ | _ | _ | _ | _ | i <;> simp [varsP', dvP', degreeOf_X]

@[expose] def rY : Fin 12 → ℕ := ![3, 0, 0, 0, 6, 22, 22, 3, 6, 22, 4, 6]
@[expose] def kY : Fin 12 → ℕ := ![2, 2, 2, 0, 2, 2, 2, 2, 2, 2, 0, 2]
@[expose] def rZ0 : Fin 12 → ℕ := ![0, 0, 0, 0, 3, 22, 22, 4, 6, 22, 3, 6]
@[expose] def kZ0 : Fin 12 → ℕ := ![8, 0, 2, 2, 4, 5, 5, 0, 2, 2, 2, 2]
@[expose] def rZ1 : Fin 12 → ℕ := ![1, 0, 0, 0, 5, 15, 14, 2, 6, 15, 2, 6]
@[expose] def kZ1 : Fin 12 → ℕ := ![3, 1, 2, 1, 2, 1, 2, 0, 0, 0, 0, 0]
@[expose] def rZ2 : Fin 12 → ℕ := ![0, 0, 0, 0, 4, 10, 10, 0, 3, 10, 0, 3]
@[expose] def kZ2 : Fin 12 → ℕ := ![0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0]
@[expose] def rZ3 : Fin 12 → ℕ := ![0, 0, 0, 0, 0, 4, 4, 0, 0, 4, 0, 0]
@[expose] def k0 : Fin 12 → ℕ := fun _ => 0

theorem entDeg_y : ∀ i j, entDeg (dvP 0) i j ≤ rY i + kY j := by decide


theorem entDeg_z0 : ∀ i j, entDeg (dvP 1) i j ≤ rZ0 i + kZ0 j := by decide
theorem entDeg_z1 : ∀ i j, entDeg (dvP 2) i j ≤ rZ1 i + kZ1 j := by decide
theorem entDeg_z2 : ∀ i j, entDeg (dvP 3) i j ≤ rZ2 i + kZ2 j := by decide
theorem entDeg_z3 : ∀ i j, entDeg (dvP 4) i j ≤ rZ3 i + k0 j := by decide
theorem entDeg_z4 : ∀ i j, entDeg (dvP 5) i j ≤ k0 i + k0 j := by decide
theorem entDeg'_y : ∀ i j, entDeg (dvP' 0) i j ≤ rY i + kY j := by decide
theorem entDeg'_z0 : ∀ i j, entDeg (dvP' 1) i j ≤ k0 i + k0 j := by decide
theorem entDeg'_z1 : ∀ i j, entDeg (dvP' 2) i j ≤ rZ0 i + kZ0 j := by decide
theorem entDeg'_z2 : ∀ i j, entDeg (dvP' 3) i j ≤ rZ1 i + kZ1 j := by decide
theorem entDeg'_z3 : ∀ i j, entDeg (dvP' 4) i j ≤ rZ2 i + kZ2 j := by decide
theorem entDeg'_z4 : ∀ i j, entDeg (dvP' 5) i j ≤ rZ3 i + k0 j := by decide

theorem degreeOf_Pmv : Pmv.degreeOf 0 ≤ 114 ∧ Pmv.degreeOf 1 ≤ 122 ∧ Pmv.degreeOf 2 ≤ 78 ∧
    Pmv.degreeOf 3 ≤ 42 ∧ Pmv.degreeOf 4 ≤ 12 ∧ Pmv.degreeOf 5 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (degreeOf_det_matOf_le (degreeOf_varsP 0) _ _ entDeg_y).trans (by decide)
  · exact (degreeOf_det_matOf_le (degreeOf_varsP 1) _ _ entDeg_z0).trans (by decide)
  · exact (degreeOf_det_matOf_le (degreeOf_varsP 2) _ _ entDeg_z1).trans (by decide)
  · exact (degreeOf_det_matOf_le (degreeOf_varsP 3) _ _ entDeg_z2).trans (by decide)
  · exact (degreeOf_det_matOf_le (degreeOf_varsP 4) _ _ entDeg_z3).trans (by decide)
  · exact Nat.le_zero.mp
      ((degreeOf_det_matOf_le (degreeOf_varsP 5) _ _ entDeg_z4).trans (by decide))

theorem degreeOf_Pmv' : Pmv'.degreeOf 0 ≤ 114 ∧ Pmv'.degreeOf 1 = 0 ∧ Pmv'.degreeOf 2 ≤ 122 ∧
    Pmv'.degreeOf 3 ≤ 78 ∧ Pmv'.degreeOf 4 ≤ 42 ∧ Pmv'.degreeOf 5 ≤ 12 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (degreeOf_det_matOf_le (degreeOf_varsP' 0) _ _ entDeg'_y).trans (by decide)
  · exact Nat.le_zero.mp
      ((degreeOf_det_matOf_le (degreeOf_varsP' 1) _ _ entDeg'_z0).trans (by decide))
  · exact (degreeOf_det_matOf_le (degreeOf_varsP' 2) _ _ entDeg'_z1).trans (by decide)
  · exact (degreeOf_det_matOf_le (degreeOf_varsP' 3) _ _ entDeg'_z2).trans (by decide)
  · exact (degreeOf_det_matOf_le (degreeOf_varsP' 4) _ _ entDeg'_z3).trans (by decide)
  · exact (degreeOf_det_matOf_le (degreeOf_varsP' 5) _ _ entDeg'_z4).trans (by decide)

end Elim

end CFSG.Walter.Ree.Bombieri

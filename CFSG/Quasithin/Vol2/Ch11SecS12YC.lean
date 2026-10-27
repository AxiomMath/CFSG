module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aL3E

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def dg3 : (Fin 3 → Fˣ) →* GL (Fin 3) F where
  toFun x := ⟨diagonal fun i => (x i : F), diagonal fun i => ((x i)⁻¹ : Fˣ), by
      rw [diagonal_mul_diagonal]
      simp, by
      rw [diagonal_mul_diagonal]
      simp⟩
  map_one' := by
    ext i j
    simp [diagonal_apply, Matrix.one_apply]
  map_mul' x y := by
    ext i j
    simp only [Units.val_mul, Pi.mul_apply, diagonal_mul_diagonal]

theorem dg3_coe (x : Fin 3 → Fˣ) :
    ((dg3 x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal fun i => (x i : F) := rfl

@[expose] noncomputable def dgP : (Fin 3 → Fˣ) →* PGL3 F := ProjGenLinGroup.mk.comp dg3

theorem dgP_apply (x : Fin 3 → Fˣ) : dgP x = ProjGenLinGroup.mk (dg3 x : GL (Fin 3) F) := rfl

theorem dgP_eq (x : Fin 3 → Fˣ) : dgP x = dgP ![1, x 1 * (x 0)⁻¹, x 2 * (x 0)⁻¹] := by
  rw [dgP_apply, dgP_apply, ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨(x 0)⁻¹, Units.ext ?_⟩
  rw [Units.val_mul, dg3_coe, dg3_coe, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

theorem card_range_dgP_le [Finite F] : Nat.card ↥(dgP (F := F)).range ≤ Nat.card (Fˣ × Fˣ) := by
  have hs : Function.Surjective fun yz : Fˣ × Fˣ =>
      (⟨dgP ![1, yz.1, yz.2], ⟨_, rfl⟩⟩ : ↥(dgP (F := F)).range) := by
    rintro ⟨_, x, rfl⟩
    exact ⟨(x 1 * (x 0)⁻¹, x 2 * (x 0)⁻¹), Subtype.ext (dgP_eq x).symm⟩
  exact Nat.card_le_card_of_surjective _ hs

@[expose] def perm3 : GL (Fin 3) F :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem det_perm3 : ((perm3 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  show (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) F).det = 1
  rw [Matrix.det_fin_three]
  simp

theorem perm3_conj_dg3 (x : Fin 3 → Fˣ) :
    (perm3 : GL (Fin 3) F) * dg3 x * perm3⁻¹ = dg3 ![x 2, x 0, x 1] := by
  apply Units.ext
  show (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) F) *
    diagonal (fun i => (x i : F)) * !![0, 1, 0; 0, 0, 1; 1, 0, 0] =
      diagonal (fun i => ((![x 2, x 0, x 1] i : Fˣ) : F))
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_three] <;> simp

theorem perm3_inv_conj_dg3 (x : Fin 3 → Fˣ) :
    (perm3 : GL (Fin 3) F)⁻¹ * dg3 x * perm3 = dg3 ![x 1, x 2, x 0] := by
  apply Units.ext
  show (!![0, 1, 0; 0, 0, 1; 1, 0, 0] : Matrix (Fin 3) (Fin 3) F) *
    diagonal (fun i => (x i : F)) * !![0, 0, 1; 1, 0, 0; 0, 1, 0] =
      diagonal (fun i => ((![x 1, x 2, x 0] i : Fˣ) : F))
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_three] <;> simp

theorem perm3_conj_mem_range {y : PGL3 F} (hy : y ∈ (dgP (F := F)).range) :
    ProjGenLinGroup.mk (perm3 : GL (Fin 3) F) * y * (ProjGenLinGroup.mk perm3)⁻¹ ∈
        (dgP (F := F)).range ∧
      (ProjGenLinGroup.mk (perm3 : GL (Fin 3) F))⁻¹ * y * ProjGenLinGroup.mk perm3 ∈
        (dgP (F := F)).range := by
  obtain ⟨x, rfl⟩ := hy
  refine ⟨⟨![x 2, x 0, x 1], ?_⟩, ⟨![x 1, x 2, x 0], ?_⟩⟩
  · rw [dgP_apply, dgP_apply, ← map_inv, ← map_mul, ← map_mul, perm3_conj_dg3]
  · rw [dgP_apply, dgP_apply, ← map_inv, ← map_mul, ← map_mul, perm3_inv_conj_dg3]

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

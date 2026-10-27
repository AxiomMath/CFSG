module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321W

public section

namespace CFSG.Quasithin.H13.NFa2

open Matrix

@[expose] def pluck (v : Fin 6 → ZMod 2) : ZMod 2 := v 0 * v 5 + v 1 * v 4 + v 2 * v 3

theorem pluck_wedgeMat4_e0 (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    pluck (B5FinWedge.wedgeMat4 g *ᵥ Pi.single 0 1) = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  simp [pluck, Matrix.mulVec, dotProduct, Fin.sum_univ_six, B5FinWedge.wedgeMat4,
    B5FinWedge.pr4, Matrix.of_apply, Pi.single_apply]
  linear_combination (g 0 0 * g 2 1 - g 0 1 * g 2 0) * (g 1 0 * g 3 1 - g 1 1 * g 3 0) * h2

@[expose] def lamS : Fin 5 → (Fin 6 → ZMod 2) :=
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 1], ![0, 1, 0, 0, 0, 1], ![0, 1, 1, 1, 1, 1],
    ![1, 1, 0, 1, 1, 1]]

@[expose] def lamG : Fin 5 → Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  ![!![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0],
    !![0, 0, 0, 1; 0, 1, 0, 0; 0, 1, 1, 0; 1, 0, 0, 0],
    !![0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 1, 0],
    !![0, 1, 0, 0; 0, 1, 0, 1; 1, 0, 0, 0; 1, 1, 1, 0],
    !![0, 1, 0, 0; 1, 0, 0, 0; 1, 1, 0, 1; 0, 1, 1, 0]]

theorem lamG_det (i : Fin 5) : (lamG i).det = 1 := by
  fin_cases i <;> decide +kernel

theorem lamS_k1 (i : Fin 5) : lamS i 5 = 1 := by
  fin_cases i <;> rfl

theorem wedgeMat4_lamG (i : Fin 5) :
    B5FinWedge.wedgeMat4 (lamG i) *ᵥ Pi.single 0 1 = lamS i := by
  fin_cases i <;> decide +kernel

private theorem no_transvection_aux :
    ∀ w : Fin 6 → ZMod 2, (∀ i : Fin 5, pluck (lamS i + w) = 0) → w = 0 := by
  decide +kernel

theorem no_transvection (w : Fin 6 → ZMod 2) (h : ∀ i, pluck (lamS i + w) = 0) : w = 0 :=
  no_transvection_aux w h

theorem exists_g_basis (k : Fin 6) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2),
      B5FinWedge.wedgeMat4 (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ Pi.single 0 1 =
        Pi.single k 1 := by
  fin_cases k
  · refine ⟨⟨!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1], ?_⟩, ?_⟩ <;> decide +kernel
  · refine ⟨⟨!![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1], ?_⟩, ?_⟩ <;> decide +kernel
  · refine ⟨⟨!![1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 0, 1, 0, 0], ?_⟩, ?_⟩ <;> decide +kernel
  · refine ⟨⟨!![0, 0, 1, 0; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1], ?_⟩, ?_⟩ <;> decide +kernel
  · refine ⟨⟨!![0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0], ?_⟩, ?_⟩ <;> decide +kernel
  · refine ⟨⟨!![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0], ?_⟩, ?_⟩ <;> decide +kernel

@[expose] def gAmat : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem gAmat_det : gAmat.det = 1 := by
  decide +kernel

@[expose] def gA : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) := ⟨gAmat, gAmat_det⟩

theorem gA_mem_P2 : gA ∈ L3321.P2 := by
  rw [L3321.mem_P2_iff]
  intro k l hl hk
  fin_cases k <;> fin_cases l <;>
    first | rfl | exact absurd hl (by decide) | exact absurd hk (by decide)

theorem gA_pow_three : gA ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  decide +kernel

theorem wedgeMat4_gA_basis :
    B5FinWedge.wedgeMat4 gAmat *ᵥ Pi.single 1 1 = Pi.single 3 1 ∧
    B5FinWedge.wedgeMat4 gAmat *ᵥ Pi.single 3 1 = Pi.single 1 1 + Pi.single 3 1 ∧
    B5FinWedge.wedgeMat4 gAmat *ᵥ Pi.single 2 1 = Pi.single 4 1 ∧
    B5FinWedge.wedgeMat4 gAmat *ᵥ Pi.single 4 1 = Pi.single 2 1 + Pi.single 4 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

end CFSG.Quasithin.H13.NFa2

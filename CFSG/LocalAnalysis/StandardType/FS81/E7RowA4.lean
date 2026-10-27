module

public import CFSG.LocalAnalysis.StandardType.FS81.E7RowA3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.E7Row

open scoped Matrix

variable {X : Subgroup (GL (Fin 8) (ZMod 3))}

theorem orb1_mul {x : GL (Fin 8) (ZMod 3)} (hx : x ∈ X ⊓ fixE0 7) {v : Coords 8} (hv : v ∈ orb1 X) :
    (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v ∈ orb1 X := by
  obtain ⟨y, hy, rfl⟩ := hv
  exact ⟨x * y, Subgroup.mul_mem _ hx hy, by rw [Units.val_mul, Matrix.mulVec_mulVec]⟩

theorem X1_b8 (h : CoreHyp X) {δ : ZMod 3} (hδ : δ = 1 ∨ δ = -1)
    (horb : ∀ v, v ∈ orb1 X ↔ IsRoot7 δ v) {x : GL (Fin 8) (ZMod 3)} (hx : x ∈ X ⊓ fixE0 7)
    (u w : Coords 8) :
    b8 ((x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ u) ((x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ w) =
      b8 u w :=
  b8_mulVec_of_gram (gram_of_roots7 hδ (mem_fixE0.mp hx.2) (h.hA x hx.1 (mem_fixE0.mp hx.2))
    (fun r hr => (horb _).mp (orb1_mul hx ((horb r).mpr hr)))) u w

@[expose] def reflM (r : Coords 8) : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  1 + Matrix.vecMulVec r (gramD *ᵥ r)

theorem reflM_mulVec (r w : Coords 8) : reflM r *ᵥ w = w + b8 w r • r := by
  rw [reflM, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, b8,
    dotProduct_comm]

theorem gramD_mulVec_single (j : Fin 8) :
    gramD *ᵥ Pi.single j 1 = Pi.single j (if j.val < 2 then 1 else 2) := by
  funext i
  rw [gramD, Matrix.mulVec_diagonal]
  by_cases h : i = j
  · subst h
    simp
  · simp [h]

theorem b8_single (w : Coords 8) (j : Fin 8) :
    b8 w (Pi.single j 1) = w j * (if j.val < 2 then 1 else 2) := by
  rw [b8, gramD_mulVec_single, dotProduct_single]

theorem matrix_ext_mulVec {A B : Matrix (Fin 8) (Fin 8) (ZMod 3)} (h : ∀ w : Coords 8, A *ᵥ w = B *ᵥ w) :
    A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  rwa [Matrix.mulVec_single_one, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.col_apply] at this

theorem t1_eq_reflM : Gen.t1.mat = reflM (Pi.single 1 1) := by
  apply matrix_ext_mulVec
  intro w
  rw [Gen.mat_mulVec, t1_act_eq, reflM_mulVec, b8_single]
  rw [if_pos (by decide), mul_one]

theorem conj_reflM {x : GL (Fin 8) (ZMod 3)}
    (hiso : ∀ u w : Coords 8, b8 ((x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ u)
      ((x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ w) = b8 u w) (r : Coords 8) :
    ((x : Matrix (Fin 8) (Fin 8) (ZMod 3)) * reflM r * ((x⁻¹ : GL (Fin 8) (ZMod 3)) :
      Matrix (Fin 8) (Fin 8) (ZMod 3))) = reflM ((x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ r) := by
  apply matrix_ext_mulVec
  intro w
  have hb : b8 (((x⁻¹ : GL (Fin 8) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ w) r =
      b8 w ((x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ r) := by
    rw [← hiso, mulVec_mulVec_inv]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, reflM_mulVec, reflM_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_smul, mulVec_mulVec_inv, hb]

theorem exists_reflM_mem (h : CoreHyp X) {δ : ZMod 3} (hδ : δ = 1 ∨ δ = -1)
    (horb : ∀ v, v ∈ orb1 X ↔ IsRoot7 δ v) {r : Coords 8} (hr : IsRoot7 δ r) :
    ∃ g ∈ X ⊓ fixE0 7, (g : Matrix (Fin 8) (Fin 8) (ZMod 3)) = reflM r := by
  obtain ⟨x, hx, hxr⟩ := (horb r).mpr hr
  obtain ⟨y, hy, hyt⟩ := h.exists_fix (Gen.mat_mem (g := .t1) trivial)
  refine ⟨x * y * x⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy) (Subgroup.inv_mem _ hx), ?_⟩
  rw [Units.val_mul, Units.val_mul, hyt, t1_eq_reflM, conj_reflM (X1_b8 h hδ horb hx), hxr]

end CFSG.StandardType.FrameRoute.FS81.E7Row

end

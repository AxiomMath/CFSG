module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Wr
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80Gen

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.Quasithin.A38c15 CFSG.Quasithin.B6 CFSG.QuasithinUnique
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]

theorem commutator_monoC_le_diagC : ⁅monoC p, monoC p⁆ ≤ diagC p :=
  commutator_le_of_relIndex_eq_two relIndex_diagC_monoC

theorem diagT_comm {a b : SL(3, ZMod p)} (ha : a ∈ diagT p) (hb : b ∈ diagT p) :
    a * b = b * a := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6,
      mul_comm]

theorem diagC_comm {a b : PSL3 p} (ha : a ∈ diagC p) (hb : b ∈ diagC p) : a * b = b * a := by
  obtain ⟨a, ha, rfl⟩ := ha
  obtain ⟨b, hb, rfl⟩ := hb
  rw [← map_mul, ← map_mul, diagT_comm ha hb]

@[expose] noncomputable def xE (i : (ZMod p)ˣ) : SL(3, ZMod p) := diagHom p (i, 1)

@[expose] noncomputable def xO (i : (ZMod p)ˣ) : SL(3, ZMod p) := diagMat i i⁻¹ 1 (by simp)

theorem coe_xE (i : (ZMod p)ˣ) :
    ((xE i : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      Matrix.diagonal ![(i : ZMod p), 1, ((i * 1)⁻¹ : (ZMod p)ˣ)] := rfl

theorem coe_xO (i : (ZMod p)ˣ) :
    ((xO i : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      Matrix.diagonal ![(i : ZMod p), ((i⁻¹ : (ZMod p)ˣ) : ZMod p), 1] := rfl

theorem xE_mul_eq (i : (ZMod p)ˣ) {g : SL(3, ZMod p)}
    (h02 : (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 2 = 0)
    (h12 : (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 2 = 0)
    (h20 : (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 0 = 0)
    (h21 : (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 1 = 0)
    (h00 : (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 0 = 0)
    (h11 : (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 1 = 0) :
    xE i * g = xO i * g * xE i := by
  have hinv : ((i⁻¹ : (ZMod p)ˣ) : ZMod p) * (i : ZMod p) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel]
    rfl
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, coe_xE, coe_xO]
  exact diag_mul_eq hinv (by rw [mul_one]) h02 h12 h20 h21 h00 h11

end CFSG.Quasithin.E2P.Asc80

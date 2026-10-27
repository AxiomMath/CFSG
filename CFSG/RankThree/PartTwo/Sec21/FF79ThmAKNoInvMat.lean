module

public import CFSG.RankThree.PartTwo.Sec21.FF79ThmAKNoInvAbs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open Matrix

theorem field_card_two_add_self {F : Type} [Field F] (hF : Nat.card F = 2) (x : F) :
    x + x = 0 := by
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (0 : F)).1 hF
  have hyy : y + y = 0 := by
    by_contra h
    exact hy (by simpa using huniq _ h)
  by_cases hx : x = 0
  · simp [hx]
  · rw [huniq x hx]; exact hyy

def matAddHom {F : Type} [Field F] {n : ℕ} (A : Matrix (Fin n) (Fin n) F) :
    (Fin n → F) →+ (Fin n → F) where
  toFun v := A *ᵥ v
  map_zero' := Matrix.mulVec_zero A
  map_add' := Matrix.mulVec_add A

theorem ff79_noInv_gl {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) (n : ℕ)
    (hn : n = 4 ∨ n = 5) (Z T : GL (Fin n) F) (hZ : Z ^ 5 = 1) (hZ1 : Z ≠ 1) (hT : T ^ 2 = 1)
    (hT1 : T ≠ 1) (hc : Z * T = T * Z) : False := by
  have hV : Nat.card (Fin n → F) = 2 ^ n := by
    rw [Nat.card_fun, hF, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hZ5 : (Z : Matrix (Fin n) (Fin n) F) * Z * Z * Z * Z = 1 := by
    have := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) hZ
    simpa [pow_succ] using this
  have hZ5' : (Z : Matrix (Fin n) (Fin n) F) * (Z * (Z * (Z * Z))) = 1 := by
    simpa [mul_assoc] using hZ5
  have hT2 : (T : Matrix (Fin n) (Fin n) F) * T = 1 := by
    have := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) hT
    simpa [pow_succ] using this
  have hc' : (Z : Matrix (Fin n) (Fin n) F) * T = T * Z := by
    simpa using congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) hc
  refine ff79_noInv_abs n hn hV (fun v => ?_) (matAddHom (Z : Matrix (Fin n) (Fin n) F))
    (matAddHom (T : Matrix (Fin n) (Fin n) F)) (fun v => ?_) ?_ (fun v => ?_) ?_ (fun v => ?_)
  · funext i
    exact field_card_two_add_self hF _
  · simp only [matAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mulVec_mulVec, hZ5',
      Matrix.one_mulVec]
  · by_contra h
    push_neg at h
    apply hZ1
    apply Units.ext
    rw [Matrix.ext_iff_mulVec]
    intro v
    simpa [matAddHom] using h v
  · simp only [matAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mulVec_mulVec, hT2,
      Matrix.one_mulVec]
  · by_contra h
    push_neg at h
    apply hT1
    apply Units.ext
    rw [Matrix.ext_iff_mulVec]
    intro v
    simpa [matAddHom] using h v
  · simp only [matAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mulVec_mulVec, hc']

end CFSG.RankThree.PartTwo.Sec21.FF79

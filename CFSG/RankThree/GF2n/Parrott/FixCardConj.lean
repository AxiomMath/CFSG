module

public import Certificates.Data.ParrottSpin
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.RankThree.GF2n.Parrott

theorem fixCard_conj_of_mul_eq_one (a b m : Matrix (Fin 8) (Fin 8) (ZMod 2)) (hba : b * a = 1)
    (hab : a * b = 1) : fixCard (a * m * b) = fixCard m := by
  unfold fixCard
  apply Fintype.card_congr
  have key1 : b * (a * m * b) = m * b := by
    calc b * (a * m * b) = (b * a) * (m * b) := by simp [Matrix.mul_assoc]
      _ = m * b := by rw [hba, one_mul]
  have key2 : a * m * b * a = a * m := by
    calc a * m * b * a = a * m * (b * a) := by simp [Matrix.mul_assoc]
      _ = a * m := by rw [hba, mul_one]
  refine
    { toFun := fun v => ⟨b.mulVec v.1, ?_⟩
      invFun := fun w => ⟨a.mulVec w.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have h1 : (a * m * b).mulVec v.1 = v.1 := v.2
    calc m.mulVec (b.mulVec v.1) = (m * b).mulVec v.1 := by rw [Matrix.mulVec_mulVec]
      _ = (b * (a * m * b)).mulVec v.1 := by rw [key1]
      _ = b.mulVec ((a * m * b).mulVec v.1) := by rw [Matrix.mulVec_mulVec]
      _ = b.mulVec v.1 := by rw [h1]
  · have h1 : m.mulVec w.1 = w.1 := w.2
    calc (a * m * b).mulVec (a.mulVec w.1) = (a * m * b * a).mulVec w.1 := by
          rw [Matrix.mulVec_mulVec]
      _ = (a * m).mulVec w.1 := by rw [key2]
      _ = a.mulVec (m.mulVec w.1) := by rw [Matrix.mulVec_mulVec]
      _ = a.mulVec w.1 := by rw [h1]
  · intro v
    apply Subtype.ext
    show a.mulVec (b.mulVec v.1) = v.1
    rw [Matrix.mulVec_mulVec, hab, Matrix.one_mulVec]
  · intro w
    apply Subtype.ext
    show b.mulVec (a.mulVec w.1) = w.1
    rw [Matrix.mulVec_mulVec, hba, Matrix.one_mulVec]

theorem fixCard_conj (P M : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
    fixCard (((P * M * P⁻¹ : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
        Matrix (Fin 8) (Fin 8) (ZMod 2))) =
      fixCard (((M : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
        Matrix (Fin 8) (Fin 8) (ZMod 2))) := by
  have h1 := fixCard_conj_of_mul_eq_one (P : Matrix (Fin 8) (Fin 8) (ZMod 2))
    ((P⁻¹ : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2))
    (M : Matrix (Fin 8) (Fin 8) (ZMod 2)) P.inv_mul P.mul_inv
  rw [← h1, Units.val_mul, Units.val_mul]

end CFSG.RankThree.GF2n.Parrott

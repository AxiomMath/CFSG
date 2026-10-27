module

public import CFSG.LocalAnalysis.StandardType.GGF4WeylData
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.StandardType.F4Model

@[expose] def classValue (k : Fin 2) (i : Fin 4) : Multiplicative (ZMod 2) :=
  Multiplicative.ofAdd (if i.val / 2 = k.val then 1 else 0)

theorem classValue_liftable (k : Fin 2) :
    CoxeterMatrix.F₄.IsLiftable (classValue k) := by
  fin_cases k <;> intro i j <;> fin_cases i <;> fin_cases j <;> decide +kernel

noncomputable def classCharacter {W : Type} [Group W]
    (cs : CoxeterSystem CoxeterMatrix.F₄ W) (k : Fin 2) :
    W →* Multiplicative (ZMod 2) :=
  cs.lift ⟨classValue k, classValue_liftable k⟩

theorem classCharacter_simple {W : Type} [Group W]
    (cs : CoxeterSystem CoxeterMatrix.F₄ W) (k : Fin 2) (i : Fin 4) :
    classCharacter cs k (cs.simple i) = classValue k i :=
  cs.lift_apply_simple (classValue_liftable k) i

theorem classCharacter_conj {W : Type} [Group W]
    (cs : CoxeterSystem CoxeterMatrix.F₄ W) (k : Fin 2) (g t : W) :
    classCharacter cs k (g * t * g⁻¹) = classCharacter cs k t := by
  simp [map_mul, map_inv, mul_comm]

theorem classCharacter_eq_of_order_three {W : Type} [Group W]
    (cs : CoxeterSystem CoxeterMatrix.F₄ W) (k : Fin 2) {a b : W}
    (hab : orderOf (a * b) = 3) :
    classCharacter cs k a = classCharacter cs k b := by
  have sq : ∀ z : Multiplicative (ZMod 2), z * z = 1 := by
    intro z
    apply Multiplicative.toAdd.injective
    change Multiplicative.toAdd z + Multiplicative.toAdd z = 0
    calc
      _ = (2 : ZMod 2) * Multiplicative.toAdd z := by ring
      _ = 0 := by rw [show (2 : ZMod 2) = 0 from by decide +kernel, zero_mul]
  have hpow : (classCharacter cs k a * classCharacter cs k b) ^ 3 = 1 := by
    rw [← map_mul, ← map_pow, ← hab, pow_orderOf_eq_one, map_one]
  have hmul : classCharacter cs k a * classCharacter cs k b = 1 := by
    simpa only [pow_succ _ 2, pow_two, sq, one_mul] using hpow
  calc
    _ = classCharacter cs k a * (classCharacter cs k b * classCharacter cs k b) := by
      rw [sq, mul_one]
    _ = classCharacter cs k b := by rw [← mul_assoc, hmul, one_mul]

end CFSG.StandardType.F4Model

end

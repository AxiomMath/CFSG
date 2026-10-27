module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

theorem par4_comm_cases : ∀ v : Fin 6 → ZMod 2,
    par4 v * par4 ![1, 0, 0, 0, 0, 0] = par4 ![1, 0, 0, 0, 0, 0] * par4 v →
    par4 v * par4 ![0, 0, 0, 1, 0, 0] = par4 ![0, 0, 0, 1, 0, 0] * par4 v →
    par4 v * par4 ![0, 0, 0, 0, 0, 1] = par4 ![0, 0, 0, 0, 0, 1] * par4 v →
    v = 0 ∨ v = ![0, 0, 1, 0, 0, 0] := by
  decide

@[expose] def zU : ↥(uniSL 4) := par4SL ![0, 0, 1, 0, 0, 0]

theorem zU_ne_one : zU ≠ 1 := by
  intro h
  have := congrFun (congrFun (congrArg (fun A : ↥(uniSL 4) =>
    ((A : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))) h) 0) 3
  simp [zU, par4SL, par4] at this

theorem par4_corner_sq :
    par4 ![0, 0, 1, 0, 0, 0] * par4 ![0, 0, 1, 0, 0, 0] = 1 := by
  decide

theorem zU_sq : zU ^ 2 = 1 := by
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [pow_two, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  exact congrFun (congrFun par4_corner_sq i) j

theorem orderOf_zU : orderOf zU = 2 :=
  orderOf_eq_prime zU_sq zU_ne_one

theorem center_uniSL_le : Subgroup.center ↥(uniSL 4) ≤ Subgroup.zpowers zU := by
  intro x hx
  obtain ⟨v, rfl⟩ := par4SL_bijective.2 x
  have hc : ∀ w, par4 v * par4 w = par4 w * par4 v := fun w => by
    have h := (Subgroup.mem_center_iff.mp hx (par4SL w)).symm
    exact congrArg (fun A : ↥(uniSL 4) =>
      ((A : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))) h
  rcases par4_comm_cases v (hc _) (hc _) (hc _) with rfl | rfl
  · convert Subgroup.one_mem _
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · exact Subgroup.mem_zpowers zU

theorem card_center_uniSL_le : Nat.card (Subgroup.center ↥(uniSL 4)) ≤ 2 := by
  calc Nat.card (Subgroup.center ↥(uniSL 4)) ≤ Nat.card (Subgroup.zpowers zU) :=
        Subgroup.card_le_of_le center_uniSL_le
    _ = 2 := by rw [Nat.card_zpowers, orderOf_zU]

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

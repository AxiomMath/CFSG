module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H35

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

variable {m k : ℕ}

@[expose] def Q2 : Subgroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) := stabStd 2 3

@[expose] def X2 : Subgroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) where
  carrier := {g | PresStd (m := 2) (k := 3) (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) ∧
    topB (m := 2) (k := 3) (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1}
  one_mem' := ⟨presStd_one, topB_one⟩
  mul_mem' := fun {a b} ha hb => ⟨presStd_mul ha.1 hb.1, by
    rw [Matrix.SpecialLinearGroup.coe_mul, topB_mul hb.1, ha.2, hb.2, Matrix.one_mul]⟩
  inv_mem' := fun hx => inv_mem_of_mul_closed
    (S := {g : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) |
      PresStd (m := 2) (k := 3) (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) ∧
        topB (m := 2) (k := 3) (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1})
    ⟨presStd_one, topB_one⟩ (fun a b ha hb => ⟨presStd_mul ha.1 hb.1, by
      rw [Matrix.SpecialLinearGroup.coe_mul, topB_mul hb.1, ha.2, hb.2, Matrix.one_mul]⟩) hx

@[expose] def X3 : Subgroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) where
  carrier := {g | PresStd (m := 3) (k := 2) (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) ∧
    botB (m := 3) (k := 2) (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1}
  one_mem' := ⟨presStd_one, botB_one⟩
  mul_mem' := fun {a b} ha hb => ⟨presStd_mul ha.1 hb.1, by
    rw [Matrix.SpecialLinearGroup.coe_mul, botB_mul ha.1, ha.2, hb.2, Matrix.one_mul]⟩
  inv_mem' := fun hx => inv_mem_of_mul_closed
    (S := {g : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) |
      PresStd (m := 3) (k := 2) (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) ∧
        botB (m := 3) (k := 2) (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1})
    ⟨presStd_one, botB_one⟩ (fun a b ha hb => ⟨presStd_mul ha.1 hb.1, by
      rw [Matrix.SpecialLinearGroup.coe_mul, botB_mul ha.1, ha.2, hb.2, Matrix.one_mul]⟩) hx

@[expose] def X14 : Subgroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :=
  (stabStd 1 4 : Subgroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) ⊓ stabStd 4 1

variable {g : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)}

theorem eq_utSL_of_blocks {h : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)}
    (hp : PresStd (h : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)))
    (ht : topB (h : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) = 1)
    (hb : botB (h : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) = 1) :
    h = utSL fun a d => (h : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2))
      (Fin.castAdd k a) (Fin.natAdd m d) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rcases fin_add_cases i with ⟨a, rfl⟩ | ⟨b, rfl⟩ <;>
    rcases fin_add_cases j with ⟨c, rfl⟩ | ⟨d, rfl⟩
  · exact (congrFun (congrFun ht a) c).trans (utSL_cc _ a c).symm
  · exact (utSL_cn (fun a d => (h : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2))
      (Fin.castAdd k a) (Fin.natAdd m d)) a d).symm
  · exact (hp b c).trans (utSL_nc _ b c).symm
  · exact (congrFun (congrFun hb b) d).trans (utSL_nn _ b d).symm

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

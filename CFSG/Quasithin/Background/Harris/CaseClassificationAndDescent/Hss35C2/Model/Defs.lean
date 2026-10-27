module

public import CFSG.Quasithin.Background.A1cKlein
public import CFSG.Quasithin.EmptyFaithful.SzF53MDefs

public section

namespace CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.Hss35C2.Model

open CFSG.Quasithin CFSG.Quasithin.F53Mod Equiv

abbrev Vec : Type := Fin 5 → ZMod 2

@[expose] def one5 : Vec := fun _ => 1

@[expose] def Zax : AddSubgroup Vec where
  carrier := {z | z = 0 ∨ z = one5}
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro x y (rfl | rfl) (rfl | rfl)
    · exact Or.inl (add_zero 0)
    · exact Or.inr (zero_add _)
    · exact Or.inr (add_zero _)
    · refine Or.inl (funext fun i => ?_)
      show (1 : ZMod 2) + 1 = 0
      decide
  neg_mem' := by
    rintro x (rfl | rfl)
    · exact Or.inl neg_zero
    · refine Or.inr (funext fun i => ?_)
      show -(1 : ZMod 2) = 1
      decide

theorem mem_Zax {z : Vec} : z ∈ Zax ↔ z = 0 ∨ z = one5 := Iff.rfl

end CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.Hss35C2.Model

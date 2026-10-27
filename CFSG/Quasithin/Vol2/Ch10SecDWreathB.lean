module

public import CFSG.Quasithin.Vol2.Ch10SecDWreathA

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Quasithin

@[expose] def wrBaseHom : (Multiplicative (ZMod 2) → Equiv.Perm (Fin 5)) →* SymFiveWrTwo where
  toFun f := ⟨f, 1⟩
  map_one' := rfl
  map_mul' f g := by
    refine RegularWreathProduct.ext ?_ ?_
    · funext x
      show f x * g x = f x * g ((1 : Multiplicative (ZMod 2))⁻¹ * x)
      have e : (1 : Multiplicative (ZMod 2))⁻¹ * x = x := by revert x; decide
      rw [e]
    · exact (one_mul 1).symm

theorem wrBaseHom_left (f : Multiplicative (ZMod 2) → Equiv.Perm (Fin 5)) :
    (wrBaseHom f).left = f := rfl

theorem wrBaseHom_right (f : Multiplicative (ZMod 2) → Equiv.Perm (Fin 5)) :
    (wrBaseHom f).right = 1 := rfl

theorem wrBaseHom_injective : Function.Injective wrBaseHom := fun _ _ h =>
  congrArg RegularWreathProduct.left h

theorem wrIota_eq (q : Multiplicative (ZMod 2)) (σ : Equiv.Perm (Fin 5)) :
    wrIota q σ = wrBaseHom (Pi.mulSingle q σ) := rfl

theorem eq_wrBaseHom {w : SymFiveWrTwo} (hw : w.right = 1) : w = wrBaseHom w.left :=
  RegularWreathProduct.ext rfl hw

abbrev zs : Multiplicative (ZMod 2) := Multiplicative.ofAdd (1 : ZMod 2)

theorem eq_mul_wrIota {w : SymFiveWrTwo} (hw : w.right = 1) :
    w = wrIota 1 (w.left 1) * wrIota zs (w.left zs) := by
  rw [wrIota_eq, wrIota_eq, ← map_mul]
  conv_lhs => rw [eq_wrBaseHom hw]
  congr 1
  funext x
  rcases zmod2_cases x with rfl | rfl
  · simp [show (zs : Multiplicative (ZMod 2)) ≠ 1 by decide]
  · simp

theorem odd_orderOf_wrIota {q : Multiplicative (ZMod 2)} {c : Equiv.Perm (Fin 5)}
    (hc : c.IsThreeCycle) : Odd (orderOf (wrIota q c)) := by
  rw [orderOf_injective _ (wrIota_injective q), hc.orderOf]
  decide

theorem map_alternating_le (q : Multiplicative (ZMod 2)) :
    (alternatingGroup (Fin 5)).map (wrIota q) ≤ oTwoUpper (⊤ : Subgroup SymFiveWrTwo) := by
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating, MonoidHom.map_closure,
    Subgroup.closure_le]
  rintro _ ⟨c, hc, rfl⟩
  exact mem_oTwoUpper_of_odd (Subgroup.mem_top _) (odd_orderOf_wrIota hc)

theorem oTwoUpper_top_eq : oTwoUpper (⊤ : Subgroup SymFiveWrTwo) = wrBase := by
  apply le_antisymm
  · rw [oTwoUpper, Subgroup.closure_le]
    rintro x ⟨-, hx⟩
    exact mem_wrBase_of_odd hx
  · intro w hw
    rw [eq_mul_wrIota hw.1]
    exact Subgroup.mul_mem _ (map_alternating_le 1 ⟨_, hw.2 1, rfl⟩)
      (map_alternating_le zs ⟨_, hw.2 zs, rfl⟩)

end CFSG.Quasithin.Vol2.Ch10.SecD

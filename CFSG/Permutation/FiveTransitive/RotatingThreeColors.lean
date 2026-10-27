module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG

namespace FiveTransitive.RotatingThreeColors

open Equiv

theorem three_dvd_card
    {X : Type*} [Finite X] (r : Perm X) (c : X → Fin 3)
    (hc : ∀ x, c (r x) = finRotate 3 (c x)) : 3 ∣ Nat.card X := by
  classical
  let _ := Fintype.ofFinite X
  let F := fun i : Fin 3 => {x : X // c x = i}
  let e (i : Fin 3) : F i ≃ F (finRotate 3 i) :=
    { toFun := fun x => ⟨r x.val, by rw [hc,x.property]⟩
      invFun := fun x => ⟨r.symm x.val, by
        apply (finRotate 3).injective
        rw [←hc,r.apply_symm_apply]
        exact x.property⟩
      left_inv := fun x => Subtype.ext (r.symm_apply_apply x.val)
      right_inv := fun x => Subtype.ext (r.apply_symm_apply x.val) }
  have h0 : Fintype.card (F 0) = Fintype.card (F 1) := Fintype.card_congr (e 0)
  have h1 : Fintype.card (F 1) = Fintype.card (F 2) := Fintype.card_congr (e 1)
  have hcard : Fintype.card X = ∑ i : Fin 3, Fintype.card (F i) := by
    rw [←Fintype.card_sigma]
    exact (Fintype.card_congr (Equiv.sigmaFiberEquiv c)).symm
  rw [Nat.card_eq_fintype_card,hcard]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two,add_zero]
  rw [←h1,←h0]
  exact ⟨Fintype.card (F 0), by omega⟩

end FiveTransitive.RotatingThreeColors

end CFSG

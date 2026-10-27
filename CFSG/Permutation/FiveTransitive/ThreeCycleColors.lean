module

public import CFSG.Permutation.FiveTransitive.RotatingThreeColors
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Tactic.FinCases

public section

namespace CFSG

namespace FiveTransitive.ThreeCycleColors

open Equiv

theorem cycle_embedding
    {C:Type*} (q:Perm C) (h3:q^3=1) (hn:∀x:C,q x≠x) (x:C) :
    ∃e:Fin 3 ↪ C,∀i,q (e i)=e (finRotate 3 i) := by
  have hq3 (z:C):q (q (q z))=z := by
    have h := congrArg (fun f:Perm C => f z) h3
    simpa only [pow_succ, pow_zero,Perm.mul_apply,Perm.one_apply] using h
  have h20:q (q x)≠x := by
    intro h
    apply hn x
    have he := congrArg q h
    rw [hq3] at he
    exact he.symm
  let e:Fin 3 ↪ C := ⟨![x,q x,q (q x)],by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first | rfl | exact (hn x hij).elim | exact (hn x hij.symm).elim
            | exact (h20 hij).elim | exact (h20 hij.symm).elim
            | exact (hn (q x) hij).elim | exact (hn (q x) hij.symm).elim⟩
  refine ⟨e,?_⟩
  intro i
  fin_cases i
  · rfl
  · rfl
  · exact hq3 x

theorem three_dvd_card_of_equivariant
    {Y C:Type*} [Finite Y] [Finite C] (hC:Nat.card C=3)
    (r:Perm Y) (q:Perm C) (h3:q^3=1) (hn:∀x:C,q x≠x)
    (c:Y→C) (hc:∀y,c (r y)=q (c y)) : 3∣Nat.card Y := by
  classical
  have : Nonempty C := Finite.card_pos_iff.mp (by omega)
  obtain ⟨e,he⟩ := cycle_embedding q h3 hn (Classical.arbitrary C)
  let _ := Fintype.ofFinite C
  have hbij:Function.Bijective e := (Fintype.bijective_iff_injective_and_card e).mpr
    ⟨e.injective,by simpa only [←Nat.card_eq_fintype_card,Nat.card_fin] using hC.symm⟩
  let E:Fin 3 ≃ C := Equiv.ofBijective e hbij
  apply RotatingThreeColors.three_dvd_card r (fun y => E.symm (c y))
  intro y
  apply E.injective
  rw [E.apply_symm_apply,hc]
  exact (congrArg q (E.apply_symm_apply (c y))).symm.trans (he (E.symm (c y)))

end FiveTransitive.ThreeCycleColors

end CFSG

module

public import CFSG.Permutation.FiveTransitive.CommutingCyclicFixedCongruence
public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport

public section

namespace CFSG

namespace FiveTransitive.Degree52ThreeCommutingFixed

open MulAction

theorem fixed_card_seven_or_ten
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g q : P) (hg : g ^ 7 = 1) (hq : q ^ 3 = 1) (hqne : q ≠ 1)
    (hgf : Nat.card (Function.fixedPoints g.val) = 3 ∨ Nat.card (Function.fixedPoints g.val) = 10)
    (hlower : Nat.card (Function.fixedPoints g.val) ≤
      Nat.card {x : Function.fixedPoints g.val // q.val x.val = x.val} + 3)
    (hcomm : Commute q g) :
    Nat.card (Function.fixedPoints q.val) = 7 ∨
      Nat.card (Function.fixedPoints q.val) = 10 := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let L := {x : Function.fixedPoints g.val // q.val x.val = x.val}
  change Nat.card (Function.fixedPoints g.val) ≤ Nat.card L + 3 at hlower
  have hLle : Nat.card L ≤ Nat.card (Function.fixedPoints g.val) := by
    exact Nat.card_le_card_of_injective (fun x : L => x.val) Subtype.val_injective
  have hmod5 := CommutingCyclicFixedCongruence.card_modEq P g q hg hcomm
  change Nat.card (Function.fixedPoints q.val) % 7 = Nat.card L % 7 at hmod5
  have hmod3 := CommutingCyclicFixedCongruence.card_modEq P q g hq hcomm.symm
  let E : {x : Function.fixedPoints q.val // g.val x.val = x.val} ≃ L :=
    { toFun := fun x => ⟨⟨x.val.val,x.property⟩,x.val.property⟩
      invFun := fun x => ⟨⟨x.val.val,x.property⟩,x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr E] at hmod3
  change Nat.card (Function.fixedPoints g.val) % 3 = Nat.card L % 3 at hmod3
  have hQ : IsPGroup 3 (Subgroup.zpowers q) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers,pow_one]
    exact orderOf_dvd_of_pow_eq_one hq)
  have hglobal3 := hQ.card_modEq_card_fixedPoints X
  rw [CentralizingSingletonFixed.fixed_zpowers] at hglobal3
  change Nat.card X % 3 = Nat.card (Function.fixedPoints q.val) % 3 at hglobal3
  rw [Nat.card_eq_fintype_card (α := X),hcard] at hglobal3
  have hne : q.val ≠ 1 := fun he => hqne (Subtype.ext he)
  have hM := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5 hnotAlt q.property hne
  rw [hcard] at hM
  have hfix : Nat.card (Function.fixedPoints q.val) = 52 - q.val.support.card := by
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,q.val.sum_cycleType,hcard]
  omega

end FiveTransitive.Degree52ThreeCommutingFixed

end CFSG

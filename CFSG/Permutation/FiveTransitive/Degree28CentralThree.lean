module

public import CFSG.Permutation.FiveTransitive.Degree28ThreeFreeReduction
public import CFSG.Permutation.FiveTransitive.CentralizingFixedPointCongruence
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

namespace FiveTransitive.Degree28CentralThree

open MulAction FixedNormalizerAction

private theorem fixed_card_le_four
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (z : P) (hz : orderOf z = 3) : Nat.card (Function.fixedPoints z.val) ≤ 4 := by
  by_contra hn
  have hfive : 5 ≤ (Function.fixedPoints z.val).ncard := by
    rw [← Nat.card_coe_set_eq]
    omega
  obtain ⟨s,hs,hsc⟩ := Set.exists_subset_card_eq hfive
  have hzmem : z ∈ fixingSubgroup P s := by
    apply (mem_fixingSubgroup_iff P).mpr
    intro x hx
    exact hs hx
  have horder : orderOf (⟨z,hzmem⟩ : fixingSubgroup P s) = 3 := by
    rw [← Subgroup.orderOf_coe,hz]
  exact Degree28ThreeFreeReduction.three_not_dvd_five_fixer_card P hcard h5 hnotAlt s hsc
    (horder ▸ orderOf_dvd_natCard (⟨z,hzmem⟩ : fixingSubgroup P s))

theorem false_of_local_fixed_three
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 2 Q) (z : Normalizer Q)
    (hz : orderOf z = 3) (hcomm : ∀ q : Q, z.val * q.val = q.val * z.val)
    (hlocal : Nat.card (Function.fixedPoints (toPermHom (Normalizer Q)
      (Fixed (X := X) Q) z)) = 3) : False := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := Fixed (X := X) Q
  let rho := toPermHom (Normalizer Q) F
  let E : {x : fixedPoints Q X // z.val.val x.val = x.val} ≃ Function.fixedPoints (rho z) :=
    { toFun := fun x => ⟨⟨x.val.val,by change x.val.val ∈ Fixed (X := X) Q; rw [fixed_eq]; exact x.val.property⟩,Subtype.ext x.property⟩
      invFun := fun x => ⟨⟨x.val.val,by rw [← fixed_eq Q]; exact x.val.property⟩,congrArg Subtype.val x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcong := CentralizingFixedPointCongruence.card_modEq P Q hQ z.val hcomm
  rw [Nat.card_congr E,hlocal] at hcong
  have hle := fixed_card_le_four P hcard h5 hnotAlt z.val
    ((Subgroup.orderOf_coe z).trans hz)
  have hglobal : Nat.card (Function.fixedPoints z.val.val) % 3 = 1 := by
    obtain ⟨u,hu⟩ := Equiv.Perm.cycleType_prime_order (σ := z.val.val) (by
      rw [Subgroup.orderOf_coe z.val,Subgroup.orderOf_coe z,hz]; norm_num)
    have hsum := z.val.val.sum_cycleType
    rw [hu,Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,
      Subgroup.orderOf_coe z.val,Subgroup.orderOf_coe z,hz] at hsum
    have hbound := Finset.card_le_univ z.val.val.support
    rw [hcard] at hbound
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,z.val.val.sum_cycleType,hcard]
    omega
  have hge : 3 ≤ Nat.card (Function.fixedPoints z.val.val) := by
    rw [← hlocal]
    exact Nat.card_le_card_of_injective
      (fun x : Function.fixedPoints (rho z) =>
        (⟨x.val.val,congrArg Subtype.val x.property⟩ : Function.fixedPoints z.val.val))
      (by intro a b h; exact Subtype.ext (Subtype.ext (congrArg (fun x => x.val) h)))
  change Nat.card (Function.fixedPoints z.val.val) % 2 = 3 % 2 at hcong
  omega

end FiveTransitive.Degree28CentralThree

end CFSG

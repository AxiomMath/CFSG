module

public import CFSG.Permutation.FiveTransitive.Degree80SevenFree
public import CFSG.Permutation.FiveTransitive.ThreeGroupOrbitSevenFixed
public import CFSG.Permutation.FiveTransitive.PrimeNormalizerResidueObstruction

public section

namespace CFSG

namespace FiveTransitive.Degree80ThreeEightExcluded
open MulAction FixedNormalizerAction

theorem excluded
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 3 Q)
    [Fintype (Fixed (X := X) Q)]
    (hF : Nat.card (Fixed (X := X) Q) = 8)
    (hAlt : alternatingGroup (Fixed (X := X) Q) ≤ Image (X := X) Q) : False := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let F := Fixed (X := X) Q
  change Nat.card F = 8 at hF
  let N := Normalizer Q
  let rho := toPermHom N F
  have hd : 7 ∣ Nat.card rho.range :=
    (SylowFixedActionCore.odd_prime_dvd_alternating_card F (by decide : Nat.Prime 7)
      (by decide) (by rw [← Nat.card_eq_fintype_card]; omega)).trans
        (Subgroup.card_dvd_of_le hAlt)
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := N) 7
    (hd.trans (Subgroup.card_range_dvd rho))
  have hzP : orderOf z.val = 7 := (Subgroup.orderOf_coe z).trans hz
  have hzpow : z ^ 7 = 1 := hz ▸ pow_orderOf_eq_one z
  have hglobal := Degree80SevenFree.fixed_card_eq_three P hcard h5 hnotAlt z.val hzP
  let a := rho z
  have hapow : a ^ 7 = 1 := by rw [← map_pow,hzpow,map_one]
  have hlocalmod := PrimeNormalizerResidueObstruction.perm_fixed_card_modEq a hapow
  change Nat.card F % 7 = Nat.card (Function.fixedPoints a) % 7 at hlocalmod
  rw [hF] at hlocalmod
  let E : Function.fixedPoints a ≃ {x : F // z.val.val x.val = x.val} :=
    { toFun := fun x => ⟨x.val,congrArg Subtype.val x.property⟩
      invFun := fun x => ⟨x.val,Subtype.ext x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let f : Function.fixedPoints a → Function.fixedPoints z.val.val :=
    fun x => ⟨x.val.val,congrArg Subtype.val x.property⟩
  have hf : Function.Injective f := by
    intro x y h
    have he : x.val.val = y.val.val := congrArg (fun t : Function.fixedPoints z.val.val => t.val) h
    exact Subtype.ext (Subtype.ext he)
  have hlocalle := Nat.card_le_card_of_injective f hf
  rw [hglobal] at hlocalle
  have hlocal : Nat.card (Function.fixedPoints a) = 1 := by omega
  have hsmall (x : X) : Nat.card (orbit Q x) < 81 := by
    have hb := Nat.card_le_card_of_injective (fun y : orbit Q x => y.val) Subtype.val_injective
    rw [Nat.card_eq_fintype_card (α := X),hcard] at hb
    omega
  have hm := ThreeGroupOrbitSevenFixed.fixed_congruence Q hQ hsmall z.val z.property
    (congrArg Subtype.val hzpow)
  rw [← fixed_eq Q] at hm
  change Nat.card (Function.fixedPoints z.val.val) % 3 =
    Nat.card {x : F // z.val.val x.val = x.val} % 3 at hm
  rw [← Nat.card_congr E,hglobal,hlocal] at hm
  norm_num at hm

end FiveTransitive.Degree80ThreeEightExcluded

end CFSG

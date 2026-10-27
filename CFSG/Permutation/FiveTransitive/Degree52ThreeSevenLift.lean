module

public import CFSG.Permutation.FiveTransitive.Degree52ThreeFixed
public import CFSG.Permutation.FiveTransitive.ThreeGroupOrbitSevenFixed
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

namespace FiveTransitive.Degree52ThreeSevenLift

open MulAction SylowFixedActionCore

private theorem local_fixed_cases
    {F : Type*} [Fintype F] [DecidableEq F] (hF : Fintype.card F = 7)
    (g : Equiv.Perm F) (hg : g ^ 7 = 1) :
    Nat.card (Function.fixedPoints g) = 0 ∨ Nat.card (Function.fixedPoints g) = 7 := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  by_cases hgne : g = 1
  · subst g
    right
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints]
    simpa using hF
  have ho : orderOf g = 7 := orderOf_eq_prime hg hgne
  obtain ⟨u,hu⟩ := Equiv.Perm.cycleType_prime_order (σ := g) (by rw [ho]; decide)
  have hsum := g.sum_cycleType
  rw [hu,Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,ho] at hsum
  have hle := Finset.card_le_univ g.support
  rw [hF] at hle
  left
  rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,g.sum_cycleType,hF]
  omega

theorem exists_seven_exterior_fixed_three
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hglobal : ∀ g : P, orderOf g = 7 →
      Nat.card (Function.fixedPoints g.val) = 3 ∨ Nat.card (Function.fixedPoints g.val) = 10)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 3 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    ∃ g : sylowNormalizer X P s S, orderOf g = 7 ∧
      Nat.card (fixedBy X g.val) =
        Nat.card {x : fixedPoints (sylowImage X P s S) X // g.val • x.val = x.val} + 3 := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
  let rho : N →* Equiv.Perm F := toPermHom N F
  have hQ : IsPGroup 3 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hfixeq : (F : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  obtain ⟨hF,hAlt⟩ := Degree52ThreeFixed.three_fixed_card_and_image P hcard h5 hnotAlt s hs S hS
  have hFfin : Fintype.card F = 7 := by rwa [← Nat.card_eq_fintype_card]
  have hdiv : 7 ∣ Nat.card N :=
    ((odd_prime_dvd_alternating_card F (by decide : Nat.Prime 7) (by norm_num)
      (by rw [hFfin])).trans (Subgroup.card_dvd_of_le hAlt)).trans
        (Subgroup.card_range_dvd rho)
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := N) 7 hdiv
  have hzpow : z ^ 7 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hg := hglobal z.val ((Subgroup.orderOf_coe z).trans hz)
  have hl := local_fixed_cases hFfin (rho z) (by rw [← map_pow,hzpow,map_one])
  let E : {x : fixedPoints Q X // z.val.val x.val = x.val} ≃ Function.fixedPoints (rho z) :=
    { toFun := fun x => ⟨⟨x.val.val,by rw [hfixeq]; exact x.val.property⟩,Subtype.ext x.property⟩
      invFun := fun x => ⟨⟨x.val.val,by rw [← hfixeq]; exact x.val.property⟩,congrArg Subtype.val x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hsmall (x : X) : Nat.card (orbit Q x) < 81 := by
    have hh := Nat.card_le_card_of_injective (fun y : orbit Q x => y.val) Subtype.val_injective
    rw [Nat.card_eq_fintype_card (α := X),hcard] at hh
    omega
  have hc := ThreeGroupOrbitSevenFixed.fixed_congruence Q hQ hsmall z.val z.property
    (congrArg Subtype.val hzpow)
  change Nat.card (Function.fixedPoints z.val.val) ≡
    Nat.card {x : fixedPoints Q X // z.val.val x.val = x.val} [MOD 3] at hc
  rw [Nat.card_congr E] at hc
  change Nat.card (Function.fixedPoints z.val.val) % 3 =
    Nat.card (Function.fixedPoints (rho z)) % 3 at hc
  refine ⟨z,hz,?_⟩
  change Nat.card (Function.fixedPoints z.val.val) =
    Nat.card {x : fixedPoints Q X // z.val.val x.val = x.val} + 3
  rw [Nat.card_congr E]
  omega

end FiveTransitive.Degree52ThreeSevenLift

end CFSG

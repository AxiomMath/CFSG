module

public import CFSG.Permutation.FiveTransitive.Degree48ThreeImage
public import CFSG.Permutation.FiveTransitive.ThreeGroupOrbitElevenFixed
public import CFSG.Permutation.FiveTransitive.PrimePowerSmallDegree

public section

namespace CFSG

namespace FiveTransitive.Degree48ThreeElevenLift

open MulAction SylowFixedActionCore

theorem exists_eleven_fixed_four
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 48)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    ∃ z : sylowNormalizer X P s S, orderOf z = 11 ∧
      Nat.card (Function.fixedPoints z.val.val) = 4 := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
  let rho : N →* Equiv.Perm F := toPermHom N F
  have hQ : IsPGroup 3 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hfixeq : (F : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  have hF := (Degree48ThreeEntrance.three_entrance P hcard h5 hnotAlt s hs S hS).1
  have hFfin : Fintype.card F = 12 := by rwa [← Nat.card_eq_fintype_card]
  have hdiv : 11 ∣ Nat.card rho.range := by
    have hI := Degree48ThreeImage.card_eq_95040 P hcard h5 hnotAlt s hs S hS
    change Nat.card rho.range = 95040 at hI
    rw [hI]; norm_num
  let T : Sylow 11 N := Sylow.nonempty.some
  have hex : ∃ z : N, z ∈ (T : Subgroup N) ∧ rho z ≠ 1 := by
    by_contra hn
    push Not at hn
    exact prime_not_dvd_range_card_of_sylow_le_ker T rho (fun z hz => hn z hz) hdiv
  obtain ⟨z,hzT,hzrho⟩ := hex
  obtain ⟨e,he⟩ := IsPGroup.iff_orderOf.mp T.isPGroup' (⟨z,hzT⟩ : T)
  have hzorder : orderOf z.val.val = 11 ^ e := by
    rw [Subgroup.orderOf_coe z.val,Subgroup.orderOf_coe z]
    exact (Subgroup.orderOf_coe (⟨z,hzT⟩ : T)).trans he
  have hzpow : z ^ 11 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact PrimePowerSmallDegree.pow_eq_one (by decide : Nat.Prime 11)
      (by rw [hcard]; norm_num) z.val.val ⟨e,hzorder⟩
  have hzne : z.val.val ≠ 1 := by
    intro hh
    have hz1 : z = 1 := Subtype.ext (Subtype.ext hh)
    exact hzrho (by rw [hz1,map_one])
  have hzglobal : orderOf z.val.val = 11 := orderOf_eq_prime
    (congrArg (fun n : N => n.val.val) hzpow) hzne
  have hzlocal : orderOf (rho z) = 11 := orderOf_eq_prime
    (by rw [← map_pow,hzpow,map_one]) hzrho
  refine ⟨z,?_,?_⟩
  · exact orderOf_eq_prime hzpow (fun hz => hzrho (by rw [hz,map_one]))
  let E : {x : fixedPoints Q X // z.val.val x.val = x.val} ≃ Function.fixedPoints (rho z) :=
    { toFun := fun x => ⟨⟨x.val.val,by rw [hfixeq]; exact x.val.property⟩,Subtype.ext x.property⟩
      invFun := fun x => ⟨⟨x.val.val,by rw [← hfixeq]; exact x.val.property⟩,congrArg Subtype.val x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hsmall (x : X) : Nat.card (orbit Q x) < 81 := by
    have hh := Nat.card_le_card_of_injective (fun y : orbit Q x => y.val) Subtype.val_injective
    rw [Nat.card_eq_fintype_card (α := X),hcard] at hh
    omega
  have hcong := ThreeGroupOrbitElevenFixed.fixed_congruence Q hQ hsmall z.val z.property
    (congrArg Subtype.val hzpow)
  change Nat.card (Function.fixedPoints z.val.val) ≡
    Nat.card {x : fixedPoints Q X // z.val.val x.val = x.val} [MOD 3] at hcong
  rw [Nat.card_congr E] at hcong
  have hglobalfixed : Nat.card (Function.fixedPoints z.val.val) = 48 - z.val.val.support.card := by
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,z.val.val.sum_cycleType,hcard]
  have hlocalfixed : Nat.card (Function.fixedPoints (rho z)) = 12 - (rho z).support.card := by
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,(rho z).sum_cycleType,hFfin]
  change Nat.card (Function.fixedPoints z.val.val) % 3 = Nat.card (Function.fixedPoints (rho z)) % 3 at hcong
  rw [hglobalfixed,hlocalfixed] at hcong
  have hM := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5 hnotAlt z.val.property hzne
  rw [hcard] at hM
  obtain ⟨u,hu⟩ := Equiv.Perm.cycleType_prime_order (σ := z.val.val) (by rw [hzglobal]; decide)
  obtain ⟨v,hv⟩ := Equiv.Perm.cycleType_prime_order (σ := rho z) (by rw [hzlocal]; decide)
  have hsumG := z.val.val.sum_cycleType
  rw [hu,Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,hzglobal] at hsumG
  have hsumF := (rho z).sum_cycleType
  rw [hv,Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,hzlocal] at hsumF
  have hleG := Finset.card_le_univ z.val.val.support
  rw [hcard] at hleG
  have hleF := Finset.card_le_univ (rho z).support
  rw [hFfin] at hleF
  omega

end FiveTransitive.Degree48ThreeElevenLift

end CFSG

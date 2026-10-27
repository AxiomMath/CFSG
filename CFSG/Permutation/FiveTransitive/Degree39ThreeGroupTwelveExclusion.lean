module

public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport
public import CFSG.Permutation.FiveTransitive.ThreeGroupOrbitElevenFixed
public import CFSG.Permutation.FiveTransitive.PrimePowerSmallDegree
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import CFSG.Permutation.FiveTransitive.SylowFixedActionCore

public section

namespace CFSG

namespace FiveTransitive.Degree39ThreeGroupTwelveExclusion

open MulAction FixedNormalizerAction

private theorem false_of_eleven_dvd_fixed_image
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 39)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 3 Q)
    (hfixed : Nat.card (Fixed (X := X) Q) = 12)
    (heleven : 11 ∣ Nat.card (Image (X := X) Q)) : False := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let _ : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  let F := Fixed (X := X) Q
  let N := Normalizer Q
  let _ : Fintype F := Fintype.ofFinite F
  let rho : N →* Equiv.Perm F := toPermHom N F
  have hfixeq : (F : Set X) = fixedPoints Q X := fixed_eq Q
  have hFfin : Fintype.card F = 12 := by rwa [Nat.card_eq_fintype_card] at hfixed
  let T : Sylow 11 N := Sylow.nonempty.some
  have hex : ∃ z : N, z ∈ (T : Subgroup N) ∧ rho z ≠ 1 := by
    by_contra hn
    push Not at hn
    have hker : (T : Subgroup N) ≤ rho.ker := fun z hz => hn z hz
    exact SylowFixedActionCore.prime_not_dvd_range_card_of_sylow_le_ker T rho hker heleven
  obtain ⟨z,hzT,hzrho⟩ := hex
  obtain ⟨e,he⟩ := IsPGroup.iff_orderOf.mp T.isPGroup' (⟨z,hzT⟩ : T)
  have hzorder : orderOf z.val.val = 11 ^ e := by
    rw [Subgroup.orderOf_coe z.val,Subgroup.orderOf_coe z]
    exact (Subgroup.orderOf_coe (⟨z,hzT⟩ : T)).trans he
  have hzpow : z ^ 11 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact PrimePowerSmallDegree.pow_eq_one (by norm_num : Nat.Prime 11)
      (by rw [hcard]; norm_num) z.val.val ⟨e,hzorder⟩
  have hzne : z.val.val ≠ 1 := by
    intro hh
    have hz1 : z = 1 := Subtype.ext (Subtype.ext hh)
    exact hzrho (by rw [hz1,map_one])
  have hzglobal : orderOf z.val.val = 11 := orderOf_eq_prime
    (congrArg (fun n : N => n.val.val) hzpow) hzne
  have hzlocal : orderOf (rho z) = 11 := orderOf_eq_prime
    (by rw [← map_pow,hzpow,map_one]) hzrho
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
  have hglobalfixed : Nat.card (Function.fixedPoints z.val.val) = 39 - z.val.val.support.card := by
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,z.val.val.sum_cycleType,hcard]
  have hlocalfixed : Nat.card (Function.fixedPoints (rho z)) = 12 - (rho z).support.card := by
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,(rho z).sum_cycleType,hFfin]
  change Nat.card (Function.fixedPoints z.val.val) % 3 = Nat.card (Function.fixedPoints (rho z)) % 3 at hcong
  rw [hglobalfixed,hlocalfixed] at hcong
  have hM := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5 hnotAlt z.val.property hzne
  rw [hcard] at hM
  obtain ⟨u,hu⟩ := Equiv.Perm.cycleType_prime_order (σ := z.val.val) (by rw [hzglobal]; norm_num)
  obtain ⟨v,hv⟩ := Equiv.Perm.cycleType_prime_order (σ := rho z) (by rw [hzlocal]; norm_num)
  have hsumG := z.val.val.sum_cycleType
  rw [hu,Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,hzglobal] at hsumG
  have hsumF := (rho z).sum_cycleType
  rw [hv,Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,hzlocal] at hsumF
  have hleG := Finset.card_le_univ z.val.val.support
  rw [hcard] at hleG
  have hleF := Finset.card_le_univ (rho z).support
  rw [hFfin] at hleF
  omega

theorem false_of_five_transitive
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 39)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 3 Q)
    (hfixed : Nat.card (Fixed (X := X) Q) = 12)
    (hN5 : IsMultiplyPretransitive (Normalizer Q) (Fixed (X := X) Q) 5) : False := by
  classical
  let F := Fixed (X := X) Q
  let N := Normalizer Q
  let _ : Fintype F := Fintype.ofFinite F
  have hFfin : Fintype.card F = 12 := by rwa [Nat.card_eq_fintype_card] at hfixed
  have hJ5 := FiveTransitive.isMultiplyPretransitive_range_toPermHom N F 5 hN5
  have hd := FiveTransitive.descFactorial_dvd_card_of_isMultiplyPretransitive
    (Image (X := X) Q) F 5 (by omega) hJ5
  rw [hFfin] at hd
  exact false_of_eleven_dvd_fixed_image P hcard h5 hnotAlt Q hQ hfixed
    ((by norm_num : 11 ∣ (12 : ℕ).descFactorial 5).trans hd)

end FiveTransitive.Degree39ThreeGroupTwelveExclusion

end CFSG

module

public import CFSG.Permutation.FiveTransitive.SylowFixedActionCore
public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import CFSG.Permutation.FiveTransitive.ThreeGroupOrbitElevenFixed
public import CFSG.Permutation.FiveTransitive.PrimePowerSmallDegree

public section

namespace CFSG

namespace FiveTransitive.Degree72ThreeElevenLift

open MulAction SylowFixedActionCore

theorem exists_eleven_fixed_twentyEight
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s)) (hF12 : Nat.card (sylowFixedPoints X P s S) = 12) :
    ∃ z : sylowNormalizer X P s S, orderOf z = 11 ∧
      Nat.card (Function.fixedPoints z.val.val) = 28 := by
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
  have hF := hF12
  have hFfin : Fintype.card F = 12 := by rwa [← Nat.card_eq_fintype_card]
  have hdiv : 11 ∣ Nat.card rho.range := by
    let J := rho.range
    have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
        ∃ g : P, ∀ i, g • a i = b i := by
      intro a b ha hb
      obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
      exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
    have hN5 := sylowNormalizer_five_transitive_on_fixedPoints X P hexp s hs S
    have hJ5 : IsMultiplyPretransitive J F 5 := by
      constructor
      intro a b
      obtain ⟨g,hg⟩ := hN5 a b a.injective b.injective
      exact ⟨⟨rho g,⟨g,rfl⟩⟩,DFunLike.ext _ _ hg⟩
    have hd := FiveTransitive.descFactorial_dvd_card_of_isMultiplyPretransitive
      J F 5 (by rw [hFfin]; decide) hJ5
    apply Nat.dvd_trans (b := (Fintype.card F).descFactorial 5) _ hd
    rw [hFfin]; norm_num [Nat.descFactorial]
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
  have hglobalfixed : Nat.card (Function.fixedPoints z.val.val) = 72 - z.val.val.support.card := by
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

end FiveTransitive.Degree72ThreeElevenLift

end CFSG

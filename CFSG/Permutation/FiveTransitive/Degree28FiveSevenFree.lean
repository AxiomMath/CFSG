module

public import CFSG.Permutation.FiveTransitive.Degree28FixedTupleDivisibility
public import CFSG.Permutation.FiveTransitive.FiveSevenSmallAut
public import CFSG.Permutation.FiveTransitive.PrimePowerSmallDegree
public import CFSG.Permutation.FiveTransitive.CentralizingFixedPointCongruence
public import CFSG.Permutation.FiveTransitive.MinimalOrbitFixedBounds
public import CFSG.Permutation.FiveTransitive.SylowFixedActionPrimeFree
public import CFSG.Permutation.FiveTransitive.SmallDegreeFixedAction
public import CFSG.Permutation.FiveTransitive.NormalizerFixedComplement

public section

namespace CFSG

namespace FiveTransitive.Degree28FiveSevenFree

open MulAction SylowFixedActionCore

private theorem prime_not_dvd_five_fixer_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : (p = 5 ∧ q = 7) ∨ (p = 7 ∧ q = 5)) :
    ¬ p ∣ Nat.card (fixingSubgroup P s) := by
  classical
  intro hpdiv
  let S : Sylow p (fixingSubgroup P s) := Sylow.nonempty.some
  have hS : Nat.card S ≠ 1 := by
    intro he
    have hh := (S : Subgroup (fixingSubgroup P s)).index_mul_card
    rw [he,mul_one] at hh
    exact S.not_dvd_index (hh ▸ hpdiv)
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
  let rho : N →* Equiv.Perm F := toPermHom N F
  have hQcard : Nat.card Q = Nat.card S := Nat.card_congr
    ((S : Subgroup (fixingSubgroup P s)).equivMapOfInjective
      (fixingSubgroup P s).subtype Subtype.val_injective).toEquiv.symm
  have hQ : IsPGroup p Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hQne : Q ≠ ⊥ := by intro he; apply hS; rw [← hQcard,he]; simp
  have hfixeq : (F : Set X) = fixedPoints Q X := by
    ext x
    constructor
    · intro hx t
      exact hx (⟨⟨t.val,Q.le_normalizer t.property⟩,t.property⟩ : sylowInNormalizer X P s S)
    · intro hx t
      exact hx (⟨t.val.val,t.property⟩ : Q)
  have hupper := MinimalOrbitFixedBounds.fixed_card_le_half X P (by omega) h5 hnotAlt Q hQne
  rw [← hfixeq,hcard] at hupper
  have hlower := SylowFixedActionPrimeFree.base_card_le_fixed_degree X P s S
  rw [hs] at hlower
  change 5 ≤ Nat.card F at hlower
  have hmod := SylowFixedActionPrimeFree.fixed_degree_modEq X P s S
  change Nat.card X % p = Nat.card F % p at hmod
  rw [Nat.card_eq_fintype_card,hcard] at hmod
  have hcases : (p = 5 ∧ (Nat.card F = 8 ∨ Nat.card F = 13)) ∨
      (p = 7 ∧ (Nat.card F = 7 ∨ Nat.card F = 14)) := by
    rcases hpq with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> omega
  have hseven : 7 ≤ Nat.card F := by rcases hcases with h | h <;> omega
  have htuple := Degree28FixedTupleDivisibility.card_dvd_desc P hcard h5 hnotAlt Q
    (by rw [← hfixeq]; exact hseven)
  rw [← hfixeq] at htuple
  obtain ⟨a,ha⟩ := IsPGroup.iff_card.mp hQ
  have ha2 : a ≤ 2 := by
    by_contra hn
    have hpdvd : p ^ 3 ∣ Nat.card Q := by rw [ha]; exact pow_dvd_pow p (by omega : 3 ≤ a)
    have hh := hpdvd.trans htuple
    rcases hcases with ⟨rfl,h | h⟩ | ⟨rfl,h | h⟩ <;> rw [h] at hh <;> norm_num at hh
  have hQp2 : Nat.card Q ≤ p ^ 2 := by
    rw [ha]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos ha2
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  have hN5 := sylowNormalizer_five_transitive_on_fixedPoints X P hexp s hs S
  have hAlt : alternatingGroup F ≤ rho.range := by
    apply SmallDegreeFixedAction.alternatingGroup_le_of_card_le_twentySeven_away_mathieu F rho.range
    · rw [← Nat.card_eq_fintype_card]; omega
    · rw [← Nat.card_eq_fintype_card]; omega
    · rw [← Nat.card_eq_fintype_card]; rcases hcases with h | h <;> omega
    · rw [← Nat.card_eq_fintype_card]; omega
    · intro a b ha hb
      obtain ⟨g,hg⟩ := hN5 a b ha hb
      exact ⟨⟨rho g,⟨g,rfl⟩⟩,hg⟩
  have hqimage : q ∣ Nat.card rho.range :=
    (odd_prime_dvd_alternating_card F (Fact.out : q.Prime)
      (by rcases hpq with h | h <;> omega)
      (by rw [← Nat.card_eq_fintype_card]; rcases hpq with h | h <;> omega)).trans
      (Subgroup.card_dvd_of_le hAlt)
  let T : Sylow q N := Sylow.nonempty.some
  have hex : ∃ z : N, z ∈ (T : Subgroup N) ∧ rho z ≠ 1 := by
    by_contra hn
    push Not at hn
    have hker : (T : Subgroup N) ≤ rho.ker := fun z hz => hn z hz
    exact prime_not_dvd_range_card_of_sylow_le_ker T rho hker hqimage
  obtain ⟨z,hzT,hzrho⟩ := hex
  obtain ⟨e,he⟩ := IsPGroup.iff_orderOf.mp T.isPGroup' (⟨z,hzT⟩ : T)
  have hzorder : orderOf z = q ^ e := (Subgroup.orderOf_coe (⟨z,hzT⟩ : T)).trans he
  have hzpermorder : orderOf z.val.val = q ^ e := by
    rw [Subgroup.orderOf_coe z.val,Subgroup.orderOf_coe z,hzorder]
  have hzpow : z ^ q = 1 := by
    by_cases hq7 : q = 7
    · apply Subtype.ext
      apply Subtype.ext
      exact PrimePowerSmallDegree.pow_eq_one (Fact.out : q.Prime)
        (by rw [hcard,hq7]; norm_num) z.val.val ⟨e,hzpermorder⟩
    · have hq5 : q = 5 := by rcases hpq with h | h <;> omega
      let C := NormalizerFixedComplement.Domain (X := X) Q
      let _ : Fintype C := Fintype.ofFinite C
      have hCcard : Fintype.card C = 28 - Nat.card F := by
        rw [← Nat.card_eq_fintype_card,NormalizerFixedComplement.card_domain,
          ← Nat.card_coe_set_eq,← hfixeq,Nat.card_eq_fintype_card (α := X),hcard]
      have hpow (Y : Type) [Fintype Y] [DecidableEq Y] [MulAction N Y]
          (hY : Fintype.card Y < q ^ 2) : toPermHom N Y z ^ q = 1 := by
        have hd := orderOf_map_dvd (toPermHom N Y) z
        rw [hzorder] at hd
        obtain ⟨k,_,hk⟩ := (Nat.dvd_prime_pow (Fact.out : q.Prime)).mp hd
        exact PrimePowerSmallDegree.pow_eq_one (Fact.out : q.Prime) hY _ ⟨k,hk⟩
      have hFpow := hpow F (by
        rw [hq5,← Nat.card_eq_fintype_card]
        change Nat.card F < 25
        omega)
      have hCpow := hpow C (by
        rw [hCcard,hq5]
        change 28 - Nat.card F < 25
        omega)
      rw [← map_pow] at hFpow hCpow
      apply Subtype.ext
      apply Subtype.ext
      ext x
      by_cases hx : x ∈ (F : Set X)
      · exact congrArg (fun g : Equiv.Perm F => (g ⟨x,hx⟩).val) hFpow
      · have hxC : x ∈ (fixedPoints Q X)ᶜ := by rwa [← hfixeq]
        exact congrArg (fun g : Equiv.Perm C => (g ⟨x,hxC⟩).val) hCpow
  have hauto : Q.normalizerMonoidHom z = 1 :=
    FiveSevenSmallAut.eq_one hpq Q hQ hQp2 _ (by rw [← map_pow,hzpow,map_one])
  have hcomm : ∀ t : Q, z.val * t.val = t.val * z.val := by
    intro t
    have hh : z.val * t.val * z.val⁻¹ = t.val := congrArg Subtype.val (DFunLike.congr_fun hauto t)
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using congrArg (fun g : P => g * z.val) hh
  have hzPorder : orderOf z.val = q := orderOf_eq_prime (congrArg Subtype.val hzpow) (by
    intro hh
    have hz1 : z = 1 := Subtype.ext hh
    exact hzrho (by rw [hz1,map_one]))
  have hzpermq : orderOf z.val.val = q := (Subgroup.orderOf_coe z.val).trans hzPorder
  have hrhoq : orderOf (rho z) = q := orderOf_eq_prime (by rw [← map_pow,hzpow,map_one]) hzrho
  let E : {x : fixedPoints Q X // z.val.val x.val = x.val} ≃ Function.fixedPoints (rho z) :=
    { toFun := fun x => ⟨⟨x.val.val,by rw [hfixeq]; exact x.val.property⟩,Subtype.ext x.property⟩
      invFun := fun x => ⟨⟨x.val.val,by rw [← hfixeq]; exact x.val.property⟩,congrArg Subtype.val x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcong := CentralizingFixedPointCongruence.card_modEq P Q hQ z.val hcomm
  rw [Nat.card_congr E] at hcong
  have hglobalfixed : Nat.card (Function.fixedPoints z.val.val) = 28 - z.val.val.support.card := by
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,z.val.val.sum_cycleType,hcard]
  have hlocalfixed : Nat.card (Function.fixedPoints (rho z)) = Fintype.card F - (rho z).support.card := by
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,(rho z).sum_cycleType]
  change Nat.card (Function.fixedPoints z.val.val) % p = Nat.card (Function.fixedPoints (rho z)) % p at hcong
  rw [hglobalfixed,hlocalfixed] at hcong
  have hzne : z.val.val ≠ 1 := by
    intro hh
    have hz1 : z = 1 := Subtype.ext (Subtype.ext hh)
    exact hzrho (by rw [hz1,map_one])
  have hM := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5 hnotAlt z.val.property hzne
  rw [hcard] at hM
  obtain ⟨u,hu⟩ := Equiv.Perm.cycleType_prime_order (σ := z.val.val) (by rw [hzpermq]; exact (Fact.out : q.Prime))
  obtain ⟨v,hv⟩ := Equiv.Perm.cycleType_prime_order (σ := rho z) (by rw [hrhoq]; exact (Fact.out : q.Prime))
  have hsumG := z.val.val.sum_cycleType
  rw [hu,Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,hzpermq] at hsumG
  have hsumF := (rho z).sum_cycleType
  rw [hv,Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,hrhoq] at hsumF
  have hleG := Finset.card_le_univ z.val.val.support
  rw [hcard] at hleG
  have hleF := Finset.card_le_univ (rho z).support
  rw [Nat.card_eq_fintype_card] at hcases
  rcases hpq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> omega

theorem five_and_seven_not_dvd_five_fixer_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    (¬ 5 ∣ Nat.card (fixingSubgroup P s)) ∧ (¬ 7 ∣ Nat.card (fixingSubgroup P s)) := by
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let _ : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact ⟨prime_not_dvd_five_fixer_card P hcard h5 hnotAlt s hs (Or.inl ⟨rfl,rfl⟩),
    prime_not_dvd_five_fixer_card P hcard h5 hnotAlt s hs (Or.inr ⟨rfl,rfl⟩)⟩

end FiveTransitive.Degree28FiveSevenFree

end CFSG

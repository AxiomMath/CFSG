module

public import CFSG.Permutation.FiveTransitive.Degree59SevenBound
public import CFSG.Permutation.FiveTransitive.CentralizingFixedPointCongruence
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import CFSG.Permutation.FiveTransitive.SylowFixedActionCore
public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport

public section

namespace CFSG

namespace FiveTransitive.Degree59SevenTwentyFour

open MulAction Subgroup SylowFixedActionCore

theorem excluded
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 59)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 7 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    Nat.card (sylowFixedPoints X P s S) ≠ 24 := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let _ : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite _
  intro hF
  change Nat.card F = 24 at hF
  have hFfin : Fintype.card F = 24 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hQ : IsPGroup 7 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hQcard : Nat.card Q = Nat.card S := Nat.card_congr
    ((S : Subgroup (fixingSubgroup P s)).equivMapOfInjective
      (fixingSubgroup P s).subtype Subtype.val_injective).toEquiv.symm
  have hfixeq : (F : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  have hQfixed : Nat.card (fixedPoints Q X) = 24 := by rw [← hfixeq]; exact hF
  have hQbound := Degree59SevenBound.card_le_seven_of_fixed_twenty_four P hcard h5 hnotAlt Q hQ hQfixed
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have he1 : e ≤ 1 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right (by norm_num : 0 < 7) (by omega : 2 ≤ e)
    rw [← he] at hh
    change 49 ≤ Nat.card Q at hh
    omega
  have he0 : e ≠ 0 := by intro he0; apply hS; rw [← hQcard,he,he0,pow_zero]
  have hQseven : Nat.card Q = 7 := by rw [he,show e = 1 by omega,pow_one]
  let _ : IsCyclic Q := isCyclic_of_prime_card hQseven
  have hAut : Nat.card (MulAut Q) = 6 := by
    rw [IsCyclic.card_mulAut Q,hQseven,Nat.totient_prime (by norm_num : Nat.Prime 7)]
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  have hN5 := sylowNormalizer_five_transitive_on_fixedPoints X P hexp s hs S
  have hNmt : IsMultiplyPretransitive N F 5 := by
    constructor
    intro a b
    obtain ⟨g,hg⟩ := hN5 a b a.injective b.injective
    exact ⟨g,DFunLike.ext _ _ hg⟩
  obtain ⟨t,_,ht⟩ := Set.exists_subset_card_eq
    (show 5 ≤ (Set.univ : Set F).ncard by simp [Set.ncard_univ,hFfin])
  have hi := IsMultiplyPretransitive.index_of_fixingSubgroup_eq (G := N) t (by rwa [ht])
  rw [hF,ht] at hi
  norm_num [Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial] at hi
  have h11 : 11 ∣ Nat.card N := (show 11 ∣ (fixingSubgroup N t).index by rw [hi]; norm_num).trans
    (fixingSubgroup N t).index_dvd_card
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := N) 11 h11
  let a : MulAut Q := Q.normalizerMonoidHom z
  have ha11 : orderOf a ∣ 11 := hz ▸ orderOf_map_dvd Q.normalizerMonoidHom z
  have ha6 := orderOf_dvd_natCard a
  rw [hAut] at ha6
  have ha1 : orderOf a = 1 := by
    apply Nat.dvd_one.mp
    have hh := Nat.dvd_gcd ha11 ha6
    norm_num at hh ⊢
    exact hh
  have haut : Q.normalizerMonoidHom z = 1 := orderOf_eq_one_iff.mp ha1
  have hcomm : ∀ q : Q, z.val * q.val = q.val * z.val := by
    intro q
    have hh : z.val * q.val * z.val⁻¹ = q.val :=
      congrArg Subtype.val (DFunLike.congr_fun haut q)
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using congrArg (fun b : P => b * z.val) hh
  have hm7 := CentralizingFixedPointCongruence.card_modEq P Q hQ z.val hcomm
  rw [← hfixeq] at hm7
  let rho : N →* Equiv.Perm F := toPermHom N F
  let e : Function.fixedPoints (rho z) ≃ {x : F // z.val.val x.val = x.val} :=
    { toFun := fun x => ⟨x.val,congrArg Subtype.val x.property⟩
      invFun := fun x => ⟨x.val,Subtype.ext x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e] at hm7
  change Nat.card (Function.fixedPoints z.val.val) % 7 =
    Nat.card (Function.fixedPoints (rho z)) % 7 at hm7
  have hz11 : z ^ 11 = 1 := hz ▸ pow_orderOf_eq_one z
  have hzperm : orderOf z.val.val = 11 := (Subgroup.orderOf_coe z.val).trans
    ((Subgroup.orderOf_coe z).trans hz)
  have hne : z.val.val ≠ 1 := by intro he; rw [he,orderOf_one] at hzperm; omega
  have hmin := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5
    hnotAlt z.val.property hne
  rw [hcard] at hmin
  have hglobal : Nat.card (Function.fixedPoints z.val.val) ≤ 29 := by
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,z.val.val.sum_cycleType,hcard]
    omega
  have hlocal : Nat.card (Function.fixedPoints (rho z)) ≤ 24 := by
    have hh := Nat.card_le_card_of_injective
      (fun x : Function.fixedPoints (rho z) => x.val) Subtype.val_injective
    rwa [hF] at hh
  let b : Function.End X := z.val.val.toFun
  have hb : b ^ 11 = 1 := by
    funext x
    change (z ^ 11).val.val x = x
    rw [hz11]
    rfl
  have hmg := Equiv.Perm.card_fixedPoints_modEq (f := b) (p := 11) (n := 1)
    (by simpa only [pow_one] using hb)
  change Fintype.card X % 11 = Fintype.card (Function.fixedPoints z.val.val) % 11 at hmg
  rw [hcard,← Nat.card_eq_fintype_card] at hmg
  let c : Function.End F := (rho z).toFun
  have hc : c ^ 11 = 1 := by
    funext x
    change ((rho z) ^ 11) x = x
    rw [← map_pow,hz11,map_one]
    rfl
  have hml := Equiv.Perm.card_fixedPoints_modEq (f := c) (p := 11) (n := 1)
    (by simpa only [pow_one] using hc)
  change Fintype.card F % 11 = Fintype.card (Function.fixedPoints (rho z)) % 11 at hml
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hF] at hml
  omega

end FiveTransitive.Degree59SevenTwentyFour

end CFSG

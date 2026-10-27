module

public import CFSG.Permutation.FiveTransitive.Degree52SevenBound
public import CFSG.Permutation.FiveTransitive.Degree52SevenTwentyFourCentralizer
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import CFSG.Permutation.FiveTransitive.SylowFixedActionCore

public section

namespace CFSG

namespace FiveTransitive.Degree52SevenFixedTwentyFour

open MulAction Subgroup SylowFixedActionCore

theorem excluded
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 7 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    Nat.card (sylowFixedPoints X P s S) ≠ 24 := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let _ : Fact (Nat.Prime 23) := ⟨by norm_num⟩
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
  have hQbound := Degree52SevenBound.card_le_seven_of_fixed_twenty_four P hcard h5 hnotAlt Q hQ hQfixed
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
  have h23 : 23 ∣ Nat.card N := (show 23 ∣ (fixingSubgroup N t).index by rw [hi]; norm_num).trans
    (fixingSubgroup N t).index_dvd_card
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := N) 23 h23
  let a : MulAut Q := Q.normalizerMonoidHom z
  have ha23 : orderOf a ∣ 23 := hz ▸ orderOf_map_dvd Q.normalizerMonoidHom z
  have ha6 := orderOf_dvd_natCard a
  rw [hAut] at ha6
  have ha1 : orderOf a = 1 := by
    apply Nat.dvd_one.mp
    have hh := Nat.dvd_gcd ha23 ha6
    norm_num at hh ⊢
    exact hh
  have haut : Q.normalizerMonoidHom z = 1 := orderOf_eq_one_iff.mp ha1
  obtain ⟨u,hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Q)
  have huP : orderOf u.val = 7 := (Subgroup.orderOf_coe u).trans (hu.trans hQseven)
  have hsub : fixedPoints Q X ⊆ Function.fixedPoints u.val.val := fun _ hx => hx u
  have hfixed := Set.ncard_le_ncard hsub
  rw [← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,hQfixed] at hfixed
  have hcomm : z.val * u.val = u.val * z.val := by
    have hh : z.val * u.val * z.val⁻¹ = u.val :=
      congrArg Subtype.val (DFunLike.congr_fun haut u)
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using congrArg (fun b : P => b * z.val) hh
  let v : Subgroup.centralizer ({u.val} : Set P) :=
    ⟨z.val,Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
  have hv : orderOf v = 23 := (Subgroup.orderOf_coe v).symm.trans
    ((Subgroup.orderOf_coe z).trans hz)
  exact Degree52SevenTwentyFourCentralizer.twenty_three_not_dvd P hcard h5 hnotAlt
    u.val huP hfixed (hv ▸ orderOf_dvd_natCard v)

end FiveTransitive.Degree52SevenFixedTwentyFour

end CFSG

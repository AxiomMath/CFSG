module

public import CFSG.Permutation.FiveTransitive.FullFixerSharpFive
public import CFSG.Permutation.FiveTransitive.SmallGroupAutomorphismPrimeFree
public import CFSG.Permutation.FiveTransitive.Degree31FiveCentralizerImage
public import CFSG.Permutation.FiveTransitive.FourFixerClosure

public section

namespace CFSG

namespace FiveTransitive.Degree36SmallTwoFixerData

open MulAction FixedNormalizerAction

theorem is_two_group
    (H : Type*) [Group H] (hH : Nat.card H = 2 ∨ Nat.card H = 4) : IsPGroup 2 H := by
  rcases hH with hH | hH
  · exact IsPGroup.of_card (n := 1) hH
  · exact IsPGroup.of_card (n := 2) hH

theorem fixed_card_cases
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5)
    (s : Set X) (hs : s.ncard = 5)
    (hH : Nat.card (fixingSubgroup P s) = 2 ∨ Nat.card (fixingSubgroup P s) = 4) :
    Nat.card (Fixed (X := X) (fixingSubgroup P s)) = 6 ∨
      Nat.card (Fixed (X := X) (fixingSubgroup P s)) = 12 := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hc := FullFixerSharpFive.fixed_degree_cases h5 s hs
  have hm := (is_two_group (fixingSubgroup P s) hH).card_modEq_card_fixedPoints X
  change Nat.card X % 2 = Nat.card (fixedPoints (fixingSubgroup P s) X) % 2 at hm
  rw [Nat.card_eq_fintype_card,hcard,← fixed_eq] at hm
  change Nat.card (Fixed (X := X) (fixingSubgroup P s)) = 5 ∨
    Nat.card (Fixed (X := X) (fixingSubgroup P s)) = 6 ∨
    Nat.card (Fixed (X := X) (fixingSubgroup P s)) = 7 ∨
    Nat.card (Fixed (X := X) (fixingSubgroup P s)) = 12 at hc
  omega

theorem nine_dvd_centralizer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5)
    (s : Set X) (hs : s.ncard = 5)
    (hH : Nat.card (fixingSubgroup P s) = 2 ∨ Nat.card (fixingSubgroup P s) = 4) :
    9 ∣ Nat.card (Subgroup.centralizer ((fixingSubgroup P s : Subgroup P) : Set P)) := by
  classical
  let H := fixingSubgroup P s
  let F := Fixed (X := X) H
  let J := Image (X := X) H
  let _ : Fintype F := Fintype.ofFinite F
  have hAut : Nat.card (MulAut H) ∣ 24 := by
    have hd := SmallGroupAutomorphismPrimeFree.card_dvd_factorial H
    change Nat.card H = 2 ∨ Nat.card H = 4 at hH
    apply hd.trans
    rcases hH with h | h <;> rw [h] <;> norm_num [Nat.factorial]
  obtain ⟨hJ5,_,hsharp⟩ := FullFixerSharpFive.sharp_image h5 s hs
  rcases fixed_card_cases P hcard h5 s hs hH with hF | hF
  · have htop : J = ⊤ := by
      apply Equiv.Perm.eq_top_of_isMultiplyPretransitive
      change IsMultiplyPretransitive J F (Nat.card F - 1)
      change Nat.card F = 6 at hF
      rw [hF]
      exact hJ5
    exact Degree31FiveCentralizerImage.nine_dvd_centralizer H hF htop (fun h => by
      have hb := h.trans hAut
      norm_num at hb)
  · let N := Normalizer H
    let C := Subgroup.centralizer (H : Set P)
    let rho := toPermHom N F
    have h27J : 27 ∣ Nat.card J := by
      change Nat.card J = (Nat.card F).descFactorial 5 at hsharp
      change Nat.card F = 12 at hF
      rw [hsharp,hF]
      norm_num [Nat.descFactorial]
    have h27N : 27 ∣ Nat.card N := h27J.trans (Subgroup.card_range_dvd rho)
    have hRange : Nat.card H.normalizerMonoidHom.range ∣ 24 :=
      (Subgroup.card_subgroup_dvd_card H.normalizerMonoidHom.range).trans hAut
    have hker : Nat.card H.normalizerMonoidHom.ker = Nat.card C := by
      rw [H.normalizerMonoidHom_ker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (Subgroup.centralizer_le_normalizer (H : Set P))).toEquiv
    have hn := H.normalizerMonoidHom.ker.index_mul_card
    rw [Subgroup.index_ker,hker] at hn
    have hd : Nat.card N ∣ 24 * Nat.card C := by
      rw [← hn]
      exact Nat.mul_dvd_mul hRange (dvd_refl _)
    have h27 : 27 ∣ 24 * Nat.card C := h27N.trans hd
    change 9 ∣ Nat.card C
    omega

theorem order_three_fixed_cases
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5)
    (s : Set X) (hs : s.ncard = 5)
    (hH : Nat.card (fixingSubgroup P s) = 2 ∨ Nat.card (fixingSubgroup P s) = 4)
    (z : P) (hz : orderOf z = 3) :
    Nat.card (Function.fixedPoints z.val) = 0 ∨ Nat.card (Function.fixedPoints z.val) = 3 := by
  classical
  have hlt : Nat.card (Function.fixedPoints z.val) < 5 := by
    by_contra hn
    have hn' : 5 ≤ (Function.fixedPoints z.val).ncard := by rw [← Nat.card_coe_set_eq]; omega
    obtain ⟨t,htsub,ht⟩ := Set.exists_subset_card_eq hn'
    let u : fixingSubgroup P t := ⟨z,(mem_fixingSubgroup_iff P).mpr (fun x hx => htsub hx)⟩
    have hu : orderOf u = 3 := (Subgroup.orderOf_coe u).symm.trans hz
    have hd : 3 ∣ Nat.card (fixingSubgroup P t) := hu ▸ orderOf_dvd_natCard u
    rw [← (FourFixerClosure.card_data h5 s t hs ht).1] at hd
    rcases hH with hH | hH <;> rw [hH] at hd <;> norm_num at hd
  have hzv : orderOf z.val = 3 := (Subgroup.orderOf_coe z).trans hz
  obtain ⟨k,hk⟩ := Equiv.Perm.cycleType_prime_order (σ := z.val) (by rw [hzv]; norm_num)
  have hsum := z.val.sum_cycleType
  rw [hk,Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,hzv] at hsum
  have hle : z.val.support.card ≤ 36 := hcard ▸ Finset.card_le_univ z.val.support
  rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,z.val.sum_cycleType,hcard] at hlt ⊢
  omega

end FiveTransitive.Degree36SmallTwoFixerData

end CFSG

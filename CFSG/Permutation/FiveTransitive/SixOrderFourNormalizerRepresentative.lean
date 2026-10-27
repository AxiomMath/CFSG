module

public import CFSG.Permutation.FiveTransitive.FourCycleFixer
public import CFSG.Permutation.FiveTransitive.NormalizerInvariantSylow
public import CFSG.Permutation.FiveTransitive.BaseSylowConjugacy
public import CFSG.Permutation.FiveTransitive.ConjugateFixedNormalizer
public import CFSG.Permutation.FiveTransitive.FixedSetNormalizerHom
public import CFSG.Permutation.FiveTransitive.NormalizerInvolutionFixedTwo
public import CFSG.Permutation.FiveTransitive.EvenSixOrderFourFixed
public import CFSG.Permutation.FiveTransitive.SemiregularSylowFixedSet

public section

namespace CFSG

namespace FiveTransitive.SixOrderFourNormalizerRepresentative

open MulAction FixedSetNormalizerPerm FixedSetNormalizerHom

theorem exists_conjugate
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (h4 : IsMultiplyPretransitive G X 4) (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup G s))
    (hcard : (fixedPoints ((S : Subgroup (fixingSubgroup G s)).map
      (fixingSubgroup G s).subtype) X).ncard = 6)
    (heven : let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
      ∀ (a : G) (ha : a ∈ Subgroup.normalizer (Q : Set G)),
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPerm G X Q a ha).sign = 1)
    (a : G) (ha : orderOf a = 4) :
    let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
    ∃ (a' : G) (ha'N : a' ∈ Subgroup.normalizer (Q : Set G)),
      orderOf a' = 4 ∧ orderOf (fixedPermHom G X Q ⟨a', ha'N⟩) = 4 ∧
      (fixedBy X a').ncard = (fixedBy X a).ncard ∧
      (fixedBy X a' ∩ fixedPoints Q X).ncard = 0 ∧
      (fixedBy X (a' ^ 2) ∩ fixedPoints Q X).ncard = 2 := by
  classical
  let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
  have ha4 : a ^ 4 = 1 := ha ▸ pow_orderOf_eq_one a
  have ha2 : a ^ 2 ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [ha] at hd
    norm_num at hd
  obtain ⟨x, hx⟩ : ∃ x : X, a ^ 2 • x ≠ x := by
    by_contra hn
    push Not at hn
    exact ha2 (FaithfulSMul.eq_of_smul_eq_smul (α := X) (by simpa only [one_smul] using hn))
  obtain ⟨t, ht, hxt, hnormt⟩ := FourCycleFixer.exists_four_set G X a ha4 x hx
  obtain ⟨T, hT⟩ := NormalizerInvariantSylow.exists_of_order_pow 2 G
    (fixingSubgroup G t) a hnormt 2 ha
  obtain ⟨c, hc⟩ := BaseSylowConjugacy.exists_conjugate_sylow_images G X 4 h4 s t hs ht S T
  let R := (T : Subgroup (fixingSubgroup G t)).map (fixingSubgroup G t).subtype
  have hxR : x ∈ fixedPoints R X := by
    rw [mem_fixedPoints]
    intro q
    obtain ⟨r, hr, hqr⟩ := Subgroup.mem_map.mp q.property
    change (q : G) • x = x
    rw [← hqr]
    exact (mem_fixingSubgroup_iff G).mp r.property x hxt
  have hR2 : fixedPerm G X R a hT ^ 2 ≠ 1 := by
    intro h
    apply hx
    have h' := congrArg (fun f : Equiv.Perm (fixedPoints R X) => (f ⟨x, hxR⟩).val) h
    simpa only [fixedPerm_pow_apply_val, Equiv.Perm.one_apply] using h'
  let a' := c⁻¹ * a * c
  have ha'N : a' ∈ Subgroup.normalizer (Q : Set G) :=
    ConjugateFixedNormalizer.normalizer_conj_back G Q R c hc a hT
  let f := fixedPermHom G X Q ⟨a', ha'N⟩
  have ha' : orderOf a' = 4 := by
    have h := orderOf_injective (MulAut.conj c⁻¹).toMonoidHom (MulAut.conj c⁻¹).injective a
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv, ha] using h
  have ha'4 : a' ^ 4 = 1 := ha' ▸ pow_orderOf_eq_one a'
  have hf4 : f ^ 4 = 1 := by
    change fixedPermHom G X Q ⟨a', ha'N⟩ ^ 4 = 1
    rw [← map_pow]
    have heq : (⟨a', ha'N⟩ : Subgroup.normalizer (Q : Set G)) ^ 4 = 1 := Subtype.ext ha'4
    rw [heq, map_one]
  have hf2 : f ^ 2 ≠ 1 := by
    intro h
    apply hR2
    let e := ConjugateFixedNormalizer.fixedEquiv G X Q R c hc
    have he : e.permCongrHom f = fixedPerm G X R a hT :=
      ConjugateFixedNormalizer.permCongr_fixedPerm G X Q R c hc a hT
    rw [← he, ← map_pow, h, map_one]
  have hfOrder : orderOf f = 4 := orderOf_eq_prime_pow (p := 2) (n := 1) hf2 hf4
  let _ := Fintype.ofFinite (fixedPoints Q X)
  let _ : DecidableEq (fixedPoints Q X) := Classical.decEq _
  have hsize : Fintype.card (fixedPoints Q X) = 6 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hcard
  obtain ⟨hzero, htwo⟩ := EvenSixOrderFourFixed.fixed_card_zero_and_square_two (fixedPoints Q X)
    hsize f (heven a' ha'N) hf4 hf2
  have hnorm2 := (Subgroup.normalizer (Q : Set G)).pow_mem ha'N 2
  have hf2eq : f ^ 2 = fixedPerm G X Q (a' ^ 2) hnorm2 := by
    change fixedPermHom G X Q ⟨a', ha'N⟩ ^ 2 = fixedPermHom G X Q ⟨a' ^ 2, hnorm2⟩
    rw [← map_pow]
    rfl
  refine ⟨a', ha'N, ha', hfOrder, ?_, ?_, ?_⟩
  · rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    simpa only [inv_inv] using
      (Nat.card_congr (SemiregularSylowFixedSet.fixedByConjugateEquiv G X a c⁻¹)).symm
  · rw [← Nat.card_coe_set_eq]
    exact (Nat.card_congr (NormalizerInvolutionFixedTwo.fixedIntersectionEquiv G X Q a' ha'N)).symm.trans hzero
  · rw [hf2eq] at htwo
    rw [← Nat.card_coe_set_eq]
    exact (Nat.card_congr (NormalizerInvolutionFixedTwo.fixedIntersectionEquiv G X Q (a' ^ 2) hnorm2)).symm.trans htwo

end FiveTransitive.SixOrderFourNormalizerRepresentative

end CFSG

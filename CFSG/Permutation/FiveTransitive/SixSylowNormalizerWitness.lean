module

public import CFSG.Permutation.FiveTransitive.TwoTranspositionFixer
public import CFSG.Permutation.FiveTransitive.NormalizerInvariantSylow
public import CFSG.Permutation.FiveTransitive.BaseSylowConjugacy
public import CFSG.Permutation.FiveTransitive.ConjugateFixedNormalizer
public import CFSG.Permutation.FiveTransitive.NormalizerInvolutionFixedTwo

public section

namespace CFSG

namespace FiveTransitive.SixSylowNormalizerWitness

open MulAction FixedSetNormalizerPerm

theorem exists_sylow_conjugate
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h4 : IsMultiplyPretransitive G X 4) (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup G s))
    (hcard : (fixedPoints ((S : Subgroup (fixingSubgroup G s)).map
      (fixingSubgroup G s).subtype) X).ncard = 6)
    (heven : let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
      ∀ (a : G) (ha : a ∈ Subgroup.normalizer (Q : Set G)),
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPerm G X Q a ha).sign = 1)
    (a : G) (ha : orderOf a = 2) (hmoved : 4 ≤ (fixedBy X a)ᶜ.ncard) :
    ∃ (t : Set X) (T : Sylow 2 (fixingSubgroup G t)) (c : G),
      t.ncard = 4 ∧
      let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
      let R := (T : Subgroup (fixingSubgroup G t)).map (fixingSubgroup G t).subtype
      Q.map (MulAut.conj c).toMonoidHom = R ∧
      a ∈ Subgroup.normalizer (R : Set G) ∧
      (fixedBy X a ∩ fixedPoints R X).ncard = 2 := by
  have ha2 : a ^ 2 = 1 := by rw [← ha]; exact pow_orderOf_eq_one _
  obtain ⟨t, ht, hmove, hnorm⟩ := TwoTranspositionFixer.exists_four_set G X a ha2 hmoved
  obtain ⟨T, hT⟩ := NormalizerInvariantSylow.exists_of_order_pow 2 G
    (fixingSubgroup G t) a hnorm 1 (by simpa only [pow_one] using ha)
  obtain ⟨c, hc⟩ := BaseSylowConjugacy.exists_conjugate_sylow_images G X 4 h4 s t hs ht S T
  let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
  let R := (T : Subgroup (fixingSubgroup G t)).map (fixingSubgroup G t).subtype
  have hnormR : a ∈ Subgroup.normalizer (R : Set G) := hT
  obtain ⟨hRcard, hReven⟩ := ConjugateFixedNormalizer.six_even_of_conjugate G X Q R c hc hcard heven
  have hsub : t ⊆ fixedPoints R X := by
    intro x hx
    rw [mem_fixedPoints]
    intro q
    have hq : (q : G) ∈ (T : Subgroup (fixingSubgroup G t)).map (fixingSubgroup G t).subtype :=
      q.property
    obtain ⟨r, hr, hqr⟩ := Subgroup.mem_map.mp hq
    change (q : G) • x = x
    rw [← hqr]
    exact (mem_fixingSubgroup_iff G).mp r.property x hx
  have hnottrivial : ∃ x ∈ fixedPoints R X, a • x ≠ x := by
    obtain ⟨x, hx⟩ := (Set.ncard_pos (Set.toFinite _)).mp (by omega : 0 < t.ncard)
    exact ⟨x, hsub hx, hmove x hx⟩
  exact ⟨t, T, c, ht, hc, hnormR, NormalizerInvolutionFixedTwo.intersection_ncard_eq_two G X R a hnormR
    hRcard ha2 (hReven a hnormR) hnottrivial⟩

end FiveTransitive.SixSylowNormalizerWitness

end CFSG

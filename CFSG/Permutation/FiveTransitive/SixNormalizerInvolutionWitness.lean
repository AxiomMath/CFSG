module

public import CFSG.Permutation.FiveTransitive.TwoTranspositionFixer
public import CFSG.Permutation.FiveTransitive.NormalizerInvariantSylow
public import CFSG.Permutation.FiveTransitive.BaseSylowConjugacy
public import CFSG.Permutation.FiveTransitive.ConjugateFixedNormalizer
public import CFSG.Permutation.FiveTransitive.NormalizerInvolutionFixedTwo

public section

namespace CFSG

namespace FiveTransitive.SixNormalizerInvolutionWitness

open MulAction FixedSetNormalizerPerm

theorem exists_conjugate
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
    ∃ c : G,
      let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
      let R := Q.map (MulAut.conj c).toMonoidHom
      a ∈ Subgroup.normalizer (R : Set G) ∧
      (fixedBy X a ∩ fixedPoints R X).ncard = 2 := by
  have ha2 : a ^ 2 = 1 := by rw [← ha]; exact pow_orderOf_eq_one _
  obtain ⟨t, ht, hmove, hnorm⟩ := TwoTranspositionFixer.exists_four_set G X a ha2 hmoved
  obtain ⟨T, hT⟩ := NormalizerInvariantSylow.exists_of_order_pow 2 G
    (fixingSubgroup G t) a hnorm 1 (by simpa only [pow_one] using ha)
  obtain ⟨c, hc⟩ := BaseSylowConjugacy.exists_conjugate_sylow_images G X 4 h4 s t hs ht S T
  let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
  let R := Q.map (MulAut.conj c).toMonoidHom
  have hnormR : a ∈ Subgroup.normalizer (R : Set G) := by
    change a ∈ Subgroup.normalizer (Q.map (MulAut.conj c).toMonoidHom : Set G)
    rw [hc]
    exact hT
  obtain ⟨hRcard, hReven⟩ := ConjugateFixedNormalizer.six_even_of_conjugate G X Q R c rfl hcard heven
  have hsub : t ⊆ fixedPoints R X := by
    intro x hx
    rw [mem_fixedPoints]
    intro q
    have hq : (q : G) ∈ (T : Subgroup (fixingSubgroup G t)).map (fixingSubgroup G t).subtype :=
      hc ▸ q.property
    obtain ⟨r, hr, hqr⟩ := Subgroup.mem_map.mp hq
    change (q : G) • x = x
    rw [← hqr]
    exact (mem_fixingSubgroup_iff G).mp r.property x hx
  have hnottrivial : ∃ x ∈ fixedPoints R X, a • x ≠ x := by
    obtain ⟨x, hx⟩ := (Set.ncard_pos (Set.toFinite _)).mp (by omega : 0 < t.ncard)
    exact ⟨x, hsub hx, hmove x hx⟩
  exact ⟨c, hnormR, NormalizerInvolutionFixedTwo.intersection_ncard_eq_two G X R a hnormR
    hRcard ha2 (hReven a hnormR) hnottrivial⟩

theorem two_le_fixed
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
    (a : G) (ha : orderOf a = 2) : 2 ≤ (fixedBy X a).ncard := by
  by_cases hmoved : 4 ≤ (fixedBy X a)ᶜ.ncard
  · obtain ⟨c, _, htwo⟩ := exists_conjugate G X h4 s hs S hcard heven a ha hmoved
    rw [← htwo]
    exact Set.ncard_le_ncard Set.inter_subset_left
  · have hsize : 6 ≤ Nat.card X := by
      rw [← hcard]
      simpa only [Set.ncard_univ] using Set.ncard_le_ncard
        (Set.subset_univ (fixedPoints ((S : Subgroup (fixingSubgroup G s)).map
          (fixingSubgroup G s).subtype) X))
    have hcompl := Set.ncard_compl (fixedBy X a)
    have hle : (fixedBy X a).ncard ≤ Nat.card X := by
      simpa only [Set.ncard_univ] using Set.ncard_le_ncard (Set.subset_univ (fixedBy X a))
    omega

end FiveTransitive.SixNormalizerInvolutionWitness

end CFSG

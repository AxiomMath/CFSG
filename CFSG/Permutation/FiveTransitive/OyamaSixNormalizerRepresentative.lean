module

public import CFSG.Permutation.FiveTransitive.SixSylowNormalizerWitness
public import CFSG.Permutation.FiveTransitive.FixedSetNormalizerHom
public import CFSG.Permutation.FiveTransitive.SemiregularSylowFixedSet

public section

namespace CFSG

namespace FiveTransitive.OyamaSixNormalizerRepresentative

open MulAction FixedSetNormalizerPerm FixedSetNormalizerHom

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
    let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
    ∃ (a' : G) (ha'N : a' ∈ Subgroup.normalizer (Q : Set G)),
      a' ^ 2 = 1 ∧ fixedPermHom G X Q ⟨a', ha'N⟩ ≠ 1 ∧
      (fixedBy X a').ncard = (fixedBy X a).ncard ∧
      (fixedBy X a' ∩ fixedPoints Q X).ncard = 2 := by
  let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
  obtain ⟨t, T, c, _, hc, hnorm, htwo⟩ := SixSylowNormalizerWitness.exists_sylow_conjugate
    G X h4 s hs S hcard heven a ha hmoved
  let R := (T : Subgroup (fixingSubgroup G t)).map (fixingSubgroup G t).subtype
  obtain ⟨hRcard, _⟩ := ConjugateFixedNormalizer.six_even_of_conjugate G X Q R c hc hcard heven
  have hneR : fixedPerm G X R a hnorm ≠ 1 := by
    intro h
    have hsub : fixedPoints R X ⊆ fixedBy X a := by
      intro x hx
      exact congrArg (fun f : Equiv.Perm (fixedPoints R X) => (f ⟨x, hx⟩).val) h
    have hset : fixedBy X a ∩ fixedPoints R X = fixedPoints R X := Set.inter_eq_right.mpr hsub
    change (fixedBy X a ∩ fixedPoints R X).ncard = 2 at htwo
    rw [hset, hRcard] at htwo
    omega
  let a' := c⁻¹ * a * c
  have ha'N : a' ∈ Subgroup.normalizer (Q : Set G) :=
    ConjugateFixedNormalizer.normalizer_conj_back G Q R c hc a hnorm
  have hneQ : fixedPermHom G X Q ⟨a', ha'N⟩ ≠ 1 := by
    intro h
    apply hneR
    rw [← ConjugateFixedNormalizer.permCongr_fixedPerm G X Q R c hc a hnorm]
    change (ConjugateFixedNormalizer.fixedEquiv G X Q R c hc).permCongr
      (fixedPermHom G X Q ⟨a', ha'N⟩) = 1
    rw [h]
    ext x
    simp
  have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  have ha'2 : a' ^ 2 = 1 := by
    have h := congrArg (MulAut.conj c⁻¹) ha2
    simpa only [map_pow, map_one, MulAut.conj_apply, inv_inv] using h
  have hmove : ∃ x ∈ fixedPoints Q X, a' • x ≠ x := by
    by_contra hn
    push Not at hn
    exact hneQ ((mem_ker_iff G X Q ⟨a', ha'N⟩).mpr hn)
  refine ⟨a', ha'N, ha'2, hneQ, ?_, ?_⟩
  · rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    simpa only [inv_inv] using
      (Nat.card_congr (SemiregularSylowFixedSet.fixedByConjugateEquiv G X a c⁻¹)).symm
  · exact NormalizerInvolutionFixedTwo.intersection_ncard_eq_two G X Q a' ha'N hcard ha'2
      (heven a' ha'N) hmove

end FiveTransitive.OyamaSixNormalizerRepresentative

end CFSG

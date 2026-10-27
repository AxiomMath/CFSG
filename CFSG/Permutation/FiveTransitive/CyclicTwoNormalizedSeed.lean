module

public import CFSG.Permutation.FiveTransitive.CyclicTwoTripleExclusion
public import CFSG.Permutation.FiveTransitive.HighDegreeNormalizedFourSeed

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.CyclicTwoNormalizedSeed

open MulAction FixedNormalizerAction

private theorem local_three_of_four
    {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (heven : ∀ g : G, Equiv.Perm.sign (toPermHom G X g) = 1)
    (hdegree : Fintype.card X % 4 = 3)
    (hmax : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ 7)
    (Q : Subgroup G) (hQ : Nat.card Q = 2)
    (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (himage : Image (X := X) Q = ⊤)
    (v : Normalizer Q) (hv : orderOf v.val = 2)
    (hfour : 4 ≤ (fixedBy X v.val \ fixedPoints Q X).ncard)
    (hlocal : (fixedBy X v.val ∩ fixedPoints Q X).ncard ≤ 3)
    (hzero : ∀ (A : Subgroup G), Q ≤ A → IsPGroup 2 A →
      ∀ u : Normalizer Q, u.val ∈ A → u.val ∉ Q →
      (fixedBy X u.val ∩ fixedPoints Q X).ncard = 5 →
      Nat.card (Function.fixedPoints
        (NormalizerSevenOrbitCount.orbitPerm (X := X) Q u)) = 0) :
    (fixedBy X v.val ∩ fixedPoints Q X).ncard = 3 ∧
      (fixedBy X v.val \ fixedPoints Q X).ncard = 4 := by
  classical
  let _ : Fintype (Fixed (X := X) Q) := Fintype.ofFinite _
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  have hvN : v ^ 2 = 1 := Subtype.ext (hv ▸ pow_orderOf_eq_one v.val)
  have hfv2 : (f v) ^ 2 = 1 := by rw [← map_pow, hvN, map_one]
  have htype := Equiv.Perm.cycleType_of_pow_prime_eq_one hfv2
  have hfixed := FixedNormalizerLocalCard.fixed_card (X := X) Q v
  have hcount := (f v).card_fixedPoints
  rw [← Nat.card_eq_fintype_card, hfixed, ← Nat.card_eq_fintype_card, hseven, htype,
    Multiset.sum_replicate, nsmul_eq_mul] at hcount
  have hbound := (f v).sum_cycleType_le
  rw [htype, Multiset.sum_replicate, nsmul_eq_mul, ← Nat.card_eq_fintype_card, hseven] at hbound
  simp only [Nat.cast_id] at hcount hbound
  have hcases : (fixedBy X v.val ∩ fixedPoints Q X).ncard = 1 ∨
      (fixedBy X v.val ∩ fixedPoints Q X).ncard = 3 := by omega
  have hsum := Set.ncard_inter_add_ncard_sdiff_eq_ncard (fixedBy X v.val) (fixedPoints Q X)
  have htotalmod := EvenInvolutionFixed.card_mod_four v.val hv (heven v.val)
  have hmaxv := hmax v.val hv
  have htotal : (fixedBy X v.val).ncard = 7 := by omega
  rcases hcases with hone | hthree
  · have hsix : (fixedBy X v.val \ fixedPoints Q X).ncard = 6 := by omega
    exact False.elim (CyclicTwoTripleExclusion.not_six heven hdegree hmax Q hQ hseven hfree
      S hS himage v hv hone hzero hsix)
  · exact ⟨hthree, by omega⟩

theorem exists_double_seed
    {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hcard : 28 ≤ Fintype.card X) (h5 : IsMultiplyPretransitive G X 5)
    (heven : ∀ g : G, Equiv.Perm.sign (toPermHom G X g) = 1)
    (hdegree : Fintype.card X % 4 = 3)
    (hmax : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ 7)
    (Q : Subgroup G) (hQ : Nat.card Q = 2)
    (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (himage : Image (X := X) Q = ⊤)
    (hzero : ∀ (A : Subgroup G), Q ≤ A → IsPGroup 2 A →
      ∀ u : Normalizer Q, u.val ∈ A → u.val ∉ Q →
      (fixedBy X u.val ∩ fixedPoints Q X).ncard = 5 →
      Nat.card (Function.fixedPoints
        (NormalizerSevenOrbitCount.orbitPerm (X := X) Q u)) = 0) :
    ∃ v : Normalizer Q, orderOf v.val = 2 ∧ v.val ∉ Q ∧
      (fixedBy X v.val ∩ fixedPoints Q X).ncard = 3 ∧
      (fixedBy X v.val \ fixedPoints Q X).ncard = 4 ∧
      ∃ T : Set X, T.ncard = 4 ∧ T ⊆ (fixedPoints Q X)ᶜ ∧
        ∀ t ∈ T, v.val • t = t := by
  have hQp : IsPGroup 2 Q := by rw [← hS]; exact S.isPGroup'.map _
  have hQne : Q ≠ ⊥ := by
    intro he
    rw [he, Subgroup.card_bot] at hQ
    norm_num at hQ
  have hseven' : Nat.card (fixedPoints Q X) = 7 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact hseven
  obtain ⟨v, hv, hvQ, hfour, hlocal, hT⟩ := HighDegreeNormalizedFourSeed.exists_normalized_seed
    hcard h5 hmax Q hQp hQne hseven' hfree S hS
  obtain ⟨hl, ho⟩ := local_three_of_four heven hdegree hmax Q hQ hseven hfree S hS himage
    v hv hfour hlocal hzero
  exact ⟨v, hv, hvQ, hl, ho, hT⟩

end FiveTransitive.CyclicTwoNormalizedSeed

end CFSG

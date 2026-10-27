module

public import CFSG.Permutation.FiveTransitive.OyamaSixElementary
public import CFSG.Permutation.FiveTransitive.OyamaSixFixedBranch
public import CFSG.Permutation.FiveTransitive.SixSylowOrderUpper

public section

namespace CFSG

namespace FiveTransitive.OyamaSixOrderUpper

open MulAction FixedSetNormalizerPerm

theorem even_of_alternating_image
    (G X : Type*) [Group G] [Fintype X] [MulAction G X] (Q : Subgroup G)
    (himage : letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (OyamaSixElementary.fixedHom G X Q).range = alternatingGroup (fixedPoints Q X)) :
    ∀ (a : G) (ha : a ∈ Subgroup.normalizer (Q : Set G)),
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPerm G X Q a ha).sign = 1 := by
  intro a ha
  let _ := Fintype.ofFinite (fixedPoints Q X)
  let _ : DecidableEq (fixedPoints Q X) := Classical.decEq _
  have hmem : fixedPerm G X Q a ha ∈ (OyamaSixElementary.fixedHom G X Q).range :=
    ⟨⟨a, ha⟩, rfl⟩
  rw [himage] at hmem
  exact Equiv.Perm.mem_alternatingGroup.mp hmem

theorem card_le_sixteen
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hX : 10 ≤ Fintype.card X)
    (h4 : IsMultiplyPretransitive G X 4) (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup G s)) [Nontrivial S]
    (hfree : ∀ (q : S) (x : X), x ∉ fixedPoints S X → q • x = x → q = 1)
    (hcard : (fixedPoints S X).ncard = 6)
    (himage : let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (OyamaSixElementary.fixedHom G X Q).range = alternatingGroup (fixedPoints Q X)) :
    Nat.card S ≤ 16 := by
  obtain ⟨hsq, hcomm⟩ := OyamaSixElementary.square_eq_one_and_commute
    G X h4 s hs S hfree hcard himage
  have hcardQ : (fixedPoints ((S : Subgroup (fixingSubgroup G s)).map
      (fixingSubgroup G s).subtype) X).ncard = 6 := by
    rw [OyamaSixElementary.fixedPoints_image]
    exact hcard
  exact SixSylowOrderUpper.card_le_sixteen G X hX h4 s hs S hfree hcard hsq hcomm
    hcardQ (even_of_alternating_image G X _ himage)

theorem involution_fixed_two_or_six
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h4 : IsMultiplyPretransitive G X 4) (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup G s))
    (hfree : ∀ (q : S) (x : X), x ∉ fixedPoints S X → q • x = x → q = 1)
    (hcard : (fixedPoints S X).ncard = 6)
    (himage : let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (OyamaSixElementary.fixedHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (a : G) (ha : orderOf a = 2) :
    (fixedBy X a).ncard = 2 ∨ (fixedBy X a).ncard = 6 := by
  have hcardQ : (fixedPoints ((S : Subgroup (fixingSubgroup G s)).map
      (fixingSubgroup G s).subtype) X).ncard = 6 := by
    rw [OyamaSixElementary.fixedPoints_image]
    exact hcard
  have hle := SixNormalizerInvolutionWitness.two_le_fixed G X h4 s hs S
    hcardQ (even_of_alternating_image G X _ himage) a ha
  rcases OyamaSixFixedBranch.involution_fixed_zero_two_or_six
    G X h4 s hs S hfree hcard a ha with hzero | hrest
  · omega
  · exact hrest

end FiveTransitive.OyamaSixOrderUpper

end CFSG

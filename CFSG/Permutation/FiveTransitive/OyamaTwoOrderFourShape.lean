module

public import CFSG.Permutation.FiveTransitive.OyamaTwoSquareFixed
public import CFSG.Permutation.FiveTransitive.SixOrderFourNormalizerRepresentative
public import CFSG.Permutation.FiveTransitive.OyamaSixOrderUpper
public import CFSG.Permutation.FiveTransitive.HigherTwoCycleShape
public import CFSG.Permutation.FiveTransitive.EvenSixOrderFourExists

public section

namespace CFSG

namespace FiveTransitive.OyamaTwoOrderFourShape

open MulAction FixedSetNormalizerHom

private theorem semiregular_of_card_two
    (H X : Type*) [Group H] [MulAction H X] (hH : Nat.card H = 2)
    (q : H) (x : X) (hx : x ∉ fixedPoints H X) (hqx : q • x = x) : q = 1 := by
  by_contra hq
  apply hx
  rw [mem_fixedPoints]
  intro r
  rcases Research.OddIndexTwoConjugacy.eq_one_or_eq_of_natCard_eq_two hH q hq r with h | h
  · rw [h, one_smul]
  · rw [h, hqx]

private theorem normalizer_fixed_zero_and_square_two
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h4 : IsMultiplyPretransitive G X 4) (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup G s)) (hS : Nat.card S = 2)
    (Q : Subgroup G)
    (hQ : (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype = Q)
    (hsix : (fixedPoints Q X).ncard = 6)
    (himage : letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPermHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (a : G) (haN : a ∈ Subgroup.normalizer (Q : Set G))
    (ha : orderOf a = 4) (hfa : orderOf (fixedPermHom G X Q ⟨a, haN⟩) = 4)
    (hzero : (fixedBy X a ∩ fixedPoints Q X).ncard = 0)
    (htwo : (fixedBy X (a ^ 2) ∩ fixedPoints Q X).ncard = 2) :
    (fixedBy X a).ncard = 0 ∧ (fixedBy X (a ^ 2)).ncard = 2 := by
  have hlt := OyamaTwoSquareFixed.square_fixed_lt_four G X h4 s hs S hS Q hQ hsix himage a haN ha hfa
  have hfree := semiregular_of_card_two S X hS
  have hfixed : (fixedPoints S X).ncard = 6 := by
    rw [← OyamaSixElementary.fixedPoints_image G X (fixingSubgroup G s) S, hQ]
    exact hsix
  have htwo' : (fixedBy X (a ^ 2)).ncard = 2 := by
    have horder : orderOf (a ^ 2) = 2 := by rw [orderOf_pow, ha]; norm_num
    have himage' := himage
    rw [← hQ] at himage'
    rcases OyamaSixOrderUpper.involution_fixed_two_or_six G X h4 s hs S hfree
      hfixed himage' (a ^ 2) horder with h | h
    · exact h
    · omega
  have heq : fixedBy X (a ^ 2) ∩ fixedPoints Q X = fixedBy X (a ^ 2) :=
    Set.eq_of_subset_of_ncard_le Set.inter_subset_left (by omega)
  have hsub : fixedBy X a ⊆ fixedPoints Q X := by
    intro x hx
    have hx2 : x ∈ fixedBy X (a ^ 2) := by
      change (a ^ 2) • x = x
      rw [pow_two, mul_smul, hx, hx]
    exact (heq.symm ▸ hx2).2
  refine ⟨?_, htwo'⟩
  rw [Set.inter_eq_left.mpr hsub] at hzero
  exact hzero

theorem fixed_zero_and_square_two
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (h4 : IsMultiplyPretransitive G X 4) (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup G s)) (hS : Nat.card S = 2)
    (hsix : (fixedPoints ((S : Subgroup (fixingSubgroup G s)).map
      (fixingSubgroup G s).subtype) X).ncard = 6)
    (himage : let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPermHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (a : G) (ha : orderOf a = 4) :
    (fixedBy X a).ncard = 0 ∧ (fixedBy X (a ^ 2)).ncard = 2 := by
  let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
  have heven := OyamaSixOrderUpper.even_of_alternating_image G X Q himage
  obtain ⟨a', ha'N, ha', hfa', hsame, hzero, htwo⟩ :=
    SixOrderFourNormalizerRepresentative.exists_conjugate G X h4 s hs S hsix heven a ha
  have hz : (fixedBy X a).ncard = 0 := hsame.symm.trans
    (normalizer_fixed_zero_and_square_two G X h4 s hs S hS Q rfl hsix himage
      a' ha'N ha' hfa' hzero htwo).1
  have hfree := semiregular_of_card_two S X hS
  have hfixed : (fixedPoints S X).ncard = 6 := by
    rwa [OyamaSixElementary.fixedPoints_image] at hsix
  have hinv (u : G) (hu : orderOf u = 2) :
      (fixedBy X u).ncard = 2 ∨ (fixedBy X u).ncard = 6 :=
    OyamaSixOrderUpper.involution_fixed_two_or_six G X h4 s hs S hfree hfixed himage u hu
  have hlocal := OyamaSixElementary.local_of_base G X h4 s hs S hsix heven
  have heq (u : G) : Nat.card (Function.fixedPoints (toPerm u : Equiv.Perm X)) =
      (fixedBy X u).ncard := by rw [Nat.card_coe_set_eq]; rfl
  have hbound (u : G) (hu : orderOf u = 2) :
      Nat.card (Function.fixedPoints (toPerm u : Equiv.Perm X)) ≤ 6 := by
    rw [heq]
    rcases hinv u hu with h | h <;> omega
  have hfour : 0 < Nat.card (CyclePatternRoots.FourRoot (toPerm a : Equiv.Perm X)) := by
    apply TwoPowerPeriodWitness.four_card_pos_of_order_four
    rw [HigherTwoCycleShape.order_toPerm, ha]
  have hshape := LocalEvenCycleShape.two_power_shape hlocal hbound a 2 (by decide) ha hfour
  have hsum := TwoElementFixedBound.fixed_square_card (toPerm a : Equiv.Perm X)
  rw [heq, hz] at hsum
  have hsquare : Nat.card (Function.fixedPoints ((toPerm a : Equiv.Perm X) ^ 2 : Equiv.Perm X)) =
      (fixedBy X (a ^ 2)).ncard := by
    change Nat.card (Function.fixedPoints ((toPermHom G X a) ^ 2 : Equiv.Perm X)) = _
    rw [← map_pow]
    exact heq (a ^ 2)
  rw [hsquare] at hsum
  have horder : orderOf (a ^ 2) = 2 := by rw [orderOf_pow, ha]; norm_num
  have hi := hinv (a ^ 2) horder
  exact ⟨hz, by omega⟩

theorem exists_order_four_shape
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (h4 : IsMultiplyPretransitive G X 4) (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup G s)) (hS : Nat.card S = 2)
    (hsix : (fixedPoints ((S : Subgroup (fixingSubgroup G s)).map
      (fixingSubgroup G s).subtype) X).ncard = 6)
    (himage : let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPermHom G X Q).range = alternatingGroup (fixedPoints Q X)) :
    ∃ a : G, orderOf a = 4 ∧ (fixedBy X a).ncard = 0 ∧ (fixedBy X (a ^ 2)).ncard = 2 := by
  classical
  let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
  let N := Subgroup.normalizer (Q : Set G)
  let _ := Fintype.ofFinite (fixedPoints Q X)
  let _ : DecidableEq (fixedPoints Q X) := Classical.decEq _
  have hsize : Fintype.card (fixedPoints Q X) = 6 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hsix
  obtain ⟨a, ha⟩ := EvenSixOrderFourExists.exists_order_four_of_alternating_image N (fixedPoints Q X)
    (fixedPermHom G X Q) hsize himage
  have haG : orderOf (a : G) = 4 := (Subgroup.orderOf_coe a).trans ha
  exact ⟨a, haG, fixed_zero_and_square_two G X h4 s hs S hS hsix himage a haG⟩

end FiveTransitive.OyamaTwoOrderFourShape

end CFSG

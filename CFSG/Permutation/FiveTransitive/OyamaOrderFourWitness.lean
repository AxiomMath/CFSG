module

public import CFSG.Permutation.FiveTransitive.EvenSixOrderFourExists
public import CFSG.Permutation.FiveTransitive.SixOrderFourNormalizerRepresentative
public import CFSG.Permutation.FiveTransitive.OyamaOrderFourShape

public section

namespace CFSG

namespace FiveTransitive.OyamaOrderFourWitness

open MulAction FixedSetNormalizerHom

theorem exists_order_four_normalizer
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hX : 10 ≤ Fintype.card X)
    (h4 : IsMultiplyPretransitive G X 4) (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup G s)) [Nontrivial S]
    (hfree : ∀ (q : S) (x : X), x ∉ fixedPoints S X → q • x = x → q = 1)
    (hcard : (fixedPoints S X).ncard = 6)
    (himage : let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (OyamaSixElementary.fixedHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (hS : Nat.card S = 16) :
    let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
    ∃ (a : G) (haN : a ∈ Subgroup.normalizer (Q : Set G)),
      orderOf a = 4 ∧ orderOf (fixedPermHom G X Q ⟨a, haN⟩) = 4 ∧
      (fixedBy X a).ncard = 2 ∧
      (fixedBy X a ∩ fixedPoints Q X).ncard = 0 ∧
      (fixedBy X (a ^ 2) ∩ fixedPoints Q X).ncard = 2 := by
  classical
  let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
  let N := Subgroup.normalizer (Q : Set G)
  let _ := Fintype.ofFinite (fixedPoints Q X)
  let _ : DecidableEq (fixedPoints Q X) := Classical.decEq _
  have hcardQ : (fixedPoints Q X).ncard = 6 := by
    rw [OyamaSixElementary.fixedPoints_image]
    exact hcard
  have hsize : Fintype.card (fixedPoints Q X) = 6 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hcardQ
  obtain ⟨b, hb⟩ := EvenSixOrderFourExists.exists_order_four_of_alternating_image N (fixedPoints Q X)
    (fixedPermHom G X Q) hsize himage
  have hbG : orderOf (b : G) = 4 := (Subgroup.orderOf_coe b).trans hb
  have heven := OyamaSixOrderUpper.even_of_alternating_image G X Q himage
  obtain ⟨a, haN, ha, hf, _, hzero, htwo⟩ := SixOrderFourNormalizerRepresentative.exists_conjugate
    G X h4 s hs S hcardQ heven b hbG
  have hfix := (OyamaOrderFourShape.fixed_two_and_two_root_four G X hX h4 s hs S
    hfree hcard himage hS a ha).1
  exact ⟨a, haN, ha, hf, hfix, hzero, htwo⟩

end FiveTransitive.OyamaOrderFourWitness

end CFSG

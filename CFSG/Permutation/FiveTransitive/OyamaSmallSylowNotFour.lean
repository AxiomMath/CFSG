module

public import CFSG.Permutation.FiveTransitive.SmallSylowNormalizerCentralizer
public import CFSG.Permutation.FiveTransitive.PrimePowerIntoSylow
public import CFSG.Permutation.FiveTransitive.EvenSixOrderFourExists
public import CFSG.Permutation.FiveTransitive.SixOrderFourNormalizerRepresentative
public import CFSG.Permutation.FiveTransitive.OyamaSixOrderUpper
public import CFSG.Permutation.FiveTransitive.OyamaSixNormalizerRepresentative
public import CFSG.Permutation.FiveTransitive.FourCentralizerFixedPointFree
public import CFSG.Permutation.FiveTransitive.FourCentralizingSquareCoset
public import CFSG.Permutation.FiveTransitive.NormalizerInvolutionModuloSylow

public section

namespace CFSG

namespace FiveTransitive.OyamaSmallSylowNotFour

open MulAction FixedSetNormalizerHom

theorem card_ne_four
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hX : 10 ≤ Fintype.card X)
    (h4 : IsMultiplyPretransitive G X 4) (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup G s)) [Nontrivial S]
    (hfree : ∀ (q : S) (x : X), x ∉ fixedPoints S X → q • x = x → q = 1)
    (hcard : (fixedPoints S X).ncard = 6)
    (himage : let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (OyamaSixElementary.fixedHom G X Q).range = alternatingGroup (fixedPoints Q X)) :
    Nat.card S ≠ 4 := by
  intro hS
  classical
  let H := fixingSubgroup G s
  let Q : Subgroup G := (S : Subgroup H).map H.subtype
  let N := Subgroup.normalizer (Q : Set G)
  let e : S ≃* Q := (S : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective
  have he : ∀ (q : S) (x : X), (Equiv.refl X) (q • x) = e q • (Equiv.refl X) x := by
    intro q x
    rfl
  have hQfree := EquivariantSemiregular.free_of_equivariant S Q X X e (Equiv.refl X) he hfree
  obtain ⟨hsq, hcomm⟩ := OyamaSixElementary.square_eq_one_and_commute G X h4 s hs S hfree hcard himage
  obtain ⟨hQ2, hQcomm⟩ := EquivariantSemiregular.square_and_commute_of_equiv S Q e hsq hcomm
  have hQcard : Nat.card Q = 4 := (Nat.card_congr e.toEquiv).symm.trans hS
  have hQfix : (fixedPoints Q X).ncard = 6 := by
    rw [OyamaSixElementary.fixedPoints_image]
    exact hcard
  have hcentral (a : G) (haN : a ∈ N) (k : ℕ) (hp : a ^ (2 ^ k) = 1) :
      ∀ q : Q, a * (q : G) = (q : G) * a :=
    SmallSylowNormalizerCentralizer.commutes G X s S Q rfl hQcomm (Or.inr hQcard) hQfix himage a haN k hp
  have heven := OyamaSixOrderUpper.even_of_alternating_image G X Q himage
  have hlocal := OyamaSixElementary.local_of_base G X h4 s hs S hQfix heven
  have hfixCard (u : G) : Nat.card (Function.fixedPoints (toPerm u : Equiv.Perm X)) = (fixedBy X u).ncard := by
    rw [Nat.card_coe_set_eq]
    rfl
  have hinv : ∀ u : G, orderOf u = 2 →
      Nat.card (Function.fixedPoints (toPerm u : Equiv.Perm X)) = 2 ∨
      Nat.card (Function.fixedPoints (toPerm u : Equiv.Perm X)) = 6 := by
    intro u hu
    rw [hfixCard]
    exact OyamaSixOrderUpper.involution_fixed_two_or_six G X h4 s hs S hfree hcard himage u hu
  let _ := Fintype.ofFinite (fixedPoints Q X)
  let _ : DecidableEq (fixedPoints Q X) := Classical.decEq _
  have hsize : Fintype.card (fixedPoints Q X) = 6 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact hQfix
  obtain ⟨z, hz⟩ := EvenSixOrderFourExists.exists_order_four_of_alternating_image N (fixedPoints Q X)
    (fixedPermHom G X Q) hsize himage
  have hzG : orderOf (z : G) = 4 := (Subgroup.orderOf_coe z).trans hz
  obtain ⟨a, haN, ha, haImage, _, haZero, _⟩ := SixOrderFourNormalizerRepresentative.exists_conjugate
    G X h4 s hs S hQfix heven z hzG
  have ha4 : a ^ 4 = 1 := ha ▸ pow_orderOf_eq_one a
  have haC := hcentral a haN 2 ha4
  have haSmall := PrimePowerIntoSylow.fixed_lt_four_of_order_four G X h4 s hs S hsq a ha
  have haFixZero := FourCentralizerFixedPointFree.fixed_ncard_zero G X Q hQcard hQfree a haC haSmall haZero
  have haSqFix : (fixedBy X (a ^ 2)).ncard = 2 := by
    have h := FourCentralizerFixedPointFree.square_fixed_two G X hlocal hinv a ha (by rwa [hfixCard])
    rwa [hfixCard] at h
  have haSqN : a ^ 2 ∈ N := N.pow_mem haN 2
  have haSq2 : (a ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact ha4
  have haSqImage : fixedPermHom G X Q ⟨a ^ 2, haSqN⟩ ≠ 1 := by
    intro h
    have hp : (fixedPermHom G X Q ⟨a, haN⟩) ^ 2 = 1 := by
      rw [← map_pow]
      exact h
    have hd := orderOf_dvd_of_pow_eq_one hp
    rw [haImage] at hd
    norm_num at hd
  obtain ⟨v, hv⟩ := exists_ne (1 : S)
  have hvOrder : orderOf v = 2 := orderOf_eq_prime (by simpa only [pow_two] using hsq v) hv
  let vG : G := ((v : H) : G)
  have hvGOrder : orderOf vG = 2 :=
    (Subgroup.orderOf_coe (v : H)).trans ((Subgroup.orderOf_coe v).trans hvOrder)
  have hvSix : (fixedBy X vG).ncard = 6 := by
    change (fixedBy X v).ncard = 6
    rw [SemiregularSylowFixedSet.fixedBy_eq_fixedPoints S X hfree v hv, hcard]
  have hvMoved : 4 ≤ (fixedBy X vG)ᶜ.ncard := by
    rw [Set.ncard_compl, hvSix, Nat.card_eq_fintype_card]
    omega
  obtain ⟨b, hbN, hb2, hbImage, hbFix, hbTwo⟩ := OyamaSixNormalizerRepresentative.exists_conjugate
    G X h4 s hs S hQfix heven vG hvGOrder hvMoved
  have hbSix : (fixedBy X b).ncard = 6 := hbFix.trans hvSix
  have hbC := hcentral b hbN 1 hb2
  obtain ⟨c, hc⟩ := NormalizerInvolutionModuloSylow.exists_conjugator G X s S Q rfl hQfix himage
    (a ^ 2) b haSqN hbN haSq2 hb2 haSqImage hbImage
  let a' := (c : G) * a * (c : G)⁻¹
  have ha'N : a' ∈ N := N.mul_mem (N.mul_mem c.property haN) (N.inv_mem c.property)
  have ha'4 : a' ^ 4 = 1 := by
    change ((c : G) * a * (c : G)⁻¹) ^ 4 = 1
    rw [conj_pow, ha4]
    group
  have hcoset : a' ^ 2 * b⁻¹ ∈ Q := by
    change (((c : G) * a * (c : G)⁻¹) ^ 2) * b⁻¹ ∈ Q
    rw [conj_pow]
    exact hc
  have hsquare := FourCentralizingSquareCoset.square_eq G X Q hQcard hQ2 hQfree a' b ha'N
    (hcentral a' ha'N 2 ha'4) hbC hcoset hbSix hbTwo
  have hconj : (c : G) * a ^ 2 * (c : G)⁻¹ = b := by
    rw [← conj_pow]
    exact hsquare
  have hfixeq : (fixedBy X (a ^ 2)).ncard = (fixedBy X b).ncard := by
    rw [← hconj, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact Nat.card_congr (SemiregularSylowFixedSet.fixedByConjugateEquiv G X (a ^ 2) c)
  omega

end FiveTransitive.OyamaSmallSylowNotFour

end CFSG

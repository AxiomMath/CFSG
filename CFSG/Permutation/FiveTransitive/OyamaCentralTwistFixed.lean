module

public import CFSG.Permutation.FiveTransitive.NormalizerInvolutionModuloSylow
public import CFSG.Permutation.FiveTransitive.OyamaSixNormalizerRepresentative
public import CFSG.Permutation.FiveTransitive.OyamaSixOrderUpper
public import CFSG.Permutation.FiveTransitive.NormalizerTwoElementInvolution

public section

namespace CFSG

namespace FiveTransitive.OyamaCentralTwistFixed

open MulAction FixedSetNormalizerHom

theorem fixedBy_eq_of_card_two
    {G X : Type*} [Group G] [MulAction G X]
    (Q : Subgroup G) (hQ : Nat.card Q = 2) (q : Q) (hq : q ≠ 1) :
    fixedBy X (q : G) = fixedPoints Q X := by
  ext x
  constructor
  · intro hx
    rw [mem_fixedPoints]
    intro r
    rcases Research.OddIndexTwoConjugacy.eq_one_or_eq_of_natCard_eq_two hQ q hq r with h | h
    · rw [h, one_smul]
    · rw [h]; exact hx
  · intro hx
    exact mem_fixedPoints.mp hx q

theorem twist_fixed_six
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hX : 10 ≤ Nat.card X) (h4 : IsMultiplyPretransitive G X 4)
    (s : Set X) (hs : s.ncard = 4) (S : Sylow 2 (fixingSubgroup G s))
    (Q : Subgroup G)
    (hQ : (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype = Q)
    (hcard : Nat.card Q = 2) (hsix : (fixedPoints Q X).ncard = 6)
    (himage : letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPermHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (q : Q) (hq : q ≠ 1) (z : G)
    (hzN : z ∈ Subgroup.normalizer (Q : Set G)) (hz : z ^ 2 = 1)
    (hzi : fixedPermHom G X Q ⟨z, hzN⟩ ≠ 1)
    (hzfix : (fixedBy X z).ncard = 2) :
    (fixedBy X ((q : G) * z)).ncard = 6 := by
  have hqpow : q ^ 2 = 1 := by rw [← hcard]; exact pow_card_eq_one' (x := q)
  have hqorder : orderOf (q : G) = 2 :=
    (Subgroup.orderOf_coe q).trans (orderOf_eq_prime hqpow hq)
  have hqfix : (fixedBy X (q : G)).ncard = 6 := by
    rw [fixedBy_eq_of_card_two Q hcard q hq, hsix]
  have hmove : 4 ≤ (fixedBy X (q : G))ᶜ.ncard := by
    rw [Set.ncard_compl, hqfix]
    omega
  have heven := OyamaSixOrderUpper.even_of_alternating_image G X Q himage
  have hbasefix : (fixedPoints ((S : Subgroup (fixingSubgroup G s)).map
      (fixingSubgroup G s).subtype) X).ncard = 6 := by rw [hQ]; exact hsix
  have heven' := heven
  rw [← hQ] at heven'
  have hex := OyamaSixNormalizerRepresentative.exists_conjugate
    G X h4 s hs S hbasefix heven' (q : G) hqorder hmove
  rw [hQ] at hex
  obtain ⟨b, hbN, hb2, hbi, hbfix, _⟩ := hex
  have hb6 : (fixedBy X b).ncard = 6 := hbfix.trans hqfix
  obtain ⟨c, hc⟩ := NormalizerInvolutionModuloSylow.exists_conjugator G X s S Q hQ
    hsix himage z b hzN hbN hz hb2 hzi hbi
  let w : Q := ⟨((c : G) * z * (c : G)⁻¹) * b⁻¹, hc⟩
  have htwist : (c : G) * ((q : G) * z) * (c : G)⁻¹ = b := by
    rcases Research.OddIndexTwoConjugacy.eq_one_or_eq_of_natCard_eq_two hcard q hq w with hw | hw
    · have he : (c : G) * z * (c : G)⁻¹ = b := by
        apply mul_inv_eq_one.mp
        exact congrArg Subtype.val hw
      have hcount : (fixedBy X z).ncard = (fixedBy X b).ncard := by
        rw [← he, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
        exact Nat.card_congr (SemiregularSylowFixedSet.fixedByConjugateEquiv G X z c)
      omega
    · have he : (c : G) * z * (c : G)⁻¹ = (q : G) * b := by
        apply mul_inv_eq_iff_eq_mul.mp
        exact congrArg Subtype.val hw
      have hcomm : (c : G) * (q : G) = (q : G) * (c : G) :=
        (NormalizerTwoElementInvolution.central_of_card_two Q hcard c q).symm
      have hq2 : (q : G) * (q : G) = 1 := by
        exact congrArg Subtype.val (show q * q = 1 by simpa only [pow_two] using hqpow)
      calc
        (c : G) * ((q : G) * z) * (c : G)⁻¹ =
            (q : G) * ((c : G) * z * (c : G)⁻¹) := by rw [← mul_assoc, hcomm]; group
        _ = (q : G) * ((q : G) * b) := by rw [he]
        _ = b := by rw [← mul_assoc, hq2, one_mul]
  have hcount : (fixedBy X ((q : G) * z)).ncard = (fixedBy X b).ncard := by
    rw [← htwist, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact Nat.card_congr (SemiregularSylowFixedSet.fixedByConjugateEquiv G X ((q : G) * z) c)
  exact hcount.trans hb6

end FiveTransitive.OyamaCentralTwistFixed

end CFSG

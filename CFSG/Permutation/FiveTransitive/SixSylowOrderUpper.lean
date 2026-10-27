module

public import CFSG.Permutation.FiveTransitive.SixNormalizerInvolutionWitness
public import CFSG.Permutation.FiveTransitive.EquivariantSemiregular
public import CFSG.Permutation.FiveTransitive.SemiregularSylowFixedSet
public import CFSG.Permutation.FiveTransitive.SemiregularNormalizerBound

public section

namespace CFSG

namespace FiveTransitive.SixSylowOrderUpper

open MulAction FixedSetNormalizerPerm

theorem card_le_sixteen
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hX : 10 ≤ Fintype.card X)
    (h4 : IsMultiplyPretransitive G X 4) (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup G s)) [Nontrivial S]
    (hfree : ∀ (q : S) (x : X), x ∉ fixedPoints S X → q • x = x → q = 1)
    (hcard : (fixedPoints S X).ncard = 6)
    (hsq : ∀ q : S, q * q = 1) (hcomm : ∀ q r : S, q * r = r * q)
    (hcardQ : (fixedPoints ((S : Subgroup (fixingSubgroup G s)).map
      (fixingSubgroup G s).subtype) X).ncard = 6)
    (heven : let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
      ∀ (a : G) (ha : a ∈ Subgroup.normalizer (Q : Set G)),
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPerm G X Q a ha).sign = 1) : Nat.card S ≤ 16 := by
  classical
  let H := fixingSubgroup G s
  let Q := (S : Subgroup H).map H.subtype
  obtain ⟨b, hb⟩ := exists_ne (1 : S)
  have hb2 : orderOf b = 2 := orderOf_eq_prime (by simpa only [pow_two] using hsq b) hb
  let bG : G := ((b : H) : G)
  have hbG2 : orderOf bG = 2 :=
    (Subgroup.orderOf_coe (b : H)).trans ((Subgroup.orderOf_coe b).trans hb2)
  have hbfix : (fixedBy X bG).ncard = 6 := by
    change (fixedBy X b).ncard = 6
    rw [SemiregularSylowFixedSet.fixedBy_eq_fixedPoints S X hfree b hb, hcard]
  have hbmoved : 4 ≤ (fixedBy X bG)ᶜ.ncard := by
    rw [Set.ncard_compl, hbfix, Nat.card_eq_fintype_card]
    omega
  obtain ⟨c, hnorm, htwo⟩ := SixNormalizerInvolutionWitness.exists_conjugate
    G X h4 s hs S hcardQ heven bG hbG2 hbmoved
  let R := Q.map (MulAut.conj c).toMonoidHom
  let e₁ : S ≃* Q := (S : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective
  let e₂ : Q ≃* R := Q.equivMapOfInjective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective
  let φ : S ≃* R := e₁.trans e₂
  have hφ (q : S) : (φ q : G) = c * (((q : H) : G)) * c⁻¹ := rfl
  have he : ∀ (q : S) (x : X), (MulAction.toPerm c) (q • x) = φ q • (MulAction.toPerm c) x := by
    intro q x
    change c • (((q : H) : G) • x) = (φ q : G) • (c • x)
    rw [hφ, mul_smul, mul_smul, inv_smul_smul]
  have hfreeR := EquivariantSemiregular.free_of_equivariant S R X X φ (MulAction.toPerm c) he hfree
  obtain ⟨hsqR, hcommR⟩ := EquivariantSemiregular.square_and_commute_of_equiv S R φ hsq hcomm
  have hbGsq : bG * bG = 1 := by
    have h := pow_orderOf_eq_one bG
    simpa only [hbG2, pow_two] using h
  have hbound := SemiregularNormalizerBound.card_le_sixteen_of_fixed_six G X R hcommR hsqR
    bG hnorm hbGsq hfreeR hbfix htwo
  exact (Nat.card_congr φ.toEquiv).trans_le hbound

end FiveTransitive.SixSylowOrderUpper

end CFSG

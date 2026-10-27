module

public import CFSG.Permutation.FiveTransitive.OyamaSixOrderUpper
public import CFSG.Permutation.FiveTransitive.SixSylowNormalizerWitness
public import CFSG.Permutation.FiveTransitive.ConjugateFixedImage
public import CFSG.Permutation.FiveTransitive.NormalizerSylowSimpleAutomorphism
public import CFSG.Permutation.FiveTransitive.TwoGroupFiveAutomorphism

public section

namespace CFSG

namespace FiveTransitive.OyamaSixOrderAlternatives

open MulAction FixedSetNormalizerPerm

private theorem card_eq_sixteen_of_four_lt
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hX : 10 ≤ Fintype.card X)
    (h4 : IsMultiplyPretransitive G X 4) (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup G s)) [Nontrivial S]
    (hfree : ∀ (q : S) (x : X), x ∉ fixedPoints S X → q • x = x → q = 1)
    (hcard : (fixedPoints S X).ncard = 6)
    (himage : let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (OyamaSixElementary.fixedHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (hgt : 4 < Nat.card S) : Nat.card S = 16 := by
  classical
  let H := fixingSubgroup G s
  let Q := (S : Subgroup H).map H.subtype
  obtain ⟨hsq, hcomm⟩ := OyamaSixElementary.square_eq_one_and_commute G X h4 s hs S hfree hcard himage
  have hupper := OyamaSixOrderUpper.card_le_sixteen G X hX h4 s hs S hfree hcard himage
  have hcardQ : (fixedPoints Q X).ncard = 6 := by
    rw [OyamaSixElementary.fixedPoints_image]
    exact hcard
  have heven := OyamaSixOrderUpper.even_of_alternating_image G X Q himage
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
  obtain ⟨t, T, c, ht, hc, hnorm, htwo⟩ := SixSylowNormalizerWitness.exists_sylow_conjugate
    G X h4 s hs S hcardQ heven bG hbG2 hbmoved
  let R := (T : Subgroup (fixingSubgroup G t)).map (fixingSubgroup G t).subtype
  let e₁ : S ≃* Q := (S : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective
  let e₂ : Q ≃* Q.map (MulAut.conj c).toMonoidHom :=
    Q.equivMapOfInjective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective
  let φ : S ≃* R := e₁.trans (e₂.trans (MulEquiv.subgroupCongr hc))
  have hφ (q : S) : (φ q : G) = c * (((q : H) : G)) * c⁻¹ := rfl
  have he : ∀ (q : S) (x : X), (MulAction.toPerm c) (q • x) = φ q • (MulAction.toPerm c) x := by
    intro q x
    change c • (((q : H) : G) • x) = (φ q : G) • (c • x)
    rw [hφ, mul_smul, mul_smul, inv_smul_smul]
  have hfreeR := EquivariantSemiregular.free_of_equivariant S R X X φ (MulAction.toPerm c) he hfree
  obtain ⟨_, hcommR⟩ := EquivariantSemiregular.square_and_commute_of_equiv S R φ hsq hcomm
  obtain ⟨hRcard, _⟩ := ConjugateFixedNormalizer.six_even_of_conjugate G X Q R c hc hcardQ heven
  have himageR := ConjugateFixedImage.alternating_image_of_conjugate G X Q R c hc himage
  change (fixedBy X bG ∩ fixedPoints R X).ncard = 2 at htwo
  have hfour : (fixedBy X bG \ fixedPoints R X).ncard = 4 := by
    have h := Set.ncard_inter_add_ncard_sdiff_eq_ncard (fixedBy X bG) (fixedPoints R X)
    omega
  obtain ⟨x, hbx, hx⟩ := (Set.ncard_pos (Set.toFinite _)).mp
    (by omega : 0 < (fixedBy X bG \ fixedPoints R X).ncard)
  let a : Subgroup.normalizer (R : Set G) := ⟨bG, hnorm⟩
  have hapow : a ^ (2 ^ 1) = 1 := by
    apply Subtype.ext
    change bG ^ (2 ^ 1) = 1
    simpa only [hbG2, pow_one] using pow_orderOf_eq_one bG
  have hsize : Nat.card S = Nat.card R := Nat.card_congr φ.toEquiv
  have hfive : 5 ∣ Nat.card (MulAut R) :=
    NormalizerSylowSimpleAutomorphism.five_dvd_aut_card G X t T R rfl hcommR hRcard himageR
      a 1 hapow x hbx hx (fun q => hfreeR q x hx) (by change
        (fixedBy X bG \ fixedPoints R X).ncard < Nat.card R; omega)
  have hRtwo : IsPGroup 2 R := T.isPGroup'.map (fixingSubgroup G t).subtype
  have hRupper : Nat.card R ≤ 16 := by omega
  exact hsize.trans (TwoGroupFiveAutomorphism.card_eq_sixteen_of_five_dvd_aut_card R hRtwo hRupper hfive)

theorem card_eq_two_four_or_sixteen
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
    Nat.card S = 2 ∨ Nat.card S = 4 ∨ Nat.card S = 16 := by
  by_cases hgt : 4 < Nat.card S
  · exact Or.inr (Or.inr (card_eq_sixteen_of_four_lt G X hX h4 s hs S hfree hcard himage hgt))
  have hnontriv : 1 < Nat.card S := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  have hk2 : k ≤ 2 := by
    by_contra hn
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 3 ≤ k by omega)
    norm_num at hp
    omega
  interval_cases k <;> norm_num only [pow_zero, pow_one, Nat.reducePow] at hk <;> omega

end FiveTransitive.OyamaSixOrderAlternatives

end CFSG

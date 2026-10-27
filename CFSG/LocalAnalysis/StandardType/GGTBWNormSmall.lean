module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormLowRank
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNine
public import CFSG.RankThree.PartOne.Q1327C.BNoCube
public import CFSG.RankThree.Chevalley.SteinbergCFExceptionalModelCover
public import CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProofRank
public import CFSG.RankThree.PartTwo.Sec8.Item89Res2ProofJTypeRee

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem largeEvenLabelAll_wnorm_nineSmall {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hp2 : p ≠ 2) (hlab : LargeEvenInLambda2 lab)
    (hsmall : GGTableBNbrInnerNineSmallLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  unfold GGTableBNbrInnerNineSmallLabel at hsmall
  rcases hsmall with h | h | h | h | h | h | h | h | ⟨ht, hl⟩
  · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hlab (Or.inl h)).mono
      fun _ _ _ _ hX => ggTorusWNormSC_of_card_lt hX
  · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hlab (Or.inr (Or.inl h))).mono
      fun _ _ _ _ hX => ggTorusWNormSC_of_card_lt hX
  · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hlab (Or.inr (Or.inr (Or.inl h)))).mono
      fun _ _ _ _ hX => ggTorusWNormSC_of_card_lt hX
  · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hlab
      (Or.inr (Or.inr (Or.inr (Or.inl h))))).mono
      fun _ _ _ _ hX => ggTorusWNormSC_of_card_lt hX
  · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hlab
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))).mono
      fun _ _ _ _ hX => ggTorusWNormSC_of_card_lt hX
  · exact largeEvenLabelAll_wnorm_A_le_two h.1 (by omega) hp hp2
  · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hlab
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))).mono
      fun _ _ _ _ hX => ggTorusWNormSC_of_card_lt hX
  · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hlab
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))).mono
      fun _ _ _ _ hX => ggTorusWNormSC_of_card_lt hX
  · exact largeEvenLabelAll_wnorm_twA_two hlab ht hl hp hp2


section Triality


theorem NbrInnerNine.largeEvenLabelAll_card_lt_triD4_all {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .triD4) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  by_cases hp3 : p = 3
  · exact NbrInnerNine.largeEvenLabelAll_card_lt_triD4_of hp hlab ht (Or.inl hp3)
  have hp5 : 5 ≤ p := by
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by decide)
    have h2 := hp.two_le
    omega
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab
  subst ht
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, fun X hXI hX => ?_⟩
  have : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := n * 3)
    (by rw [hK, pow_mul])
  let σ := iterateFrobeniusEquiv K 2 n
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [show σ = iterateFrobeniusEquiv K 2 n from rfl,
      iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨e⟩ := TableBExcSmallRest.nonempty_triD4_equiv hn K hK σ hσ
  obtain ⟨-, -, -, -, -, -, hZC, -⟩ :=
    CFSG.LieType.Chevalley.even_triality_exact_automorphism_normal_form hn K hK σ hσ
  have : Finite (ModGL TwistTag.D4.tag K) :=
    CFSG.LieType.Chevalley.finite_modGL
  have : Finite (LargeEvenCenterQuot
      (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)) :=
    Finite.of_equiv _ e.symm.toEquiv
  have hmodel : CFSG.Blueprint.ChevalleyExceptionalModel
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) .trialityD4 2 n := by
    obtain ⟨e₀⟩ := CFSG.RankThree.Chevalley.nonempty_derivedCentralQuotient_equiv
      TwistTag.D4 Nat.prime_two hn K hK σ.toRingHom hσ
    exact ⟨⟨Nat.prime_two, hn, rfl⟩, K, inferInstance, inferInstance, hK, σ.toRingHom,
      hσ, ⟨e₀.symm⟩⟩
  have hbound : ∀ E : Subgroup
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsElemAbelian p E → Nat.card E < p ^ 3 := by
    intro E hE
    by_contra hlt
    obtain ⟨F, hFcard⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card hp
      (CFSG.RankThree.PartOne.N143X.isPGroup_of_pow_eq_one hE.2) (not_lt.mp hlt)
    have hmapcard : Nat.card (F.map E.subtype) = p ^ 3 := by
      rw [Subgroup.card_map_of_injective E.subtype_injective, hFcard]
    exact CFSG.RankThree.PartOne.Q1327C.false_of_pow_three_triality_five hmodel hp hp5
      (fun x hx => hE.2 x (Subgroup.map_subtype_le F hx)) hmapcard
  have hI := TableBExcSmallRest.chevIDImage_subset_inn_triD4 hn K hK
  refine TableBExcSmallRest.card_lt_of_subset_inn
    (TableBExcSmallRest.center_eq_bot_of_mulEquiv e hZC)
    (fun A hA => TableBExcSmallRest.card_lt_of_mulEquiv e hbound hA)
    (fun φ hφ => ?_) hX
  obtain ⟨r, hr⟩ := hI (hXI hφ)
  exact ⟨r, hr⟩

theorem largeEvenLabelAll_wnorm_triality {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .triD4) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I :=
  (NbrInnerNine.largeEvenLabelAll_card_lt_triD4_all hp hp2 hlab ht).mono
    fun _ _ _ _ hX => ggTorusWNormSC_of_card_lt hX

end Triality


section LargeRee

open CFSG.LieType.Ree

theorem NbrInnerNine.largeEvenLabelAll_card_lt_twF4_all {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .twF4) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab
  subst ht
  obtain ⟨-, -, ⟨k, hk⟩, hn3⟩ := hlab
  have hk' : n = 2 * k + 1 := hk
  have hna : 2 * ((n - 1) / 2) + 1 = n := by omega
  have ha : 1 ≤ (n - 1) / 2 := by omega
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, fun X hXI hX => ?_⟩
  have : CharP K ReeTag.F4.prime := charP_two_of_card hK
  have hK' : Nat.card K = 2 ^ (2 * ((n - 1) / 2) + 1) := hK
  obtain ⟨e⟩ := TableBExcSmallRest.nonempty_twF4_equiv ha K hK'
  have hZ := TableBExcSmallRest.center_eq_bot_of_mulEquiv e
    (ReeTag.large_Ree_fixed_group_center_trivial _ K hK')
  have : Finite (ModGL Tag.F4 K) := finite_modGL
  have : Finite (LargeEvenCenterQuot (LargeEvenTwF4H ((n - 1) / 2) K)) :=
    Finite.of_equiv _ e.symm.toEquiv
  have hmodel := CFSG.RankThree.PartTwo.Sec8.Item89Res2.reeTitsModel_reeGamma ha hK'
  have hbound : ∀ E : Subgroup (ReeTag.F4.reeGamma K ((n - 1) / 2)),
      IsElemAbelian p E → Nat.card E < p ^ 3 := by
    intro E hE
    by_cases hp3 : p = 3
    · subst hp3
      have hcard := CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProof.card_le_nine_of_reeGamma
        ((n - 1) / 2) K hK' E hE
      exact hcard.trans_lt (by norm_num)
    · have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
      by_contra hlt
      obtain ⟨F, hFcard⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card hp
        (CFSG.RankThree.PartOne.N143X.isPGroup_of_pow_eq_one hE.2) (not_lt.mp hlt)
      have hmapcard : Nat.card (F.map E.subtype) = p ^ 3 := by
        rw [Subgroup.card_map_of_injective E.subtype_injective, hFcard]
      exact CFSG.RankThree.PartOne.Q1327C.false_of_pow_three_ree_five hmodel hp hp5
        (fun x hx => hE.2 x (Subgroup.map_subtype_le F hx)) hmapcard
  have hI := chevIDImage_subset_inn_twF4 ha K hK'
  refine TableBExcSmallRest.card_lt_of_subset_inn hZ
    (fun A hA => TableBExcSmallRest.card_lt_of_mulEquiv e hbound hA)
    (fun φ hφ => ?_) hX
  obtain ⟨r, hr⟩ := hI (hXI hφ)
  exact ⟨r, hr⟩


theorem largeEvenLabelAll_wnorm_largeRee {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twF4) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I :=
  (NbrInnerNine.largeEvenLabelAll_card_lt_twF4_all hp hp2 hlab ht).mono
    fun _ _ _ _ hX => ggTorusWNormSC_of_card_lt hX

end LargeRee

end CFSG.StandardType

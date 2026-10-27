module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRest
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanksTri
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanksTwF4

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree TableBExcSmallRest

namespace TableBExcSmallRanks

@[expose] def GGTableBExcSmallRanksDoneLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .G2der ∨ lab.tag = .triD4 ∨ (lab.tag = .twF4 ∧ p ≠ 3)

section TwF4


theorem largeEvenLabelAll_card_lt_twF4_of {p : ℕ}
    (hF : ∀ a : ℕ, 1 ≤ a → ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime],
      Nat.card K = 2 ^ (2 * a + 1) → p ∣ 2 ^ (2 * a + 1) + 1 →
      ∀ E : Subgroup (ReeTag.F4.reeGamma K a), IsElemAbelian p E → Nat.card E < p ^ 3)
    {lab : LargeEvenLabel} (hp : p.Prime) (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .twF4) (hs : LargeEvenSplit p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  have hpn := dvd_of_largeEvenSplit_twF4 ht hlab hs
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab hpn
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
  obtain ⟨e⟩ := nonempty_twF4_equiv ha K hK
  have hZ := center_eq_bot_of_mulEquiv e (ReeTag.large_Ree_fixed_group_center_trivial _ K hK)
  have : Finite (ModGL Tag.F4 K) := finite_modGL
  have : Finite (LargeEvenCenterQuot (LargeEvenTwF4H ((n - 1) / 2) K)) :=
    Finite.of_equiv _ e.symm.toEquiv
  have hcop : Nat.Coprime p (Nat.card Kˣ) := by
    rw [Nat.card_units, hK, hna]
    exact coprime_of_dvd_two_pow_add_one hp (by omega) hpn
  have hXinn := subset_inn_of_pow_eq_one (ggOutCyclic_twF4 ha K hK)
    (D := LargeEvenChevDiagImage LargeEvenCartanF4 K (LargeEvenTwF4H ((n - 1) / 2) K))
    (fun δ hδ => pow_card_units_eq_one_of_mem_diagImage hδ) hcop hXI (fun χ hχ => hX.2 χ hχ)
  exact card_lt_of_subset_inn hZ (fun A hA => card_lt_of_mulEquiv e
    (fun E hE => hF _ ha K hK (by rw [hna]; exact hpn) E hE) hA) hXinn hX


theorem largeEvenLabelAll_card_lt_twF4_of_ne_three {p : ℕ} (hp3 : p ≠ 3)
    {lab : LargeEvenLabel} (hp : p.Prime) (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .twF4) (hs : LargeEvenSplit p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  refine largeEvenLabelAll_card_lt_twF4_of (fun a ha K _ _ _ hK hpq E hE => ?_) hp hlab ht hs
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h1 : 2 ^ (2 * a + 1) + 1 = 2 * 2 ^ (2 * a) + 1 := by ring
    rw [h1] at hpq
    omega
  have hp4 : p ≠ 4 := by
    rintro rfl
    exact absurd hp (by decide)
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    omega
  exact (card_le_sq_twF4_of_five_le ha K hK hp hp5 hpq hE).trans_lt
    (Nat.pow_lt_pow_right hp.one_lt (by norm_num))

end TwF4

section Labels


theorem largeEvenLabelAll_card_lt_smallRanksDone {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (h : GGTableBExcSmallRanksDoneLabel p lab)
    (hs : LargeEvenSplit p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  rcases h with ht | ht | ⟨ht, hp3⟩
  · exact largeEvenLabelAll_card_lt_G2der hp hlab ht hs
  · exact largeEvenLabelAll_card_lt_triD4 (fun _ => ggTriD4ThreeRankInput_holds) hp hlab ht hs
  · exact largeEvenLabelAll_card_lt_twF4_of_ne_three hp3 hp hlab ht hs


theorem largeEvenLabelAll_card_lt_smallRanks (hF3 : GGTwF4ThreeRankInput)
    (hT : GGTitsThreeRankInput) {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (h : GGTableBExcSmallRestLabel p lab)
    (hs : LargeEvenSplit p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 :=
  largeEvenLabelAll_card_lt_smallRest ggTriD4ThreeRankInput_holds (ggTwF4RankInput_of_three hF3)
    hT hp hlab h hs

end Labels

section Inputs


theorem ggBstarInputOn_smallRanksDone : GGBstarInputOn GGTableBExcSmallRanksDoneLabel :=
  ggBstarInputOn_of_labelAll_card_lt fun _ _ hp hlab h hs =>
    largeEvenLabelAll_card_lt_smallRanksDone hp hlab h hs

theorem ggStdSubPreInputOn_smallRanksDone : GGStdSubPreInputOn GGTableBExcSmallRanksDoneLabel :=
  ggStdSubPreInputOn_of_labelAll_card_lt fun _ _ hp hlab h hs =>
    largeEvenLabelAll_card_lt_smallRanksDone hp hlab h hs


theorem ggBstarInputOn_smallRest_of_three (hF3 : GGTwF4ThreeRankInput)
    (hT : GGTitsThreeRankInput) : GGBstarInputOn GGTableBExcSmallRestLabel :=
  ggBstarInputOn_smallRest ggTriD4ThreeRankInput_holds (ggTwF4RankInput_of_three hF3) hT

theorem ggStdSubPreInputOn_smallRest_of_three (hF3 : GGTwF4ThreeRankInput)
    (hT : GGTitsThreeRankInput) : GGStdSubPreInputOn GGTableBExcSmallRestLabel :=
  ggStdSubPreInputOn_smallRest ggTriD4ThreeRankInput_holds (ggTwF4RankInput_of_three hF3) hT

theorem ggBstarInputOn_rest4NoF4_of_noSmall_three (hF3 : GGTwF4ThreeRankInput)
    (hT : GGTitsThreeRankInput) (h : GGBstarInputOn GGTableBOtherRestNoSmall) :
    GGBstarInputOn GGTableBOtherRest4NoF4 :=
  ggBstarInputOn_rest4NoF4_of_noSmall ggTriD4ThreeRankInput_holds (ggTwF4RankInput_of_three hF3)
    hT h

theorem ggStdSubPreInputOn_rest4NoF4_of_noSmall_three (hF3 : GGTwF4ThreeRankInput)
    (hT : GGTitsThreeRankInput) (h : GGStdSubPreInputOn GGTableBOtherRestNoSmall) :
    GGStdSubPreInputOn GGTableBOtherRest4NoF4 :=
  ggStdSubPreInputOn_rest4NoF4_of_noSmall ggTriD4ThreeRankInput_holds
    (ggTwF4RankInput_of_three hF3) hT h

end Inputs

end TableBExcSmallRanks

end CFSG.StandardType

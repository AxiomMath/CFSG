module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthDefs
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeSmall
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenOrth
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailFinal
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticOmega
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

namespace SmallOrth

theorem charP_two_of_card_pow {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) : CharP K 2 :=
  CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn hK

theorem conjunct_of_elt {p r : ℕ} {R : Type} [Group R] (hp : p.Prime)
    (hZ : Subgroup.center R = ⊥) (hZp : GGCenterPrime p R) (hlift : GGTorusLift p r R)
    (h : GGStdSubTwoTorusEltNormSmall p r R) :
    GGOutdiagOdd p R (LargeEvenInnSet R) ∧ ∃ r, GGTorusLift p r R ∧
      GGStdSubTwoTorusNormSmall p r R (LargeEvenInnSet R) ∧
        GGStdSubTwoTorusDeltaSmall p r R (LargeEvenInnSet R) :=
  ⟨ggOutdiagOdd_of_prime OrthRest.ggOutdiagPrime_inn, r, hlift,
    ggStdSubTwoTorusNormSmall_of_elt hp OrthRest.ggOutdiagPrime_inn hZ hZp h,
    ggStdSubTwoTorusDeltaSmall_of_delta
      (ggStdSubTwoTorusDelta_of_prime OrthRest.ggOutdiagPrime_inn hZp)⟩

section Labels


theorem largeEvenLabelAll_orthGood {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab)
    (h : DSplitLabel p lab ∨ DTwoLabel p lab ∨ TwDSplitLabel p lab ∨ TwDUnitLabel p lab)
    (h1 : PlusSplitInput) (h2 : PlusTwoInput) (h3 : MinusSplitInput) (h4 : MinusUnitInput) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧ ∃ r, GGTorusLift p r R ∧
      GGStdSubTwoTorusNormSmall p r R I ∧ GGStdSubTwoTorusDeltaSmall p r R I := by
  have hn1 : 1 ≤ lab.n := hlab.1
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hn1
  rcases h with ⟨ht, hl, hpn⟩ | ⟨ht, hl, hn, hp3⟩ | ⟨ht, hl, hpn⟩ | ⟨ht, hl, hpn, hnot⟩
  ·
    dsimp only at ht hl hpn
    subst ht
    have hp2 := ne_two_of_dvd_two_pow_sub_one' hn1 hpn
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢ with h3'
    · omega
    · obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
      have : CharP K 2 := charP_two_of_card_pow hn1 hK
      have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
      exact ⟨K, i1, i2, hK, hQ', conjunct_of_elt hp
        (TableBOrth.center_omegaPlus_eq_bot hp hp2 hpK (by omega))
        (CorFourTwoOpen.ggCenterPrime_omegaPlus hp hp2 (by omega))
        (TableBSymp.ggTorusLift_omegaPlus hp hp2 hpK (by omega))
        (h1 K n l p hK hl hp hpn)⟩
  ·
    dsimp only at ht hl hn
    subst ht hn hp3
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢ with h3'
    · omega
    · obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
      have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
      have : CharP K 2 := charP_two_of_card_pow hn1 hK
      have hcen := ggOrthRestCenterInput_holds.2 K l hK2 hl
      exact ⟨K, i1, i2, hK, hQ', conjunct_of_elt hp hcen.1 hcen.2
        (ggOrthRestTorusLiftInput_holds.2 K l hK2 hl) (h2 K l hK2 hl)⟩
  ·
    dsimp only at ht hl hpn
    subst ht
    have hp2 := ne_two_of_dvd_two_pow_sub_one' hn1 hpn
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢ with h2' h3'
    · omega
    · omega
    · obtain ⟨K, i1, i2, hK, b, c, hbc, hQ'⟩ := hQ
      have : CharP K 2 := charP_two_of_card_pow hn1 hK
      have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
      exact ⟨K, i1, i2, hK, b, c, hbc, hQ', conjunct_of_elt hp
        (TableBOrth.center_omegaMinus_eq_bot hp hp2 hpK (by omega) hbc)
        (CorFourTwoOpen.ggCenterPrime_omegaMinus hp hp2 (by omega) hbc)
        (TableBSymp.ggTorusLift_omegaMinus hp hp2 hpK (by omega) b c)
        (h3 K n (l - 1) p b c hK (by omega) hp hpn hbc)⟩
  ·
    dsimp only at ht hl hpn hnot
    subst ht
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢ with h2' h3'
    · omega
    · omega
    · obtain ⟨K, i1, i2, hK, b, c, hbc, hQ'⟩ := hQ
      have : CharP K 2 := charP_two_of_card_pow hn1 hK
      have hcen := ggOrthRestCenterInput_holds.1 K n (l - 1) p b c hK (by omega) hp hpn hbc
      exact ⟨K, i1, i2, hK, b, c, hbc, hQ', conjunct_of_elt hp hcen.1 hcen.2
        (ggOrthRestTorusLiftInput_holds.1 K n (l - 1) p b c hK (by omega) hp hpn hbc)
        (h4 K n (l - 1) p b c hK (by omega) hp hpn hbc (by omega))⟩

end Labels

end SmallOrth

section Assembly


open SmallOrth in
theorem ggStdSubSmallInputOn_orthGood_of_inputs (h1 : PlusSplitInput) (h2 : PlusTwoInput)
    (h3 : MinusSplitInput) (h4 : MinusUnitInput) :
    GGStdSubSmallInputOn fun p lab => DSplitLabel p lab ∨ DTwoLabel p lab ∨
      TwDSplitLabel p lab ∨ TwDUnitLabel p lab :=
  ggStdSubSmallInputOn_of_labels_normSmall ggLNoncyclicInput_holds fun _ _ hp hlab hS _ =>
    largeEvenLabelAll_orthGood hp hlab hS h1 h2 h3 h4

end Assembly

end CFSG.StandardType

end

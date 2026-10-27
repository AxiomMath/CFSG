module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrSmallRank
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8032
public import Certificates.Certificate8033
import CFSG.LocalAnalysis.StandardType.GGTableB
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineSmall
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineTwF4
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestG2
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallTits
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTwF4
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanksTwF4
import CFSG.LocalAnalysis.StandardType.GGTwF4SUThreeRank
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsOrder

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggInndiag_pRank_le_two_G2
    {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ StandardType.LargeEvenMarking X (fun lab R _ I _ _ => lab.tag = .G2 ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E) :=
  not_largeEvenMarking_of_labelAll_card_lt fun _ _ h =>
    (NbrInnerNine.largeEvenLabelAll_card_lt_G2_all hp hp2 h).mono fun _ _ _ _ h' _ _ => h'

theorem ggInndiag_pRank_le_two_G2der
    {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ StandardType.LargeEvenMarking X (fun lab R _ I _ _ => lab.tag = .G2der ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E) := by
  refine not_largeEvenMarking_of_labelAll_card_lt fun lab hlab ht =>
    LargeEvenLabelAll.mono (fun _ _ _ _ h' _ _ => h') ?_
  by_cases hp3 : p = 3
  · refine TableBExcSmallRest.largeEvenLabelAll_card_lt_G2der hp hlab ht
      (.inr (.inr (.inr ⟨?_, hp3⟩)))
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht hlab ⊢
    subst ht
    exact hlab.2.2
  · exact NbrInnerNine.largeEvenLabelAll_card_lt_G2der_ne_three hp hp2 hp3 ht

theorem ggInndiag_pRank_le_two_triD4
    {X : Type} [Group X] {p : ℕ} (hp : p.Prime) :
    ¬ StandardType.LargeEvenMarking X (fun lab R _ I _ _ =>
      (lab.tag = .triD4 ∧ (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)) ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E) := by
  refine not_largeEvenMarking_of_labelAll_card_lt fun lab hlab ⟨ht, hpq⟩ =>
    (NbrInnerNine.largeEvenLabelAll_card_lt_triD4_of hp hlab ht (.inr ?_)).mono
      fun _ _ _ _ h' _ _ => h'
  rw [pow_two, mul_self_tsub_one]
  rcases hpq with h | h
  · exact dvd_mul_of_dvd_right h _
  · exact dvd_mul_of_dvd_left h _

theorem ggInndiag_pRank_le_two_twB2 {X : Type} [Group X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ StandardType.LargeEvenMarking X (fun lab R _ I _ _ => lab.tag = .twB2 ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E) :=
  not_largeEvenMarking_of_labelAll_card_lt fun _ hlab h =>
    (NbrInnerNine.largeEvenLabelAll_card_lt_twB2_all hp hp2 hlab h).mono
      fun _ _ _ _ h' _ _ => h'

theorem ggInndiag_pRank_le_two_twF4
    {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ StandardType.LargeEvenMarking X (fun lab R _ I _ _ =>
      (lab.tag = .twF4 ∧ (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)) ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E) := by
  refine not_largeEvenMarking_of_labelAll_card_lt fun lab hlab ⟨ht, hpq⟩ =>
    LargeEvenLabelAll.mono (fun _ _ _ _ h' _ _ => h') ?_
  rcases hpq with h | h
  · exact NbrInnerNine.largeEvenLabelAll_card_lt_twF4_sub hp hp2 hlab ht h
  · exact TableBExcSmallRest.largeEvenLabelAll_card_lt_twF4
      (TableBExcSmallRanks.ggTwF4RankInput_of_three TwF4SUThree.ggTwF4ThreeRankInput_holds)
      hp hlab ht (.inr (.inl ⟨by rw [ht]; exact id, by rw [ht]; decide, h⟩))

theorem ggInndiag_pRank_le_two_twF4der
    {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ StandardType.LargeEvenMarking X (fun lab R _ I _ _ => lab.tag = .twF4der ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ 3 ≤ Nat.card E) := by
  refine not_largeEvenMarking_of_labelAll_card_lt fun lab hlab ht =>
    LargeEvenLabelAll.mono (fun _ _ _ _ h' _ _ => h') ?_
  by_cases hp3 : p = 3
  · refine TableBExcSmallRest.largeEvenLabelAll_card_lt_twF4der_holds hp hlab ht
      (.inr (.inr (.inr ⟨?_, hp3⟩)))
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht hlab ⊢
    subst ht
    exact hlab.2.2
  · exact NbrInnerNine.largeEvenLabelAll_card_lt_twF4der_ne_three hp hp2 hp3 hlab ht

end CFSG.StandardType

end

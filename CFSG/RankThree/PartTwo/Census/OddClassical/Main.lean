module

public import CFSG.RankThree.PartTwo.Census.Interface
public import CFSG.RankThree.PartTwo.Census.Suzuki
public import CFSG.RankThree.PartTwo.Census.OddClassical.LinearWitness
public import CFSG.RankThree.PartTwo.Census.OddClassical.LinearComponent
public import CFSG.RankThree.PartTwo.Census.OddClassical.LinearTwo
public import CFSG.RankThree.PartTwo.Census.OddClassical.SymplecticWitness
public import CFSG.RankThree.PartTwo.Census.OddClassical.SymplecticComponent
public import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryWitness
public import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryComponent
public import CFSG.RankThree.PartTwo.Census.OddClassical.SmallThree
public import CFSG.RankThree.PartTwo.Census.OddClassical.LinearFourThree
import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.SectionRank.SignLines
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.RankThreeEven TauCeti

@[expose] def LocalRankThreeU43 : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Nat.card F = 9 →
    localRank 3 (CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSU 4 3 F)) ≤ 2

theorem excluded433_twistedA_three_three (hU43 : LocalRankThreeU43) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA 3 q).Valid) (hq : q.p = 3) (hf : q.exponent = 1) :
    Excluded433 (.lie ⟨.twistedA 3 q, hv⟩) := by
  intro G _ _ hG e
  have hc : ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩ = 3 :=
    (LieTypeIndex.characteristic_twistedA 3 q).trans hq
  have he : ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩ = 1 :=
    (LieTypeIndex.fieldExponent_twistedA 3 q).trans hf
  have hK : Nat.card (GaloisField (ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩)
      (2 * ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩)) = 9 := by
    rw [GaloisField.card _ _ (by rw [he]; norm_num), hc, he]
    norm_num
  have hq3 : ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩ ^
      ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩ = 3 := by rw [hc, he]; rfl
  have e' := e.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 3 q hv)
  rw [hq3] at e'
  exact hG.false_of_localRank_three_le_two e' (hU43 _ hK)

theorem five_le_card_of_odd (q : PrimePower) (hq : q.p ≠ 2) (h3 : ¬ (q.p = 3 ∧ q.exponent = 1)) :
    5 ≤ q.card := by
  rw [PrimePower.card_def]
  have hp := q.prime_p
  have hp2 := hp.two_le
  have he := q.exponent_pos
  have hp4 : q.p ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
  by_cases hp3 : q.p = 3
  · have he2 : 2 ≤ q.exponent := by
      by_contra h
      exact h3 ⟨hp3, by omega⟩
    rw [hp3]
    calc 5 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) he2
  · calc 5 ≤ q.p := by omega
      _ = q.p ^ 1 := (pow_one _).symm
      _ ≤ q.p ^ q.exponent := Nat.pow_le_pow_right hp.pos he

theorem item433Case_A_odd (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.A r q).Valid) (hq : q.p ≠ 2) : Item433Case (.lie ⟨.A r q, hv⟩) := by
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hr : 1 ≤ r := hrange.1
  rcases (show r = 1 ∨ r = 2 ∨ r = 3 ∨ 4 ≤ r by omega) with rfl | rfl | rfl | hr4
  · exact (excluded433_A_one_odd q hv hq).item433Case
  · by_cases h3 : q.p = 3 ∧ q.exponent = 1
    · exact (excluded433_A_two_three q hv h3.1 h3.2).item433Case
    · exact (excluded433_A_two_odd q hv hq (five_le_card_of_odd q hq h3)).item433Case
  · by_cases h3 : q.p = 3 ∧ q.exponent = 1
    · exact (excluded433_A_three_three q hv h3.1 h3.2).item433Case
    · exact (excluded433_A_three_odd q hv hq (five_le_card_of_odd q hq h3)).item433Case
  · exact (excluded433_A_odd_of_four_le r q hv hq hr4).item433Case

theorem item433Case_twistedA_odd (hU43 : LocalRankThreeU43) (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) (hq : q.p ≠ 2) :
    Item433Case (.lie ⟨.twistedA r q, hv⟩) := by
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hr : 2 ≤ r := hrange.1
  rcases (show r = 2 ∨ r = 3 ∨ 4 ≤ r by omega) with rfl | rfl | hr4
  · by_cases h3 : q.p = 3 ∧ q.exponent = 1
    · exact (excluded433_twistedA_two_three q hv h3.1 h3.2).item433Case
    · exact (excluded433_twistedA_two_odd q hv hq (five_le_card_of_odd q hq h3)).item433Case
  · by_cases h3 : q.p = 3 ∧ q.exponent = 1
    · exact (excluded433_twistedA_three_three hU43 q hv h3.1 h3.2).item433Case
    · exact (excluded433_twistedA_three_odd_of_five_le q hv hq
        (five_le_card_of_odd q hq h3)).item433Case
  · exact (excluded433_twistedA_odd_of_four_le r q hv hq hr4).item433Case

theorem item433Case_B2_odd (q : PrimePower) (hv : (LieTypeIndex.B 2 q).Valid) (hq : q.p ≠ 2) :
    Item433Case (.lie ⟨.B 2 q, hv⟩) :=
  (excluded433_B2_odd q hv hq).item433Case

theorem item433Case_C (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.C r q).Valid) :
    Item433Case (.lie ⟨.C r q, hv⟩) :=
  (excluded433_C r q hv).item433Case

end CFSG.RankThree.PartTwo.Census

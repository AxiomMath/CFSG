module

public import CFSG.RankThree.PartTwo.Sec4.Census.Bridges
public import CFSG.RankThree.PartOne.Census3.Interface
public import CFSG.RankThree.PartTwo.Census.Assembly
import CFSG.RankThree.PartOne.Census3.LinearWitness
import CFSG.RankThree.PartTwo.Census.Classical.Bridges
import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness
import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryWitness
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne.Census3
open CFSG.RankThree.PartTwo.Census (typeAGroupEquivProjSL typeTwistedAGroupEquivProjSU
  BridgeSp6Four BridgeSp8Two BridgeOmega8PlusTwo BridgeOmega8MinusTwo)
open CFSG.Assembly.LowTwoRank TauCeti
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex
  primePowerTwo localRank)

variable {G : Type} [Group G] [Finite G]

theorem three_lt_of_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) : 3 < p := by
  have := hp.two_le
  rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 4 < p by omega) with h | h | h | h
  · exact absurd h hp2
  · exact absurd h hp3
  · exact absurd (h ▸ hp) (by norm_num)
  · omega

theorem SectionFourHyp.false_of_A2 (hG : SectionFourHyp G) {q : PrimePower}
    (hv : (LieTypeIndex.A 2 q).Valid) (hq : 3 < q.p) (hf : q.exponent = 3)
    (e : G ≃* (CFSGIndex.lie ⟨.A 2 q, hv⟩).Group) : False := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  refine SectionFourHyp.false_of_three_le_localRank hG
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)) q.prime_p hq ?_
  exact le_trans (by omega)
    (le_localRank_PSL_three (K := GaloisField q.p q.exponent) (by omega)
      (GaloisField.card _ _ q.exponent_pos.ne'))

theorem SectionFourHyp.false_of_twistedA2 (hG : SectionFourHyp G) {q : PrimePower}
    (hv : (LieTypeIndex.twistedA 2 q).Valid) (hq : 3 < q.p) (hf : q.exponent = 3)
    (e : G ≃* (CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group) : False := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hu := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField q.p q.exponent
    q.exponent_pos
  refine SectionFourHyp.false_of_three_le_localRank hG
    ((e.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 q hv)).trans
      (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hu (n := 2 + 1) (by norm_num)).symm)
    q.prime_p hq ?_
  exact le_trans (by rw [one_pow, mul_one]; omega)
    (CFSG.RankThree.PartTwo.Census.le_localRank_unitaryPSU hu (by omega) (n := 2 + 1) (r := 1)
      le_rfl (by norm_num))

theorem SectionFourHyp.false_of_A3_even (hG : SectionFourHyp G) {q : PrimePower}
    (hv : (LieTypeIndex.A 3 q).Valid) (hq : q.p = 2) (hf : 3 ≤ q.exponent)
    (e : G ≃* (CFSGIndex.lie ⟨.A 3 q, hv⟩).Group) : False := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hq
  obtain ⟨s, hs, hs5, hsd⟩ := CFSG.RankThree.PartTwo.Census.exists_prime_five_le_dvd_two_pow_sub_one
    hf
  have hU : Nat.card (GaloisField q.p q.exponent)ˣ = 2 ^ q.exponent - 1 := by
    rw [Nat.card_units, GaloisField.card _ _ q.exponent_pos.ne', hq]
  refine SectionFourHyp.false_of_three_le_localRank hG
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 3 q hv)) hs (by omega) ?_
  refine CFSG.RankThree.PartTwo.Census.le_localRank_PSL_torus (m := 3) hs (by rw [hU]; exact hsd)
    (by norm_num) (by norm_num) (Or.inr fun h4 => ?_)
  have := Nat.le_of_dvd (by norm_num) h4
  omega

theorem SectionFourHyp.false_of_twistedA4_even (hG : SectionFourHyp G) {q : PrimePower}
    (hv : (LieTypeIndex.twistedA 4 q).Valid) (hq : q.p = 2) (hf : 4 ≤ q.exponent)
    (e : G ≃* (CFSGIndex.lie ⟨.twistedA 4 q, hv⟩).Group) : False := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : CharP (GaloisField q.p (2 * q.exponent)) 2 := CharP.congr q.p hq
  have hu := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField q.p q.exponent
    q.exponent_pos
  obtain ⟨s, hs, hs7, hsd⟩ :=
    CFSG.RankThree.PartTwo.Census.exists_prime_seven_le_dvd_two_pow_add_one hf
  refine SectionFourHyp.false_of_three_le_localRank hG
    (e.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 4 q hv)) hs (by omega)
    ?_
  refine CFSG.RankThree.PartTwo.Census.le_localRank_statedSU_torus (k := 2) hu hs
    (by rw [hq]; exact hsd) (by norm_num) (Or.inr fun h5 => ?_)
  have := Nat.le_of_dvd (by norm_num) h5
  omega

omit [Finite G] in
theorem list42_of_item1 (h : ThmThreeItem1 G) : List42 G := by
  obtain ⟨q, hq, -, hv, ⟨e⟩⟩ := h
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  exact List42.one q.p q.exponent hq q.exponent_pos (e.trans (typeAGroupEquivProjSL 1 q hv))

theorem list42_of_item2 (hG : SectionFourHyp G) (h : ThmThreeItem2 G) : List42 G := by
  obtain ⟨q, hq, hf3, h⟩ := h
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hf1 := q.exponent_pos
  by_cases hp3 : q.p = 3
  · obtain ⟨p, f, hp, hf⟩ := q
    obtain rfl : p = 3 := hp3
    rcases h with ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩
    · exact List42.nine_SL3 hf hf3 (e.trans (typeAGroupEquivProjSL 2 _ hv))
    · exact List42.nine_SU3 hf hf3 (e.trans (typeTwistedAGroupEquivProjSU 2 _ hv))
  have hp5 := three_lt_of_prime q.prime_p hq hp3
  by_cases hf2 : q.exponent ≤ 2
  · rcases h with ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩
    · exact List42.two_SL q.p q.exponent hp5 hf1 hf2 (e.trans (typeAGroupEquivProjSL 2 q hv))
    · exact List42.two_SU q.p q.exponent hp5 hf1 hf2
        (e.trans (typeTwistedAGroupEquivProjSU 2 q hv))
  · exfalso
    rcases h with ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩
    · exact SectionFourHyp.false_of_A2 hG hv hp5 (by omega) e
    · exact SectionFourHyp.false_of_twistedA2 hG hv hp5 (by omega) e

omit [Finite G] in
theorem list42_of_item3 (h : ThmThreeItem3 G) : List42 G := by
  obtain ⟨hv, ⟨e⟩⟩ := h
  exact List42.three hv e

omit [Finite G] in
theorem list42_of_item4 (h : ThmThreeItem4 G) : List42 G := by
  obtain ⟨q, hq, hf, h⟩ := h
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  by_cases hp3 : q.p = 3
  · obtain ⟨p, f, hp, hf'⟩ := q
    obtain rfl : p = 3 := hp3
    obtain rfl : f = 1 := hf
    rcases h with ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩
    · exact List42.nine_G23 e
    · exact absurd ((LieTypeIndex.isDuplicateRepresentative_iff
        (LieTypeIndex.B 2 ⟨3, 1, hp, hf'⟩)).mpr ⟨rfl, rfl⟩) hv.2
    · exact List42.nine_SU43 (e.trans (typeTwistedAGroupEquivProjSU 3 _ hv))
    · exact List42.nine_SL43 (e.trans (typeAGroupEquivProjSL 3 _ hv))
  have hp5 := three_lt_of_prime q.prime_p hq hp3
  rcases h with ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩
  · exact List42.four_G2 hp5 hf hv e
  · obtain ⟨p, f, hp, hf'⟩ := q
    obtain rfl : f = 1 := hf
    exact List42.four_Sp p hp5 (e.trans (typeB2GroupEquivProjSp _ hv))
  · obtain ⟨p, f, hp, hf'⟩ := q
    obtain rfl : f = 1 := hf
    exact List42.four_SU p hp5 (e.trans (typeTwistedAGroupEquivProjSU 3 _ hv))
  · obtain ⟨p, f, hp, hf'⟩ := q
    obtain rfl : f = 1 := hf
    exact List42.four_SL p hp5 (e.trans (typeAGroupEquivProjSL 3 _ hv))

omit [Finite G] in
theorem list42_of_item5 (h : ThmThreeItem5 G) : List42 G := by
  obtain ⟨n, hn5, hn, ⟨e⟩⟩ := h
  exact List42.five hn5 hn e

omit [Finite G] in
theorem list42_of_item6 (h : ThmThreeItem6 G) : List42 G := by
  obtain ⟨s, hs, ⟨e⟩⟩ := h
  exact List42.six (by simpa [sporadicsThm3, sporadics42] using hs) e

theorem list42_of_item7 (hG : SectionFourHyp G) (h : ThmThreeItem7 G) : List42 G := by
  rcases h with ⟨q, hq, hv, ⟨e⟩⟩ | ⟨m, hv, ⟨e⟩⟩ | ⟨q, hq, h⟩ | ⟨m, hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩
  · obtain ⟨p, f, hp, hf⟩ := q
    obtain rfl : p = 2 := hq
    refine List42.seven (Or.inl ⟨f, hf, Or.inl ⟨e.trans (typeAGroupEquivProjSL 1 _ hv)⟩⟩)
  · exact List42.seven (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hv, ⟨e⟩⟩))))
  · obtain ⟨p, f, hp, hf⟩ := q
    obtain rfl : p = 2 := hq
    rcases h with ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩ |
      ⟨hv, ⟨e⟩⟩
    · exact List42.seven (Or.inl ⟨f, hf, Or.inr (Or.inr (Or.inl
        ⟨e.trans (typeTwistedAGroupEquivProjSU 2 _ hv)⟩))⟩)
    · exact List42.seven (Or.inl ⟨f, hf, Or.inr (Or.inl
        ⟨e.trans (typeAGroupEquivProjSL 2 _ hv)⟩)⟩)
    · exact List42.seven (Or.inl ⟨f, hf, Or.inr (Or.inr (Or.inr (Or.inl
        ⟨e.trans (typeB2GroupEquivProjSp _ hv)⟩)))⟩)
    · exact List42.seven (Or.inr (Or.inl ⟨_, rfl, hv, ⟨e⟩⟩))
    · exact List42.seven (Or.inl ⟨f, hf, Or.inr (Or.inr (Or.inr (Or.inr
        ⟨e.trans (typeTwistedAGroupEquivProjSU 3 _ hv)⟩)))⟩)
    ·
      rcases (show f = 1 ∨ f = 2 ∨ f = 3 ∨ 4 ≤ f by omega) with rfl | rfl | rfl | hf4
      · exact List42.eight_SU52 (e.trans (typeTwistedAGroupEquivProjSU 4 _ hv))
      · exact List42.eight_SU54 (e.trans (typeTwistedAGroupEquivProjSU 4 _ hv))
      · exact List42.eight_SU58 (e.trans (typeTwistedAGroupEquivProjSU 4 _ hv))
      · exact (SectionFourHyp.false_of_twistedA4_even hG hv rfl hf4 e).elim
    · exact List42.seven (Or.inr (Or.inr (Or.inl ⟨_, hv, rfl, ⟨e⟩⟩)))
  · exact List42.seven (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hv, ⟨e⟩⟩)))))
  · exact List42.seven (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hv, ⟨e⟩⟩)))))

theorem list42_of_item8 (hG : SectionFourHyp G) (hSp6 : BridgeSp6Two) (hSp64 : BridgeSp6Four)
    (hOm : BridgeOmega8MinusTwo) (hlarge : SpinLargePrimeRankThree) (h : ThmThreeItem8 G) :
    List42 G := by
  obtain ⟨q, hq, h⟩ := h
  have hf1 := q.exponent_pos
  rcases h with ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩
  ·
    rcases (show q.exponent = 1 ∨ q.exponent = 2 ∨ 3 ≤ q.exponent by omega) with hf | hf | hf3
    · exact absurd ((LieTypeIndex.isDuplicateRepresentative_iff _).mpr
        (Or.inr (Or.inr ⟨rfl, by simp [PrimePower.card_def, hq, hf]⟩))) hv.2
    · obtain ⟨p, f, hp, hf'⟩ := q
      obtain rfl : p = 2 := hq
      obtain rfl : f = 2 := hf
      exact List42.eight_SL44 (e.trans (typeAGroupEquivProjSL 3 _ hv))
    · exact (SectionFourHyp.false_of_A3_even hG hv hq hf3 e).elim
  ·
    rcases (show q.exponent = 1 ∨ q.exponent = 2 ∨ 3 ≤ q.exponent by omega) with hf | hf | hf3
    · obtain ⟨b⟩ := hSp6 q hv hq hf
      exact List42.eight_Sp62 (e.trans b)
    · obtain ⟨b⟩ := hSp64 q hv hq hf
      exact List42.eight_Sp64 (e.trans b)
    · exfalso
      have : Finite (CFSGIndex.lie ⟨.B 3 q, hv⟩).Group := Finite.of_equiv G e.toEquiv
      obtain ⟨r, hr, hr3, hrk⟩ := hlarge.typeB3 q hv hq hf3
      exact SectionFourHyp.false_of_three_le_localRank hG e hr hr3 hrk
  ·
    rcases (show q.exponent = 1 ∨ 2 ≤ q.exponent by omega) with hf | hf2
    · obtain ⟨b, c, hbc, ⟨f⟩⟩ := hOm q hv hq hf
      exact List42.eight_OmegaMinus hbc (e.trans f)
    · exfalso
      have : Finite (CFSGIndex.lie ⟨.twistedD 4 q, hv⟩).Group := Finite.of_equiv G e.toEquiv
      obtain ⟨r, hr, hr3, hrk⟩ := hlarge.twistedD4 q hv hq hf2
      exact SectionFourHyp.false_of_three_le_localRank hG e hr hr3 hrk

omit [Finite G] in
theorem list42_of_item9 (hSp8 : BridgeSp8Two) (hOp : BridgeOmega8PlusTwo) (h : ThmThreeItem9 G) :
    List42 G := by
  obtain ⟨q, hq, hf, h⟩ := h
  rcases h with ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩ |
    ⟨hv, ⟨e⟩⟩
  · obtain ⟨p, f, hp, hf'⟩ := q
    obtain rfl : p = 2 := hq
    obtain rfl : f = 1 := hf
    exact List42.eight_SL52 (e.trans (typeAGroupEquivProjSL 4 _ hv))
  · obtain ⟨p, f, hp, hf'⟩ := q
    obtain rfl : p = 2 := hq
    obtain rfl : f = 1 := hf
    exact List42.eight_SL62 (e.trans (typeAGroupEquivProjSL 5 _ hv))
  · obtain ⟨p, f, hp, hf'⟩ := q
    obtain rfl : p = 2 := hq
    obtain rfl : f = 1 := hf
    exact List42.eight_SL72 (e.trans (typeAGroupEquivProjSL 6 _ hv))
  · obtain ⟨p, f, hp, hf'⟩ := q
    obtain rfl : p = 2 := hq
    obtain rfl : f = 1 := hf
    exact List42.eight_SU62 (e.trans (typeTwistedAGroupEquivProjSU 5 _ hv))
  · obtain ⟨b⟩ := hSp8 q hv hq hf
    exact List42.eight_Sp82 (e.trans b)
  · obtain ⟨b⟩ := hOp q hv hq hf
    exact List42.eight_OmegaPlus (e.trans b)
  · obtain rfl : q = primePowerTwo := PrimePower.ext hq hf
    exact List42.eight_F42 e

theorem list42_of_theoremThreeList (hG : SectionFourHyp G) (hSp6 : BridgeSp6Two)
    (hSp64 : BridgeSp6Four) (hSp8 : BridgeSp8Two) (hOp : BridgeOmega8PlusTwo)
    (hOm : BridgeOmega8MinusTwo) (hlarge : SpinLargePrimeRankThree) (h : TheoremThreeList G) :
    List42 G := by
  rcases h with h | h | h | h | h | h | h | h | h
  · exact list42_of_item1 h
  · exact list42_of_item2 hG h
  · exact list42_of_item3 h
  · exact list42_of_item4 h
  · exact list42_of_item5 h
  · exact list42_of_item6 h
  · exact list42_of_item7 hG h
  · exact list42_of_item8 hG hSp6 hSp64 hOm hlarge h
  · exact list42_of_item9 hSp8 hOp h

end CFSG.RankThree.PartTwo.Sec4.Census

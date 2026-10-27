module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LH2
public import CFSG.RankThree.PartTwo.Sec14.Ronan148SH2Assembly
import CFSG.RankThree.PartTwo.Sec4.Item419ThetaProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4.Ronan148S CFSG.RankThree.PartTwo.Sec14.Ronan148S
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)
open TauCeti (PrimePower LieTypeIndex ValidLieTypeIndex)

theorem rowOfH2_projSL (r p e : ℕ) [Fact p.Prime] (he : 1 ≤ e)
    (hv : (LieTypeIndex.A r ⟨p, e, Fact.out, he⟩).Valid) :
    RowOfH2 (projSL (r + 1) (GaloisField p e)) :=
  rowOfH2_of_lie ⟨_, hv⟩ ⟨(Census.typeAGroupEquivProjSL r ⟨p, e, Fact.out, he⟩ hv).symm⟩

theorem rowOfH2_projSU (r p e : ℕ) [Fact p.Prime] (he : 1 ≤ e)
    (hv : (LieTypeIndex.twistedA r ⟨p, e, Fact.out, he⟩).Valid) :
    RowOfH2 (projSU (r + 1) p e) :=
  rowOfH2_of_lie ⟨_, hv⟩ ⟨(Census.typeTwistedAGroupEquivProjSU r ⟨p, e, Fact.out, he⟩ hv).symm⟩

theorem rowOfH2_projSp_two (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e)
    (hv : (LieTypeIndex.B 2 ⟨p, e, Fact.out, he⟩).Valid) :
    RowOfH2 (projSp 2 (GaloisField p e)) :=
  rowOfH2_of_lie ⟨_, hv⟩ ⟨(Sec4.Census.typeB2GroupEquivProjSp ⟨p, e, Fact.out, he⟩ hv).symm⟩

theorem kH2_two_SL (p e : ℕ) [Fact p.Prime] (hp : 3 < p) (he : 1 ≤ e) (_ : e ≤ 2) :
    RowOfH2 (projSL 3 (GaloisField p e)) :=
  rowOfH2_projSL 2 p e he (valid_A (by norm_num) (fun h => absurd h (by norm_num)) fun _ => by
    simp only [TauCeti.PrimePower.card_def]
    have := five_le_pow hp Fact.out he
    omega)

theorem kH2_two_SU (p e : ℕ) [Fact p.Prime] (hp : 3 < p) (he : 1 ≤ e) (_ : e ≤ 2) :
    RowOfH2 (projSU 3 p e) :=
  rowOfH2_projSU 2 p e he (valid_twistedA le_rfl fun _ => by
    simp only [TauCeti.PrimePower.card_def]
    have := five_le_pow hp Fact.out he
    omega)

theorem kH2_four_G2 (p : ℕ) [Fact p.Prime] (_ : 3 < p) (q : PrimePower) (_ : q.p = p)
    (_ : q.exponent = 1) (hq : (LieTypeIndex.G2 q).Valid) :
    RowOfH2 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group :=
  rowOfH2_of_lie ⟨_, hq⟩ ⟨MulEquiv.refl _⟩

theorem kH2_four_Sp (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    RowOfH2 (projSp 2 (GaloisField p 1)) :=
  rowOfH2_projSp_two p 1 le_rfl
    (valid_B_two (by simp only [TauCeti.PrimePower.card_def, pow_one]; omega)
      (by simp only [TauCeti.PrimePower.card_def, pow_one]; omega))

theorem kH2_four_SL (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    RowOfH2 (projSL 4 (GaloisField p 1)) :=
  rowOfH2_projSL 3 p 1 le_rfl (valid_A (by norm_num) (fun h => absurd h (by norm_num)) fun _ => by
    simp only [TauCeti.PrimePower.card_def]
    rw [pow_one]
    omega)

theorem kH2_four_SU (p : ℕ) [Fact p.Prime] (_ : 3 < p) :
    RowOfH2 (projSU 4 p 1) :=
  rowOfH2_projSU 3 p 1 le_rfl (valid_twistedA (by norm_num) (by omega))

theorem kH2_seven_SL3 (n : ℕ) (hn : 1 ≤ n) : RowOfH2 (projSL 3 (GaloisField 2 n)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    exact rowOfH2_of_noCQ (NoCQOf.of_not_dvd (by rw [card_projSL_three_two]; norm_num))
  · exact rowOfH2_projSL 2 2 n hn
      (valid_A (by norm_num) (fun h => absurd h (by norm_num)) fun _ => by
        simp only [TauCeti.PrimePower.card_def]
        have := four_le_two_pow h
        omega)

theorem kH2_seven_SU3 (n : ℕ) (hn : 1 ≤ n) : RowOfH2 (projSU 3 2 n) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    exact rowOfH2_of_noCQ (NoCQOf.of_not_dvd
      (by rw [Sec4.Item419ThetaProof.card_projSU_three_two_one]; norm_num))
  · exact rowOfH2_projSU 2 2 n hn (valid_twistedA le_rfl fun _ => by
      simp only [TauCeti.PrimePower.card_def]
      have := four_le_two_pow h
      omega)

theorem kH2_seven_Sp4 (n : ℕ) (hn : 1 ≤ n) : RowOfH2 (projSp 2 (GaloisField 2 n)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    exact rowOfH2_of_noCQ (NoCQOf.of_not_dvd
      (by rw [CFSG.PGLModel.card_projSp_two_two]; norm_num))
  · have := four_le_two_pow h
    exact rowOfH2_projSp_two 2 n hn
      (valid_B_two (by simp only [TauCeti.PrimePower.card_def]; omega)
        (by simp only [TauCeti.PrimePower.card_def]; omega))

theorem kH2_seven_SU4 (n : ℕ) (hn : 1 ≤ n) : RowOfH2 (projSU 4 2 n) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact rowOfH2_projSU 3 2 n hn (valid_twistedA (by norm_num) (by omega))

theorem kH2_seven_G2 (q : PrimePower) (_ : q.p = 2) (hq : (LieTypeIndex.G2 q).Valid) :
    RowOfH2 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group :=
  rowOfH2_of_lie ⟨_, hq⟩ ⟨MulEquiv.refl _⟩

theorem kH2_seven_D4 (q : PrimePower) (hq : (LieTypeIndex.trialityD4 q).Valid) (_ : q.p = 2) :
    RowOfH2 (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group :=
  rowOfH2_of_lie ⟨_, hq⟩ ⟨MulEquiv.refl _⟩

theorem kH2_seven_F4 (m : ℕ) (hm : (LieTypeIndex.reeF4 m).Valid) :
    RowOfH2 (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group :=
  rowOfH2_of_lie ⟨_, hm⟩ ⟨MulEquiv.refl _⟩

theorem kH2_seven_Tits (ht : LieTypeIndex.tits.Valid) :
    RowOfH2 (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group :=
  rowOfH2_of_lie ⟨_, ht⟩ ⟨MulEquiv.refl _⟩

theorem kH2_eight_SU5 : RowOfH2 (projSU 5 2 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact rowOfH2_projSU 4 2 1 le_rfl (valid_twistedA (by norm_num) (by omega))

theorem kH2_eight_SL6 : RowOfH2 (projSL 6 (GaloisField 2 1)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact rowOfH2_projSL 5 2 1 le_rfl
    (valid_A (by norm_num) (fun h => absurd h (by norm_num)) (by omega))

theorem kH2_eight_SU6 : RowOfH2 (projSU 6 2 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact rowOfH2_projSU 5 2 1 le_rfl (valid_twistedA (by norm_num) (by omega))

theorem kH2_eight_SL7 : RowOfH2 (projSL 7 (GaloisField 2 1)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact rowOfH2_projSL 6 2 1 le_rfl
    (valid_A (by norm_num) (fun h => absurd h (by norm_num)) (by omega))

theorem kH2_eight_Sp6 : RowOfH2 (projSp 3 (GaloisField 2 1)) := by
  obtain ⟨e⟩ := Census.bridgeSp6Two _ (valid_B_of_three_le le_rfl le_rfl) rfl rfl
  exact rowOfH2_of_lie _ ⟨e.symm⟩

theorem kH2_eight_Sp8 : RowOfH2 (projSp 4 (GaloisField 2 1)) := by
  obtain ⟨e⟩ := Census.bridgeSp8Two _ (valid_B_of_three_le (by norm_num) le_rfl) rfl rfl
  exact rowOfH2_of_lie _ ⟨e.symm⟩

theorem kH2_eight_OmegaPlus : RowOfH2 (projOmegaPlus 4 (GaloisField 2 1)) := by
  have hv : (LieTypeIndex.D 4 ⟨2, 1, Nat.prime_two, Nat.one_pos⟩).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨le_rfl, id⟩
  obtain ⟨e⟩ := Census.bridgeOmega8PlusTwo _ hv rfl rfl
  exact rowOfH2_of_lie _ ⟨e.symm⟩

theorem kH2_eight_OmegaMinus (b c : GaloisField 2 1)
    (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) :
    RowOfH2 (projOmegaMinus 3 (GaloisField 2 1) b c) := by
  have hv : (LieTypeIndex.twistedD 4 ⟨2, 1, Nat.prime_two, Nat.one_pos⟩).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨le_rfl, id⟩
  obtain ⟨b', c', hbc', ⟨e⟩⟩ := Census.bridgeOmega8MinusTwo _ hv rfl rfl
  obtain ⟨rfl, rfl⟩ := eq_one_one_of_irreducible hbc
  obtain ⟨rfl, rfl⟩ := eq_one_one_of_irreducible hbc'
  exact rowOfH2_of_lie _ ⟨e.symm⟩

theorem kH2_eight_SL4 : RowOfH2 (projSL 4 (GaloisField 2 2)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact rowOfH2_projSL 3 2 2 (by norm_num)
    (valid_A (by norm_num) (fun h => absurd h (by norm_num)) fun _ => by
    simp only [TauCeti.PrimePower.card_def]
    norm_num)

theorem kH2_eight_Sp6_4 : RowOfH2 (projSp 3 (GaloisField 2 2)) := by
  obtain ⟨e⟩ := Census.bridgeSp6Four _ (valid_B_of_three_le le_rfl (by norm_num)) rfl rfl
  exact rowOfH2_of_lie _ ⟨e.symm⟩

theorem kH2_eight_SU5_8 : RowOfH2 (projSU 5 2 3) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact rowOfH2_projSU 4 2 3 (by norm_num) (valid_twistedA (by norm_num) (by omega))

theorem kH2_eight_F4 : RowOfH2 (TauCeti.CFSGIndex.lie f4TwoIndex).Group :=
  rowOfH2_of_lie f4TwoIndex ⟨MulEquiv.refl _⟩

theorem kH2_nine_SL3_nine : RowOfH2 (projSL 3 (GaloisField 3 2)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact rowOfH2_projSL 2 3 2 (by norm_num)
    (valid_A (by norm_num) (fun h => absurd h (by norm_num)) fun _ => by
    simp only [TauCeti.PrimePower.card_def]
    norm_num)

theorem kH2_nine_SU3_nine : RowOfH2 (projSU 3 3 2) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact rowOfH2_projSU 2 3 2 (by norm_num) (valid_twistedA le_rfl fun _ => by
    simp only [TauCeti.PrimePower.card_def]
    norm_num)

theorem kH2_nine_SL4 : RowOfH2 (projSL 4 (GaloisField 3 1)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact rowOfH2_projSL 3 3 1 le_rfl
    (valid_A (by norm_num) (fun h => absurd h (by norm_num)) fun _ => by
    simp only [TauCeti.PrimePower.card_def]
    norm_num)

theorem kH2OpenRows_of_six (h : ∀ s ∈ sporadicsOpenH2, RowOfH2 (Sec4.Spor s)) :
    KH2OpenRows where
  two_SL := kH2_two_SL
  two_SU := kH2_two_SU
  four_G2 := kH2_four_G2
  four_Sp := kH2_four_Sp
  four_SL := kH2_four_SL
  four_SU := kH2_four_SU
  six_open := h
  seven_SL3 := kH2_seven_SL3
  seven_SU3 := kH2_seven_SU3
  seven_Sp4 := kH2_seven_Sp4
  seven_SU4 := kH2_seven_SU4
  seven_G2 := kH2_seven_G2
  seven_D4 := kH2_seven_D4
  seven_F4 := kH2_seven_F4
  seven_Tits := kH2_seven_Tits
  eight_SU5 := kH2_eight_SU5
  eight_SL6 := kH2_eight_SL6
  eight_SU6 := kH2_eight_SU6
  eight_SL7 := kH2_eight_SL7
  eight_Sp6 := kH2_eight_Sp6
  eight_Sp8 := kH2_eight_Sp8
  eight_OmegaPlus := kH2_eight_OmegaPlus
  eight_OmegaMinus := kH2_eight_OmegaMinus
  eight_SL4 := kH2_eight_SL4
  eight_Sp6_4 := kH2_eight_Sp6_4
  eight_SU5_8 := kH2_eight_SU5_8
  eight_F4 := kH2_eight_F4
  nine_SL3_nine := kH2_nine_SL3_nine
  nine_SU3_nine := kH2_nine_SU3_nine
  nine_SL4 := kH2_nine_SL4

end CFSG.RankThree.PartTwo.Sec4.Ronan148L

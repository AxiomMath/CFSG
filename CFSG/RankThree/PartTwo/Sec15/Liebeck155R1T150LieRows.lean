module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150Lie
import CFSG.RankThree.PartTwo.Sec4.Ronan148LValid
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
import CFSG.RankThree.PartTwo.Sec8.Hering418Seven
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150

open CFSG CFSG.RankThree.PartTwo
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.RankThree.PartTwo.Sec4.Ronan148L (valid_A valid_twistedA valid_B_two
  valid_B_of_three_le five_le_pow four_le_two_pow card_projSL_three_two eq_one_one_of_irreducible)
open CFSG.RankThree.PartTwo.Census (typeAGroupEquivProjSL typeTwistedAGroupEquivProjSU
  bridgeSp6Two bridgeSp8Two bridgeSp6Four bridgeOmega8PlusTwo bridgeOmega8MinusTwo)
open CFSG.RankThree.PartTwo.Sec4.Census (typeB2GroupEquivProjSp)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex
  primePowerTwo)
open TauCeti (PrimePower LieTypeIndex ValidLieTypeIndex)

theorem k150_rowAll_of_card_le {J : Type} [Group J] (hF : K150Facts J) {X : Type} [Group X]
    (hX : 0 < Nat.card X) (hle : Nat.card X ≤ 720) : RowAllOfK150 J X :=
  k150_rowAll_of_not_dvd fun hd => by
    have := Nat.le_of_dvd hX hd
    have := hF.card_gt
    omega

variable {J : Type} [Group J] (hF : K150Facts J) (hLSC : LieSemisimpleCent)
  (hLC : LieComp.LieComp)

include hF hLSC hLC

private theorem k150_projSL (r p e : ℕ) [Fact p.Prime] (he : 1 ≤ e) (hp3 : p ≠ 3)
    (hv : (LieTypeIndex.A r ⟨p, e, Fact.out, he⟩).Valid) :
    RowAllOfK150 J (projSL (r + 1) (GaloisField p e)) :=
  k150_rowAll_of_lie hF hLSC hLC ⟨_, hv⟩ (by simpa using hp3)
    ⟨(typeAGroupEquivProjSL r ⟨p, e, Fact.out, he⟩ hv).symm⟩

private theorem k150_projSU (r p e : ℕ) [Fact p.Prime] (he : 1 ≤ e) (hp3 : p ≠ 3)
    (hv : (LieTypeIndex.twistedA r ⟨p, e, Fact.out, he⟩).Valid) :
    RowAllOfK150 J (projSU (r + 1) p e) :=
  k150_rowAll_of_lie hF hLSC hLC ⟨_, hv⟩ (by simpa using hp3)
    ⟨(typeTwistedAGroupEquivProjSU r ⟨p, e, Fact.out, he⟩ hv).symm⟩

private theorem k150_projSp_two (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e) (hp3 : p ≠ 3)
    (hv : (LieTypeIndex.B 2 ⟨p, e, Fact.out, he⟩).Valid) :
    RowAllOfK150 J (projSp 2 (GaloisField p e)) :=
  k150_rowAll_of_lie hF hLSC hLC ⟨_, hv⟩ (by simpa using hp3)
    ⟨(typeB2GroupEquivProjSp ⟨p, e, Fact.out, he⟩ hv).symm⟩

theorem k150_one_of_ne_three (p e : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e) (hp3 : p ≠ 3) :
    RowAllOfK150 J (projSL 2 (GaloisField p e)) := by
  have hp : p.Prime := Fact.out
  have h6 : p ≠ 6 := fun h => absurd (h ▸ hp) (by decide)
  have h4 : p ≠ 4 := fun h => absurd (h ▸ hp) (by decide)
  have h5 : 5 ≤ p := by
    have := hp.two_le
    omega
  by_cases h51 : p = 5 ∧ e = 1
  · obtain ⟨rfl, rfl⟩ := h51
    refine k150_rowAll_of_not_dvd fun hd => ?_
    have h2 := Nat.le_of_dvd (by norm_num)
      (hd.trans (Sec8.Hering418.card_projSL_two_dvd 5 1 le_rfl))
    have := hF.card_gt
    norm_num at h2
    omega
  · have hq : 7 ≤ p ^ e := by
      rcases eq_or_ne p 5 with rfl | h5'
      · have he2 : 2 ≤ e := by omega
        calc 7 ≤ 5 ^ 2 := by norm_num
          _ ≤ 5 ^ e := Nat.pow_le_pow_right (by norm_num) he2
      · exact (show 7 ≤ p by omega).trans (Nat.le_self_pow (by omega) p)
    have h9 : p ^ e ≠ 9 := by
      intro h
      have hdvd : p ∣ 3 ^ 2 := by
        rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← h]
        exact dvd_pow_self p (by omega)
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow hdvd))
    exact k150_projSL hF hLSC hLC 1 p e he hp3
      (valid_A le_rfl (fun _ => by
        simp only [TauCeti.PrimePower.card_def]
        omega) (fun h => absurd h (by omega)))

theorem k150_two_SL (p e : ℕ) [Fact p.Prime] (hp : 3 < p) (he : 1 ≤ e) (_ : e ≤ 2) :
    RowAllOfK150 J (projSL 3 (GaloisField p e)) :=
  k150_projSL hF hLSC hLC 2 p e he (by omega)
    (valid_A (by norm_num) (fun h => absurd h (by norm_num)) fun _ => by
      simp only [TauCeti.PrimePower.card_def]
      have := five_le_pow hp Fact.out he
      omega)

theorem k150_two_SU (p e : ℕ) [Fact p.Prime] (hp : 3 < p) (he : 1 ≤ e) (_ : e ≤ 2) :
    RowAllOfK150 J (projSU 3 p e) :=
  k150_projSU hF hLSC hLC 2 p e he (by omega)
    (valid_twistedA le_rfl fun _ => by
      simp only [TauCeti.PrimePower.card_def]
      have := five_le_pow hp Fact.out he
      omega)

theorem k150_four_G2 (p : ℕ) [Fact p.Prime] (hp : 3 < p) (q : PrimePower) (hqp : q.p = p)
    (_ : q.exponent = 1) (hq : (LieTypeIndex.G2 q).Valid) :
    RowAllOfK150 J (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group :=
  k150_rowAll_of_lie hF hLSC hLC ⟨_, hq⟩ (by simp; omega) ⟨MulEquiv.refl _⟩

theorem k150_four_Sp (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    RowAllOfK150 J (projSp 2 (GaloisField p 1)) :=
  k150_projSp_two hF hLSC hLC p 1 le_rfl (by omega)
    (valid_B_two (by simp only [TauCeti.PrimePower.card_def, pow_one]; omega)
      (by simp only [TauCeti.PrimePower.card_def, pow_one]; omega))

theorem k150_four_SL (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    RowAllOfK150 J (projSL 4 (GaloisField p 1)) :=
  k150_projSL hF hLSC hLC 3 p 1 le_rfl (by omega)
    (valid_A (by norm_num) (fun h => absurd h (by norm_num)) fun _ => by
      simp only [TauCeti.PrimePower.card_def]
      rw [pow_one]
      omega)

theorem k150_four_SU (p : ℕ) [Fact p.Prime] (hp : 3 < p) : RowAllOfK150 J (projSU 4 p 1) :=
  k150_projSU hF hLSC hLC 3 p 1 le_rfl (by omega)
    (valid_twistedA (by norm_num) (by omega))

theorem k150_seven_SL2 (n : ℕ) (hn : 1 ≤ n) : RowAllOfK150 J (projSL 2 (GaloisField 2 n)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.lt_or_ge n 3 with h | h
  · refine k150_rowAll_of_not_dvd fun hd => ?_
    have h2 := Nat.le_of_dvd (by interval_cases n <;> norm_num)
      (hd.trans (Sec8.Hering418.card_projSL_two_dvd 2 n hn))
    have := hF.card_gt
    interval_cases n <;> norm_num at h2 <;> omega
  · have h8 : 8 ≤ 2 ^ n :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    have h9 : 2 ^ n ≠ 9 := by
      intro h9
      have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
      rw [h9] at h2
      omega
    exact k150_projSL hF hLSC hLC 1 2 n hn (by norm_num)
      (valid_A le_rfl (fun _ => by
        simp only [TauCeti.PrimePower.card_def]
        omega) (fun h => absurd h (by omega)))

theorem k150_seven_SL3 (n : ℕ) (hn : 1 ≤ n) : RowAllOfK150 J (projSL 3 (GaloisField 2 n)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    exact k150_rowAll_of_card_le hF (by rw [card_projSL_three_two]; norm_num)
      (by rw [card_projSL_three_two]; norm_num)
  · exact k150_projSL hF hLSC hLC 2 2 n hn (by norm_num)
      (valid_A (by norm_num) (fun h => absurd h (by norm_num)) fun _ => by
        simp only [TauCeti.PrimePower.card_def]
        have := four_le_two_pow h
        omega)

theorem k150_seven_SU3 (n : ℕ) (hn : 1 ≤ n) : RowAllOfK150 J (projSU 3 2 n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    have h72 := KFacts.KS14.card_projSU_three_mul_gcd 2 1 le_rfl
    norm_num at h72
    exact k150_rowAll_of_card_le hF (by omega) (by omega)
  · exact k150_projSU hF hLSC hLC 2 2 n hn (by norm_num)
      (valid_twistedA le_rfl fun _ => by
        simp only [TauCeti.PrimePower.card_def]
        have := four_le_two_pow h
        omega)

theorem k150_seven_Sp4 (n : ℕ) (hn : 1 ≤ n) : RowAllOfK150 J (projSp 2 (GaloisField 2 n)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    exact k150_rowAll_of_card_le hF (by rw [CFSG.PGLModel.card_projSp_two_two]; norm_num)
      (by rw [CFSG.PGLModel.card_projSp_two_two])
  · have := four_le_two_pow h
    exact k150_projSp_two hF hLSC hLC 2 n hn (by norm_num)
      (valid_B_two (by simp only [TauCeti.PrimePower.card_def]; omega)
        (by simp only [TauCeti.PrimePower.card_def]; omega))

theorem k150_seven_SU4 (n : ℕ) (hn : 1 ≤ n) : RowAllOfK150 J (projSU 4 2 n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact k150_projSU hF hLSC hLC 3 2 n hn (by norm_num)
    (valid_twistedA (by norm_num) (by omega))

theorem k150_seven_G2 (q : PrimePower) (hq2 : q.p = 2) (hq : (LieTypeIndex.G2 q).Valid) :
    RowAllOfK150 J (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group :=
  k150_rowAll_of_lie hF hLSC hLC ⟨_, hq⟩ (by simp; omega) ⟨MulEquiv.refl _⟩

theorem k150_seven_D4 (q : PrimePower) (hq : (LieTypeIndex.trialityD4 q).Valid) (hq2 : q.p = 2) :
    RowAllOfK150 J (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group :=
  k150_rowAll_of_lie hF hLSC hLC ⟨_, hq⟩ (by simp; omega) ⟨MulEquiv.refl _⟩

theorem k150_seven_Sz (m : ℕ) (hm : (LieTypeIndex.suzuki m).Valid) :
    RowAllOfK150 J (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group :=
  k150_rowAll_of_lie hF hLSC hLC ⟨_, hm⟩ (by simp) ⟨MulEquiv.refl _⟩

theorem k150_seven_F4 (m : ℕ) (hm : (LieTypeIndex.reeF4 m).Valid) :
    RowAllOfK150 J (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group :=
  k150_rowAll_of_lie hF hLSC hLC ⟨_, hm⟩ (by simp) ⟨MulEquiv.refl _⟩

theorem k150_seven_Tits (ht : LieTypeIndex.tits.Valid) :
    RowAllOfK150 J (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group :=
  k150_rowAll_of_lie hF hLSC hLC ⟨_, ht⟩ (by simp) ⟨MulEquiv.refl _⟩

theorem k150_eight_SL5 : RowAllOfK150 J (projSL 5 (GaloisField 2 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact k150_projSL hF hLSC hLC 4 2 1 le_rfl (by norm_num)
    (valid_A (by norm_num) (fun h => absurd h (by norm_num)) (by omega))

theorem k150_eight_SU5 : RowAllOfK150 J (projSU 5 2 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact k150_projSU hF hLSC hLC 4 2 1 le_rfl (by norm_num)
    (valid_twistedA (by norm_num) (by omega))

theorem k150_eight_SL6 : RowAllOfK150 J (projSL 6 (GaloisField 2 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact k150_projSL hF hLSC hLC 5 2 1 le_rfl (by norm_num)
    (valid_A (by norm_num) (fun h => absurd h (by norm_num)) (by omega))

theorem k150_eight_SU6 : RowAllOfK150 J (projSU 6 2 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact k150_projSU hF hLSC hLC 5 2 1 le_rfl (by norm_num)
    (valid_twistedA (by norm_num) (by omega))

theorem k150_eight_SL7 : RowAllOfK150 J (projSL 7 (GaloisField 2 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact k150_projSL hF hLSC hLC 6 2 1 le_rfl (by norm_num)
    (valid_A (by norm_num) (fun h => absurd h (by norm_num)) (by omega))

theorem k150_eight_Sp6 : RowAllOfK150 J (projSp 3 (GaloisField 2 1)) := by
  obtain ⟨e⟩ := bridgeSp6Two _ (valid_B_of_three_le le_rfl le_rfl) rfl rfl
  exact k150_rowAll_of_lie hF hLSC hLC _ (by simp) ⟨e.symm⟩

theorem k150_eight_Sp8 : RowAllOfK150 J (projSp 4 (GaloisField 2 1)) := by
  obtain ⟨e⟩ := bridgeSp8Two _ (valid_B_of_three_le (by norm_num) le_rfl) rfl rfl
  exact k150_rowAll_of_lie hF hLSC hLC _ (by simp) ⟨e.symm⟩

theorem k150_eight_OmegaPlus : RowAllOfK150 J (projOmegaPlus 4 (GaloisField 2 1)) := by
  have hv : (LieTypeIndex.D 4 ⟨2, 1, Nat.prime_two, Nat.one_pos⟩).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨le_rfl, id⟩
  obtain ⟨e⟩ := bridgeOmega8PlusTwo _ hv rfl rfl
  exact k150_rowAll_of_lie hF hLSC hLC _ (by simp) ⟨e.symm⟩

theorem k150_eight_OmegaMinus (b c : GaloisField 2 1)
    (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) :
    RowAllOfK150 J (projOmegaMinus 3 (GaloisField 2 1) b c) := by
  have hv : (LieTypeIndex.twistedD 4 ⟨2, 1, Nat.prime_two, Nat.one_pos⟩).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨le_rfl, id⟩
  obtain ⟨b', c', hbc', ⟨e⟩⟩ := bridgeOmega8MinusTwo _ hv rfl rfl
  obtain ⟨rfl, rfl⟩ := eq_one_one_of_irreducible hbc
  obtain ⟨rfl, rfl⟩ := eq_one_one_of_irreducible hbc'
  exact k150_rowAll_of_lie hF hLSC hLC _ (by simp) ⟨e.symm⟩

theorem k150_eight_SL4 : RowAllOfK150 J (projSL 4 (GaloisField 2 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact k150_projSL hF hLSC hLC 3 2 2 (by norm_num) (by norm_num)
    (valid_A (by norm_num) (fun h => absurd h (by norm_num)) fun _ => by
      simp only [TauCeti.PrimePower.card_def]
      norm_num)

theorem k150_eight_Sp6_4 : RowAllOfK150 J (projSp 3 (GaloisField 2 2)) := by
  obtain ⟨e⟩ := bridgeSp6Four _ (valid_B_of_three_le le_rfl (by norm_num)) rfl rfl
  exact k150_rowAll_of_lie hF hLSC hLC _ (by simp) ⟨e.symm⟩

theorem k150_eight_SU5_4 : RowAllOfK150 J (projSU 5 2 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact k150_projSU hF hLSC hLC 4 2 2 (by norm_num) (by norm_num)
    (valid_twistedA (by norm_num) (by omega))

theorem k150_eight_SU5_8 : RowAllOfK150 J (projSU 5 2 3) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact k150_projSU hF hLSC hLC 4 2 3 (by norm_num) (by norm_num)
    (valid_twistedA (by norm_num) (by omega))

theorem k150_eight_F4 : RowAllOfK150 J (TauCeti.CFSGIndex.lie f4TwoIndex).Group :=
  k150_rowAll_of_lie hF hLSC hLC f4TwoIndex (by simp [f4TwoIndex, primePowerTwo])
    ⟨MulEquiv.refl _⟩

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150

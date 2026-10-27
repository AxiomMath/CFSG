module

public import CFSG.RankThree.PartTwo.Sec11.SetUp1118ProofList
public import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard
import CFSG.RankThree.PartTwo.KFacts.KSListsProofArith
import CFSG.RankThree.PartTwo.KFacts.KSListsProof1118Odd
import CFSG.RankThree.PartTwo.KFacts.KSListsProof1121
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
import CFSG.RankThree.PartTwo.Sec6.BThreeCensusOrders
import CFSG.RankThree.PartTwo.Sec21.Item229Orders
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.Sporadic.Ru
import CFSG.LieType.Ree.LargeReeModelSchreier
import CFSG.RankThree.SteinbergR3ELargeReeOrder
import CFSG.Sporadic.Schreier.TitsOuter
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Open (ordTrialityD4 ordG2)
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

namespace KSListsProof

theorem ordTrialityD4_three_five_seven :
    ordTrialityD4 3 = 20560831566912 ∧ ordTrialityD4 5 = 35817806390625000000 ∧
      ordTrialityD4 7 = 450782974156649555296512 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [ordTrialityD4]

theorem ne_ordTrialityD4_of_lt_three {N Q : ℕ} (hQ3 : 3 ≤ Q) (hN : N < 20560831566912) :
    N ≠ ordTrialityD4 Q := by
  have h := Sec19.Step1911Proof.ordTrialityD4_le hQ3
  rw [ordTrialityD4_three_five_seven.1] at h
  omega

theorem ne_ordTrialityD4_of_lt_seven {N Q : ℕ} (hQ : Odd Q) (hQ3 : 3 ≤ Q)
    (hN : N < 450782974156649555296512) (h3 : N ≠ 20560831566912)
    (h5 : N ≠ 35817806390625000000) : N ≠ ordTrialityD4 Q := by
  obtain ⟨e3, e5, e7⟩ := ordTrialityD4_three_five_seven
  intro h
  rcases (by omega : Q = 3 ∨ Q = 4 ∨ Q = 5 ∨ Q = 6 ∨ 7 ≤ Q) with rfl | rfl | rfl | rfl | h7
  · exact h3 (h.trans e3)
  · exact absurd hQ (by decide)
  · exact h5 (h.trans e5)
  · exact absurd hQ (by decide)
  · have := Sec19.Step1911Proof.ordTrialityD4_le h7
    rw [e7] at this
    omega

theorem false_of_two_pow_dvd {m Q n a K : ℕ} (hQ : Odd Q) (hQ3 : 3 ≤ Q)
    (hdvd : (2 ^ n) ^ a ∣ m) (hlt : m < (2 ^ n) ^ K) (hK : K ≤ 3 * a)
    (h : m = ordTrialityD4 Q) : False := by
  refine Sec19.Step1911Proof.false_of_odd (N := n * a) hQ hQ3 (by rwa [pow_mul])
    (hlt.trans_le ?_) h
  rw [← pow_mul]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  calc n * K ≤ n * (3 * a) := Nat.mul_le_mul_left n hK
    _ = 3 * (n * a) := by ring

theorem pow_add_one_le {Q a : ℕ} (hQ : 2 ≤ Q) : Q ^ a + 1 ≤ Q ^ (a + 1) := by
  have h1 : 1 ≤ Q ^ a := Nat.one_le_pow _ _ (by omega)
  have : 2 * Q ^ a ≤ Q ^ (a + 1) := by
    rw [pow_succ, mul_comm]
    exact Nat.mul_le_mul_left _ hQ
  omega

theorem pow_sub_one_lt {Q a : ℕ} (hQ : 1 ≤ Q) : Q ^ a - 1 < Q ^ a :=
  Nat.sub_lt (Nat.one_le_pow _ _ hQ) one_pos

theorem psl2_lt {Q : ℕ} (hQ : 2 ≤ Q) : Q * (Q ^ 2 - 1) < Q ^ 3 := by
  calc Q * (Q ^ 2 - 1) < Q * Q ^ 2 :=
        Nat.mul_lt_mul_of_pos_left (pow_sub_one_lt (by omega)) (by omega)
    _ = Q ^ 3 := by ring

theorem sl3_lt {Q : ℕ} (hQ : 2 ≤ Q) :
    Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 - 1)) < Q ^ 9 ∧ Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 + 1)) < Q ^ 9 := by
  have h2 := pow_sub_one_lt (a := 2) (by omega : 1 ≤ Q)
  have h3 : Q ^ 3 + 1 ≤ Q ^ 4 := pow_add_one_le hQ
  have hp : Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 + 1)) < Q ^ 9 := by
    calc Q ^ 3 * ((Q ^ 2 - 1) * (Q ^ 3 + 1)) < Q ^ 3 * (Q ^ 2 * Q ^ 4) :=
          Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_lt_of_le h2 h3 (by positivity))
            (by positivity)
      _ = Q ^ 9 := by ring
  refine ⟨lt_of_le_of_lt ?_ hp, hp⟩
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))

theorem sp4_lt {Q : ℕ} (hQ : 2 ≤ Q) : Q ^ 4 * ((Q ^ 2 - 1) * (Q ^ 4 - 1)) < Q ^ 12 := by
  have h2 := pow_sub_one_lt (a := 2) (by omega : 1 ≤ Q)
  have h4 : Q ^ 4 - 1 ≤ Q ^ 4 := Nat.sub_le _ _
  calc Q ^ 4 * ((Q ^ 2 - 1) * (Q ^ 4 - 1)) < Q ^ 4 * (Q ^ 2 * Q ^ 4) :=
        Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_lt_of_le h2 h4 (by positivity))
          (by positivity)
    _ = Q ^ 10 := by ring
    _ ≤ Q ^ 12 := Nat.pow_le_pow_right (by omega) (by norm_num)

theorem u4_lt {Q : ℕ} (hQ : 2 ≤ Q) :
    Q ^ 6 * ((Q ^ 2 - 1) * (Q ^ 3 + 1) * (Q ^ 4 - 1)) < Q ^ 18 := by
  have h2 := pow_sub_one_lt (a := 2) (by omega : 1 ≤ Q)
  have h3 : Q ^ 3 + 1 ≤ Q ^ 4 := pow_add_one_le hQ
  have h4 : Q ^ 4 - 1 ≤ Q ^ 4 := Nat.sub_le _ _
  calc Q ^ 6 * ((Q ^ 2 - 1) * (Q ^ 3 + 1) * (Q ^ 4 - 1)) < Q ^ 6 * (Q ^ 2 * Q ^ 4 * Q ^ 4) :=
        Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_lt_of_le
          (Nat.mul_lt_mul_of_lt_of_le h2 h3 (by positivity)) h4 (by positivity)) (by positivity)
    _ = Q ^ 16 := by ring
    _ ≤ Q ^ 18 := Nat.pow_le_pow_right (by omega) (by norm_num)

theorem sz_lt {Q : ℕ} (hQ : 2 ≤ Q) : Q ^ 2 * ((Q - 1) * (Q ^ 2 + 1)) < Q ^ 6 := by
  have h1 : Q - 1 < Q := by omega
  have h2 : Q ^ 2 + 1 ≤ Q ^ 3 := pow_add_one_le hQ
  calc Q ^ 2 * ((Q - 1) * (Q ^ 2 + 1)) < Q ^ 2 * (Q * Q ^ 3) :=
        Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_lt_of_le h1 h2 (by positivity))
          (by positivity)
    _ = Q ^ 6 := by ring

theorem f4_lt {Q : ℕ} (hQ : 2 ≤ Q) :
    Q ^ 12 * (Q - 1) ^ 2 * (Q + 1) ^ 2 * (Q ^ 2 + 1) ^ 2 * (Q ^ 2 - Q + 1) *
      (Q ^ 4 - Q ^ 2 + 1) < Q ^ 36 := by
  have h1 : (Q - 1) ^ 2 < Q ^ 2 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  have h2 : (Q + 1) ^ 2 ≤ (Q ^ 2) ^ 2 := Nat.pow_le_pow_left (by nlinarith) 2
  have h3 : (Q ^ 2 + 1) ^ 2 ≤ (Q ^ 3) ^ 2 := Nat.pow_le_pow_left (pow_add_one_le hQ) 2
  have h4 : Q ^ 2 - Q + 1 ≤ Q ^ 2 := by
    have : Q ≤ Q ^ 2 := Nat.le_self_pow (by norm_num) Q
    omega
  have h5 : Q ^ 4 - Q ^ 2 + 1 ≤ Q ^ 4 := by
    have : Q ^ 2 ≤ Q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  calc Q ^ 12 * (Q - 1) ^ 2 * (Q + 1) ^ 2 * (Q ^ 2 + 1) ^ 2 * (Q ^ 2 - Q + 1) *
        (Q ^ 4 - Q ^ 2 + 1)
      = Q ^ 12 * ((Q - 1) ^ 2 * ((Q + 1) ^ 2 * (Q ^ 2 + 1) ^ 2 * (Q ^ 2 - Q + 1) *
          (Q ^ 4 - Q ^ 2 + 1))) := by ring
    _ < Q ^ 12 * (Q ^ 2 * ((Q ^ 2) ^ 2 * (Q ^ 3) ^ 2 * Q ^ 2 * Q ^ 4)) :=
        Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_lt_of_le h1
          (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h2 h3) h4) h5) (by positivity))
          (by positivity)
    _ = Q ^ 30 := by ring
    _ ≤ Q ^ 36 := Nat.pow_le_pow_right (by omega) (by norm_num)

theorem two_le_two_pow {n : ℕ} (hn : 1 ≤ n) : 2 ≤ 2 ^ n :=
  le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn : 2 ^ 1 ≤ 2 ^ n)

theorem card_four {X : Type} [Group X]
    (hX : (∃ n : ℕ, n ≤ 9 ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
      Sec4.IsExtOf X (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3)) ∨
      Sec4.IsExtOf X (alternatingGroup (Fin 7)) (Multiplicative (ZMod 3))) :
    Nat.card X < 20560831566912 := by
  rcases hX with ⟨n, hn, ⟨φ⟩⟩ | h6 | h7
  · rw [Nat.card_congr φ.toEquiv]
    have := Nat.le_of_dvd (Nat.factorial_pos 9) (Sec6.BThreeCensus.card_alternatingGroup_dvd hn)
    have h9 : Nat.factorial 9 = 362880 := by decide
    omega
  · rw [Sec6.BThreeCensus.card_of_isExtOf h6, nat_card_alternatingGroup, Nat.card_fin,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    decide
  · rw [Sec6.BThreeCensus.card_of_isExtOf h7, nat_card_alternatingGroup, Nat.card_fin,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    decide

theorem sporadic_bounds {m : ℕ}
    (hm : m ∈ ({7920, 95040, 443520, 10200960, 244823040, 175560, 604800, 50232960,
        86775571046077562880, 898128000, 44352000, 4030387200, 460815505920} : Finset ℕ))
    {k : ℕ} (hk : k = 1 ∨ k = 3) :
    m * k < 450782974156649555296512 ∧ m * k ≠ 20560831566912 ∧
      m * k ≠ 35817806390625000000 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hk with rfl | rfl <;>
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num

section Sporadic


theorem card_five {X : Type} [Group X]
    (hX : (∃ s ∈ Sec4.sporadics46, Nonempty (X ≃* Blueprint.NativeSporadic.Carrier s)) ∨
      ∃ s ∈ Sec4.sporadicCovers46,
        Sec4.IsExtOf X (Blueprint.NativeSporadic.Carrier s) (Multiplicative (ZMod 3))) :
    Nat.card X < 450782974156649555296512 ∧ Nat.card X ≠ 20560831566912 ∧
      Nat.card X ≠ 35817806390625000000 := by
  rcases hX with ⟨s, hs, ⟨φ⟩⟩ | ⟨s, hs, hext⟩
  · rw [Nat.card_congr φ.toEquiv]
    by_cases hRu : s = .Ru
    · subst hRu
      rw [show Nat.card (Blueprint.NativeSporadic.Carrier .Ru) = 145926144000 from
        CFSG.Sporadic.Ru.card_Ru]
      norm_num
    · have h := sporadic_bounds (Sec6.BThreeCensus.card_carrier_of_mem (Or.inl hs) hRu)
        (Or.inl rfl)
      rwa [mul_one] at h
  · have hRu : s ≠ .Ru := by
      rintro rfl
      simp [Sec4.sporadicCovers46] at hs
    rw [Sec6.BThreeCensus.card_of_isExtOf hext, Nat.card_congr Multiplicative.toAdd,
      Nat.card_zmod]
    exact sporadic_bounds (Sec6.BThreeCensus.card_carrier_of_mem (Or.inr hs) hRu) (Or.inr rfl)

end Sporadic

theorem card_seven {X : Type} [Group X]
    (hX : Nonempty (X ≃* projSL 5 (GaloisField 2 1)) ∨
      Nonempty (X ≃* projSp 3 (GaloisField 2 1)) ∨ Nonempty (X ≃* projSU 5 2 2)) :
    Nat.card X < 450782974156649555296512 ∧ Nat.card X ≠ 20560831566912 ∧
      Nat.card X ≠ 35817806390625000000 := by
  rcases hX with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · rw [Nat.card_congr φ.toEquiv, Sec19.Step1911Proof.card_projSL (by norm_num) le_rfl,
      show CFSG.Open.ordA (5 - 1) (2 ^ 1) = 9999360 by decide]
    norm_num
  · rw [Nat.card_congr φ.toEquiv, Sec6.BThreeCensus.card_projSp_three_two]
    norm_num
  · rw [Nat.card_congr φ.toEquiv, Sec21.card_projSU (by norm_num) (by norm_num),
      show CFSG.Open.ordTwistedA (5 - 1) (2 ^ 2) = 53443952640000 by decide]
    norm_num

section Certified


theorem card_eight {X : Type} [Group X]
    (hX : (∃ e : ℕ, 1 ≤ e ∧ e ≤ 2 ∧
        (Nonempty (X ≃* projSL 3 (GaloisField 3 e)) ∨ Nonempty (X ≃* projSU 3 3 e))) ∨
      Nonempty (X ≃* projSL 4 (GaloisField 3 1)) ∨
      (Nat.card (Subgroup.center X) ≤ 3 ∧
        (Blueprint.ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 3 1 ∨
          Nonempty (X ⧸ Subgroup.center X ≃* projSU 4 3 1)))) :
    Nat.card X < 20560831566912 := by
  rcases hX with ⟨e, he1, he2, ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩ | ⟨⟨φ⟩⟩ | ⟨hZ, hG | ⟨⟨φ⟩⟩⟩
  · have h := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 3 e)
    rw [GaloisField.card 3 e (by omega), ← Nat.card_congr φ.toEquiv] at h
    have hg : 0 < Nat.gcd 3 (3 ^ e - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hle := Nat.le_mul_of_pos_right (Nat.card X) hg
    rw [h] at hle
    interval_cases e <;> norm_num at hle <;> omega
  · have h := KFacts.KS14.card_projSU_three_mul_gcd 3 e he1
    rw [← Nat.card_congr φ.toEquiv] at h
    have hg : 0 < Nat.gcd 3 (3 ^ e + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hle := Nat.le_mul_of_pos_right (Nat.card X) hg
    rw [h] at hle
    interval_cases e <;> norm_num at hle <;> omega
  · have h := card_projSL_four_mul (GaloisField 3 1)
    rw [GaloisField.card 3 1 one_ne_zero, ← Nat.card_congr φ.toEquiv] at h
    have hg : 0 < Nat.gcd 4 (3 ^ 1 - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hle := Nat.le_mul_of_pos_right (Nat.card X) hg
    rw [h] at hle
    norm_num at hle
    omega
  · have h := CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_G2 hG.2
    rw [Sec6.BThreeCensus.card_eq_card_center_mul, h]
    have : ordG2 (3 ^ 1) = 4245696 := by norm_num [ordG2]
    rw [this]
    omega
  · have h := card_projSU_four_mul 3 1 le_rfl
    rw [← Nat.card_congr φ.toEquiv] at h
    have hg : 0 < Nat.gcd 4 (3 ^ 1 + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hle := Nat.le_mul_of_pos_right (Nat.card (X ⧸ Subgroup.center X)) hg
    rw [h] at hle
    norm_num at hle
    rw [Sec6.BThreeCensus.card_eq_card_center_mul]
    have := Nat.mul_le_mul hZ hle
    omega

theorem false_six
    {X : Type} [Group X] {Q : ℕ} (hQ : Odd Q) (hQ3 : 3 ≤ Q)
    (hX : Sec4.IsChevTwoRankTwoModel X ∨ ∃ n : ℕ, 1 ≤ n ∧ Sec4.IsSLThreeEpsAt X (2 ^ n))
    (hcard : Nat.card X = ordTrialityD4 Q) : False := by
  have hcop : ∀ {n g : ℕ}, Odd g → Nat.Coprime ((2 ^ n) ^ 3) g := fun hg =>
    Nat.Coprime.pow_left 3 (Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hg))
  have hg3 : ∀ {x : ℕ}, Odd (Nat.gcd 3 x) := fun {x} =>
    Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left 3 x)
  rcases hX with (⟨n, hn, ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩ |
      ⟨f, hG | hD | hS | hF | hT⟩) |
    ⟨n, hn, K, _, _, ⟨hK, ⟨φ⟩⟩ | ⟨hK, ⟨φ⟩⟩⟩
  ·
    have hm : Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      rw [Nat.card_congr φ.toEquiv, Sec21.card_projSL_two n hn]
    refine false_of_two_pow_dvd (n := n) (a := 1) (K := 3) hQ hQ3 ?_ ?_ (by norm_num) hcard
    · rw [hm, pow_one]
      exact Dvd.intro _ rfl
    · rw [hm]
      exact psl2_lt (two_le_two_pow hn)
  ·
    have hm : Nat.card X * Nat.gcd 3 (2 ^ n - 1) =
        2 ^ (n * 3) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
      rw [Nat.card_congr φ.toEquiv, Sec19.Step1911Proof.card_projSL (by norm_num) hn]
      exact Sec19.Step1911Proof.ordA_two_mul_gcd n
    rw [pow_mul] at hm
    refine false_of_two_pow_dvd (n := n) (a := 3) (K := 9) hQ hQ3
      ((hcop hg3).dvd_of_dvd_mul_right ⟨_, hm⟩) ?_ (by norm_num) hcard
    exact lt_of_le_of_lt (le_trans (Nat.le_mul_of_pos_right _ (Nat.gcd_pos_of_pos_left _
      (by norm_num))) hm.le) (sl3_lt (two_le_two_pow hn)).1
  ·
    have hm := KFacts.KS14.card_projSU_three_mul_gcd 2 n hn
    rw [← Nat.card_congr φ.toEquiv] at hm
    refine false_of_two_pow_dvd (n := n) (a := 3) (K := 9) hQ hQ3
      ((hcop hg3).dvd_of_dvd_mul_right ⟨_, hm⟩) ?_ (by norm_num) hcard
    exact lt_of_le_of_lt (le_trans (Nat.le_mul_of_pos_right _ (Nat.gcd_pos_of_pos_left _
      (by norm_num))) hm.le) (sl3_lt (two_le_two_pow hn)).2
  ·
    have hm : Nat.card X = (2 ^ n) ^ 4 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) := by
      rw [Nat.card_congr φ.toEquiv, Sec19.Step1911Proof.card_projSp_two hn, pow_mul]
    refine false_of_two_pow_dvd (n := n) (a := 4) (K := 12) hQ hQ3 ⟨_, hm⟩ ?_ (by norm_num) hcard
    rw [hm]
    exact sp4_lt (two_le_two_pow hn)
  ·
    have hm := Sec19.Step1911Proof.card_projSU_four hn
    rw [← Nat.card_congr φ.toEquiv] at hm
    refine false_of_two_pow_dvd (n := n) (a := 6) (K := 18) hQ hQ3 ⟨_, hm⟩ ?_ (by norm_num) hcard
    rw [hm]
    exact u4_lt (two_le_two_pow hn)
  ·
    have hf : 1 ≤ f := hG.1.2.1
    have hm := CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_G2 hG.2
    refine false_of_two_pow_dvd (n := f) (a := 6) (K := 18) hQ hQ3 (hm ▸ pow_six_dvd_ordG2 _) ?_
      (by norm_num) hcard
    rw [hm]
    exact (ordG2_lt_pow (two_le_two_pow hf)).trans_le
      (Nat.pow_le_pow_right (by positivity) (by norm_num))
  ·
    obtain ⟨-, hf, hm⟩ := Sec19.Step1911Proof.card_of_trialityD4 hD
    refine false_of_two_pow_dvd (n := f) (a := 12) (K := 36) hQ hQ3
      (hm ▸ pow_twelve_dvd_ordTrialityD4 _) ?_ (by norm_num) hcard
    rw [hm]
    exact (ordTrialityD4_lt_pow (two_le_two_pow hf)).trans_le
      (Nat.pow_le_pow_right (by positivity) (by norm_num))
  ·
    obtain ⟨-, a, ha, K, _, _, hfa, hK, ⟨φ⟩⟩ := hS
    have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
    have hm : Nat.card X = (2 ^ (2 * a + 1)) ^ 2 * ((2 ^ (2 * a + 1) - 1) *
        ((2 ^ (2 * a + 1)) ^ 2 + 1)) := by
      rw [Nat.card_congr φ.toEquiv, CFSG.LieType.Ree.suzuki_order hK']
      ring
    refine false_of_two_pow_dvd (n := 2 * a + 1) (a := 2) (K := 6) hQ hQ3 ⟨_, hm⟩ ?_
      (by norm_num) hcard
    rw [hm]
    exact sz_lt (two_le_two_pow (by omega))
  ·
    have hSch := CFSG.LieType.Ree.ReeTag.large_Ree_model_Schreier X 2 f hF
    obtain ⟨-, a, hfa, hmodel⟩ := hF
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
    have : Fintype K := Fintype.ofFinite K
    have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_of_card_eq_prime_pow
      (f := 2 * a + 1) (by
        rw [← Nat.card_eq_fintype_card, hK, hfa]
        rfl)
    obtain ⟨E⟩ := hSch.2.2.2.2.2 a K hfa hK ⟨e⟩
    have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
    have hord :=
      (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion a K
        hK').1
    have hm := (Nat.card_congr E.toEquiv).trans hord
    refine false_of_two_pow_dvd (n := 2 * a + 1) (a := 12) (K := 36) hQ hQ3
      (hm ▸ (((((dvd_refl _).mul_right _).mul_right _).mul_right _).mul_right _).mul_right _) ?_
      (by norm_num) hcard
    rw [hm]
    exact f4_lt (two_le_two_pow (by omega))
  ·
    obtain ⟨E⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv X 2 f hT
    rw [Nat.card_congr E.toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD] at hcard
    exact ne_ordTrialityD4_of_lt_three hQ3 (by norm_num) hcard
  ·
    have hm : Nat.card X = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) := by
      rw [Nat.card_congr φ.toEquiv, CFSG.SectionRank.OddCover.card_statedSL_three, hK]
      ring
    refine false_of_two_pow_dvd (n := n) (a := 3) (K := 9) hQ hQ3 ⟨_, hm⟩ ?_ (by norm_num) hcard
    rw [hm]
    exact (sl3_lt (two_le_two_pow hn)).1
  ·
    have : Fintype K := Fintype.ofFinite K
    have : CharP K 2 := charP_of_card_eq_prime_pow (f := n * 2)
      (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
    have hm : Nat.card X = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1)) := by
      rw [Nat.card_congr φ.toEquiv, CFSG.SectionRank.OddCover.card_statedSU_three hK]
      ring
    refine false_of_two_pow_dvd (n := n) (a := 3) (K := 9) hQ hQ3 ⟨_, hm⟩ ?_ (by norm_num) hcard
    rw [hm]
    exact (sl3_lt (two_le_two_pow hn)).2

end Certified

end KSListsProof

open KSListsProof in
theorem kFact1118Triality46 :
    KFact1118Triality46 := by
  intro X _ hX q hq ⟨e⟩
  by_contra hp2
  have hr := q.prime_p
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hcard : Nat.card X = ordTrialityD4 (q.p ^ q.exponent) := by
    rw [Nat.card_congr e.toEquiv, card_trialityD4_carrier q hq, TauCeti.PrimePower.card_def]
  have hQ3 : 3 ≤ q.p ^ q.exponent := three_le_pow hr hp2 hf
  have hQodd : Odd (q.p ^ q.exponent) := (hr.odd_of_ne_two hp2).pow
  rcases hX with ⟨p, e', hp, hp2', he, ⟨φ⟩⟩ | ⟨p, e', hp, -, he1, he2, h2⟩ |
    ⟨p, hp, hp3, h3⟩ | h4 | h5 | h6 | h7 | h8
  · exact false_psl2_of_iso hr hp2 hf hp2' he φ hcard
  · exact false_sl3_of_list hr hp2 hf he1 he2 h2 hcard
  · exact false_three_of_list hr hp2 hf hp3 h3 hcard
  · exact ne_ordTrialityD4_of_lt_three hQ3 (card_four h4) hcard
  · obtain ⟨h1, h2, h3⟩ := card_five h5
    exact ne_ordTrialityD4_of_lt_seven hQodd hQ3 h1 h2 h3 hcard
  · exact false_six hQodd hQ3 h6 hcard
  · obtain ⟨h1, h2, h3⟩ := card_seven h7
    exact ne_ordTrialityD4_of_lt_seven hQodd hQ3 h1 h2 h3 hcard
  · exact ne_ordTrialityD4_of_lt_three hQ3 (card_eight h8) hcard

end CFSG.RankThree.PartTwo.Sec11

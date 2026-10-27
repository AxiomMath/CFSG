module

public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusTools
public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents
import CFSG.RankThree.PartTwo.Sec4.Item413Orders
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec4.Item426A6Proof
import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
import CFSG.Sporadic.Schreier.TitsOuter
import CFSG.Sporadic.Mathieu.M11
import CFSG.Sporadic.Mathieu.M24
import CFSG.Sporadic.J1
import CFSG.Sporadic.J2
import CFSG.Sporadic.J3
import CFSG.Sporadic.J4
import CFSG.Sporadic.McL.Simple
import CFSG.Sporadic.HS
import CFSG.Sporadic.He.Simple
import CFSG.Sporadic.ON.Simple
import CFSG.Models.PGLOrders
import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.RankThree.PartTwo.Sec6.BThreeCensus

open CFSG CFSG.Blueprint CFSG.Assembly.RankThreeEven

variable {X : Type} [Group X]

theorem card_of_isExtOf {A B : Type*} [Group A] [Group B] (h : Sec4.IsExtOf X A B) :
    Nat.card X = Nat.card A * Nat.card B := by
  obtain ⟨K, _, ⟨eK⟩, ⟨eQ⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup K, Nat.card_congr eQ.toEquiv,
    Nat.card_congr eK.toEquiv]

theorem card_eq_card_center_mul :
    Nat.card X = Nat.card (Subgroup.center X) * Nat.card (X ⧸ Subgroup.center X) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X), mul_comm]

theorem card_alternatingGroup_dvd {n : ℕ} (hn : n ≤ 9) :
    Nat.card (alternatingGroup (Fin n)) ∣ Nat.factorial 9 := by
  refine (Subgroup.card_subgroup_dvd_card _).trans ?_
  rw [Nat.card_perm, Nat.card_fin]
  exact Nat.factorial_dvd_factorial hn

theorem threePrimeB3_four [Finite X]
    (hX : (∃ n : ℕ, n ≤ 9 ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
      Sec4.IsExtOf X (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3)) ∨
      Sec4.IsExtOf X (alternatingGroup (Fin 7)) (Multiplicative (ZMod 3))) :
    ThreePrimeB3 X := by
  rcases hX with ⟨n, hn, ⟨e⟩⟩ | h6 | h7
  · refine threePrimeB3_of_dvd (M := Nat.factorial 9) (B := 4) ?_ (by decide) (by decide)
      (by decide)
    rw [Nat.card_congr e.toEquiv]
    exact card_alternatingGroup_dvd hn
  · refine threePrimeB3_of_dvd (M := 1080) (B := 3) ?_ (by norm_num) (by norm_num) (by decide)
    rw [card_of_isExtOf h6, nat_card_alternatingGroup, Nat.card_fin,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    decide
  · refine threePrimeB3_of_dvd (M := 7560) (B := 3) ?_ (by norm_num) (by norm_num) (by decide)
    rw [card_of_isExtOf h7, nat_card_alternatingGroup, Nat.card_fin,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    decide

theorem not_suzukiOrder_dvd_three_mul {m : ℕ}
    (hm : m ∈ ({7920, 95040, 443520, 10200960, 244823040, 175560, 604800, 50232960,
        86775571046077562880, 898128000, 44352000, 4030387200, 460815505920} : Finset ℕ)) :
    ∀ a ∈ Finset.Icc 1 16, ¬ suzukiOrder a ∣ 3 * m := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

section Sporadic


theorem card_carrier_of_mem {s : TauCeti.SporadicName}
    (hs : s ∈ Sec4.sporadics46 ∨ s ∈ Sec4.sporadicCovers46) (hRu : s ≠ .Ru) :
    Nat.card (NativeSporadic.Carrier s) ∈
      ({7920, 95040, 443520, 10200960, 244823040, 175560, 604800, 50232960,
        86775571046077562880, 898128000, 44352000, 4030387200, 460815505920} : Finset ℕ) := by
  have hm23 : Nat.card NativeSporadic.M23 = 10200960 :=
    (CFSG.Sporadic.Schreier.fam_m23_order).choose_spec.2.2.2.choose_spec.2.2.2.2
  simp only [Sec4.sporadics46, Sec4.sporadicCovers46, List.mem_cons, List.not_mem_nil,
    or_false] at hs
  rcases hs with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
      (rfl | rfl | rfl | rfl)
  · rw [show Nat.card (NativeSporadic.Carrier .M11) = 7920 from CFSG.Sporadic.Mathieu.card_M11]
    decide
  · rw [show Nat.card (NativeSporadic.Carrier .M12) = 95040 from
      CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeM12]
    decide
  · rw [show Nat.card (NativeSporadic.Carrier .M22) = 443520 from
      CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeM22]
    decide
  · rw [show Nat.card (NativeSporadic.Carrier .M23) = 10200960 from hm23]
    decide
  · rw [show Nat.card (NativeSporadic.Carrier .M24) = 244823040 from
      CFSG.Sporadic.Mathieu.card_M24]
    decide
  · rw [show Nat.card (NativeSporadic.Carrier .J1) = 175560 from CFSG.Sporadic.J1.card_J1]
    decide
  · rw [show Nat.card (NativeSporadic.Carrier .J2) = 604800 from CFSG.Sporadic.J2.card_J2]
    decide
  · rw [show Nat.card (NativeSporadic.Carrier .J3) = 50232960 from CFSG.Sporadic.J3.card_J3]
    decide
  · rw [show Nat.card (NativeSporadic.Carrier .J4) = 86775571046077562880 from
      CFSG.Sporadic.J4.card_J4]
    decide
  · rw [show Nat.card (NativeSporadic.Carrier .McL) = 898128000 from CFSG.Sporadic.McL.card_McL]
    decide
  · rw [show Nat.card (NativeSporadic.Carrier .HS) = 44352000 from CFSG.Sporadic.HS.card_HS]
    decide
  · rw [show Nat.card (NativeSporadic.Carrier .He) = 4030387200 from CFSG.Sporadic.He.card_He]
    decide
  · exact absurd rfl hRu
  · rw [show Nat.card (NativeSporadic.Carrier .M22) = 443520 from
      CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeM22]
    decide
  · rw [show Nat.card (NativeSporadic.Carrier .J3) = 50232960 from CFSG.Sporadic.J3.card_J3]
    decide
  · rw [show Nat.card (NativeSporadic.Carrier .McL) = 898128000 from CFSG.Sporadic.McL.card_McL]
    decide
  · rw [show Nat.card (NativeSporadic.Carrier .ONan) = 460815505920 from
      CFSG.Sporadic.ON.card_ON_eq]
    decide

theorem threePrimeB3_five [Finite X]
    (hX : (∃ s ∈ Sec4.sporadics46, s ≠ .Ru ∧ Nonempty (X ≃* NativeSporadic.Carrier s)) ∨
      ∃ s ∈ Sec4.sporadicCovers46,
        Sec4.IsExtOf X (NativeSporadic.Carrier s) (Multiplicative (ZMod 3))) :
    ThreePrimeB3 X := by
  rcases hX with ⟨s, hs, hRu, ⟨e⟩⟩ | ⟨s, hs, hext⟩
  · have hm := card_carrier_of_mem (Or.inl hs) hRu
    refine threePrimeB3_of_dvd (M := 3 * Nat.card (NativeSporadic.Carrier s)) (B := 16) ?_ ?_ ?_
      (not_suzukiOrder_dvd_three_mul hm)
    · rw [Nat.card_congr e.toEquiv]
      exact Dvd.intro_left _ rfl
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> norm_num
  · have hRu : s ≠ .Ru := by
      rintro rfl
      simp [Sec4.sporadicCovers46] at hs
    have hm := card_carrier_of_mem (Or.inr hs) hRu
    refine threePrimeB3_of_dvd (M := 3 * Nat.card (NativeSporadic.Carrier s)) (B := 16) ?_ ?_ ?_
      (not_suzukiOrder_dvd_three_mul hm)
    · rw [card_of_isExtOf hext, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, mul_comm]
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> norm_num
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> norm_num

end Sporadic

theorem threePrimeB3_tits
    [Finite X] {p f : ℕ}
    (h : ReeTitsModel X .Tits p f) : ThreePrimeB3 X := by
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv X p f h
  refine threePrimeB3_of_dvd (M := 17971200) (B := 5) ?_ (by norm_num) (by norm_num) (by decide)
  rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD]

theorem card_SL_galoisField (n p e : ℕ) [Fact p.Prime] [NeZero n] (he : e ≠ 0) :
    Nat.card (Matrix.SpecialLinearGroup (Fin n) (GaloisField p e)) =
      (∏ i : Fin n, ((p ^ e) ^ n - (p ^ e) ^ (i : ℕ))) / (p ^ e - 1) := by
  have : Fintype (GaloisField p e) := Fintype.ofFinite _
  rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, GaloisField.card p e he]

theorem card_projSU_five_four_dvd : Nat.card (projSU 5 2 2) ∣ 4 ^ 10 * 254840625 := by
  have hSU := CFSG.RankThree.PartTwo.Census.card_statedSU_five_four
    (CFSG.RankThree.PartTwo.Sec4.unitaryFieldData_galoisField 2 2 (by norm_num))
  have : Finite (CFSG.Assembly.LowTwoRank.StatedSU 5 (2 ^ 2) (GaloisField 2 (2 * 2))) :=
    Nat.finite_of_card_ne_zero (by rw [hSU]; norm_num)
  rw [← hSU]
  exact CFSG.RankThree.PartTwo.Sec4.card_projSU_dvd 5 2 2

theorem card_projSp_three_two : Nat.card (projSp 3 (GaloisField 2 1)) = 1451520 :=
  CFSG.PGLModel.card_projSp_three_two

theorem threePrimeB3_seven [Finite X]
    (hX : Nonempty (X ≃* projSL 5 (GaloisField 2 1)) ∨
      Nonempty (X ≃* projSp 3 (GaloisField 2 1)) ∨ Nonempty (X ≃* projSU 5 2 2)) :
    ThreePrimeB3 X := by
  rcases hX with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · refine threePrimeB3_of_dvd (M := 9999360) (B := 6) ?_ (by norm_num) (by norm_num)
      (by decide)
    rw [Nat.card_congr e.toEquiv]
    refine (CFSG.RankThree.PartTwo.Sec4.card_projSL_dvd 5 (GaloisField 2 1)).trans ?_
    rw [card_SL_galoisField 5 2 1 one_ne_zero]
    decide
  · refine threePrimeB3_of_dvd (M := 1451520) (B := 5) ?_ (by norm_num) (by norm_num)
      (by decide)
    rw [Nat.card_congr e.toEquiv, card_projSp_three_two]
  · refine threePrimeB3_of_dvd (M := 4 ^ 10 * 254840625) (B := 11) ?_ (by norm_num)
      (by norm_num) (by decide)
    rw [Nat.card_congr e.toEquiv]
    exact card_projSU_five_four_dvd

theorem card_projSU_four_three : Nat.card (projSU 4 3 1) = 3265920 :=
  CFSG.PGLModel.card_projSU_four_three

theorem card_projSU_three_three_dvd {e : ℕ} (he : 1 ≤ e) :
    Nat.card (projSU 3 3 e) ∣ (3 ^ e) ^ 3 * (((3 ^ e) ^ 2 - 1) * ((3 ^ e) ^ 3 + 1)) := by
  rw [← CFSG.RankThree.PartTwo.KFacts.KS14.card_projSU_three_mul_gcd 3 e he]
  exact Dvd.intro _ rfl

theorem dvd_two_of_mul_suzukiOrder_dvd_L39 (a : ℕ) (ha : 1 ≤ a) (n : ℕ)
    (hn : n * suzukiOrder a ∣ 42456960) (h3 : ¬ 3 ∣ n) : n ∣ 2 := by
  have hs : suzukiOrder a ∣ 42456960 := Dvd.dvd.trans (Dvd.intro_left _ rfl) hn
  have haB := le_of_suzukiOrder_dvd (B := 6) (by norm_num) (by norm_num) hs
  interval_cases a
  · have h1 : n ∣ 2 * 3 ^ 6 := by
      have : suzukiOrder 1 = 29120 := by decide
      rw [this] at hn
      exact Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 29120)
        (by simpa [mul_comm] using hn)
    have hcop : Nat.Coprime n (3 ^ 6) :=
      Nat.Coprime.pow_right 6 ((Nat.coprime_comm.mp
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)))
    exact hcop.dvd_of_dvd_mul_right h1
  all_goals exact absurd hs (by decide)

theorem threePrimeB3_eight
    [Finite X]
    (hX : (∃ e : ℕ, 1 ≤ e ∧ e ≤ 2 ∧
        (Nonempty (X ≃* projSL 3 (GaloisField 3 e)) ∨ Nonempty (X ≃* projSU 3 3 e))) ∨
      Nonempty (X ≃* projSL 4 (GaloisField 3 1)) ∨
      (Nat.card (Subgroup.center X) ≤ 3 ∧
        (ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 3 1 ∨
          Nonempty (X ⧸ Subgroup.center X ≃* projSU 4 3 1)))) :
    ThreePrimeB3 X := by
  rcases hX with ⟨e, he1, he2, ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩⟩ | ⟨⟨f⟩⟩ | ⟨hZ, hG | ⟨⟨f⟩⟩⟩
  · interval_cases e
    · refine threePrimeB3_of_dvd (M := 5616) (B := 3) ?_ (by norm_num) (by norm_num) (by decide)
      rw [Nat.card_congr f.toEquiv]
      refine (CFSG.RankThree.PartTwo.Sec4.card_projSL_dvd 3 (GaloisField 3 1)).trans ?_
      rw [card_SL_galoisField 3 3 1 one_ne_zero]
      decide
    · refine threePrimeB3_of_dvd_two (M := 42456960) ?_ dvd_two_of_mul_suzukiOrder_dvd_L39
      rw [Nat.card_congr f.toEquiv]
      refine (CFSG.RankThree.PartTwo.Sec4.card_projSL_dvd 3 (GaloisField 3 2)).trans ?_
      rw [card_SL_galoisField 3 3 2 two_ne_zero]
      decide
  · interval_cases e
    · refine threePrimeB3_of_dvd (M := 6048) (B := 3) ?_ (by norm_num) (by norm_num) (by decide)
      rw [Nat.card_congr f.toEquiv]
      exact card_projSU_three_three_dvd le_rfl
    · refine threePrimeB3_of_dvd (M := 42573600) (B := 6) ?_ (by norm_num) (by norm_num)
        (by decide)
      rw [Nat.card_congr f.toEquiv]
      exact card_projSU_three_three_dvd (by norm_num)
  · refine threePrimeB3_of_dvd (M := 12130560) (B := 6) ?_ (by norm_num) (by norm_num)
      (by decide)
    rw [Nat.card_congr f.toEquiv]
    refine (CFSG.RankThree.PartTwo.Sec4.card_projSL_dvd 4 (GaloisField 3 1)).trans ?_
    rw [card_SL_galoisField 4 3 1 one_ne_zero]
    decide
  · refine threePrimeB3_of_not_five_dvd fun h5 => ?_
    rw [card_eq_card_center_mul] at h5
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp h5 with h | h
    · have h0 : 0 < Nat.card (Subgroup.center X) := Nat.card_pos
      have := Nat.le_of_dvd h0 h
      omega
    · exact CFSG.RankThree.PartTwo.Sec4.Item426.not_five_dvd_card_of_G2_three hG h
  · refine threePrimeB3_of_dvd (M := 6 * 3265920) (B := 5) ?_ (by norm_num) (by norm_num)
      (by decide)
    rw [card_eq_card_center_mul, Nat.card_congr f.toEquiv, card_projSU_four_three]
    refine Nat.mul_dvd_mul_right ?_ _
    have h0 : 0 < Nat.card (Subgroup.center X) := Nat.card_pos
    interval_cases (Nat.card (Subgroup.center X)) <;> norm_num

end CFSG.RankThree.PartTwo.Sec6.BThreeCensus

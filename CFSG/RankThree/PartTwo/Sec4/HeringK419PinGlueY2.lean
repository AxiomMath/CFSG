module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419PinGlueY1
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusOrders
public import CFSG.RankThree.PartOne.S12K.Rigidity
public import CFSG.GH74.Orders.LieType
public import CFSG.Sporadic.Ru
public import CFSG.Models.PGLOrders

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringPin

open Finset CFSG.Open CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

open CFSG.RankThree.PartTwo.Sec6.BThreeCensus

theorem num_c4 {X : Type} [Group X]
    (h : (∃ n : ℕ, n ≤ 9 ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
      IsExtOf X (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3)) ∨
      IsExtOf X (alternatingGroup (Fin 7)) (Multiplicative (ZMod 3))) :
    NumList46 (Nat.card X) := by
  refine NumList46.explicit ?_
  rcases h with ⟨n, hn, ⟨e⟩⟩ | h6 | h7
  · refine ⟨362880, by decide +kernel, ?_⟩
    rw [Nat.card_congr e.toEquiv]
    exact (card_alternatingGroup_dvd hn : _ ∣ Nat.factorial 9)
  · refine ⟨1080, by decide +kernel, ?_⟩
    rw [card_of_isExtOf h6, nat_card_alternatingGroup, Nat.card_fin,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    decide
  · refine ⟨7560, by decide +kernel, ?_⟩
    rw [card_of_isExtOf h7, nat_card_alternatingGroup, Nat.card_fin,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    decide

theorem list13_subset : ∀ m ∈ ({7920, 95040, 443520, 10200960, 244823040, 175560, 604800,
    50232960, 86775571046077562880, 898128000, 44352000, 4030387200, 460815505920} :
      Finset ℕ), m ∈ ExplicitD ∧ 3 * m ∈ ExplicitD := by
  decide +kernel

section Certs


theorem num_c5 {X : Type} [Group X]
    (h : (∃ s ∈ Sec4.sporadics46, Nonempty (X ≃* NativeSporadic.Carrier s)) ∨
      ∃ s ∈ Sec4.sporadicCovers46,
        IsExtOf X (NativeSporadic.Carrier s) (Multiplicative (ZMod 3))) :
    NumList46 (Nat.card X) := by
  refine NumList46.explicit ?_
  rcases h with ⟨s, hs, ⟨e⟩⟩ | ⟨s, hs, hext⟩
  · by_cases hRu : s = .Ru
    · subst hRu
      refine ⟨145926144000, by decide +kernel, ?_⟩
      rw [Nat.card_congr e.toEquiv]
      exact (CFSG.Sporadic.Ru.card_Ru).dvd
    · have hm := card_carrier_of_mem (Or.inl hs) hRu
      exact ⟨Nat.card X, by
        rw [Nat.card_congr e.toEquiv]
        exact (list13_subset _ hm).1, dvd_rfl⟩
  · have hRu : s ≠ .Ru := by
      rintro rfl
      simp [Sec4.sporadicCovers46] at hs
    have hm := card_carrier_of_mem (Or.inr hs) hRu
    refine ⟨3 * Nat.card (NativeSporadic.Carrier s), (list13_subset _ hm).2, ?_⟩
    rw [card_of_isExtOf hext, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, mul_comm]

end Certs

theorem num_projSL_two_even {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (φ : X ≃* projSL 2 (GaloisField 2 n)) : NumList46 (Nat.card X) := by
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have h1 := CFSG.RankThree.PartTwo.Sec11.KSListsProof.card_projSL_two_mul (GaloisField 2 n)
  rw [hK, ← Nat.card_congr φ.toEquiv] at h1
  have hg : Nat.gcd 2 (2 ^ n - 1) = 1 :=
    Nat.coprime_two_left.mpr (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega))
  rw [hg, mul_one] at h1
  have h2 : 2 ≤ 2 ^ n := le_trans Nat.prime_two.two_le (Nat.le_self_pow (by omega) 2)
  exact NumList46.psl2 ⟨2 ^ n, 1, h2, Or.inr ⟨(Nat.even_pow' (by omega)).mpr even_two, rfl⟩,
    by rw [mul_one, h1]⟩

section Certs


theorem num_c6 {X : Type} [Group X]
    (h : IsChevTwoRankTwoModel X ∨ ∃ n : ℕ, 1 ≤ n ∧ IsSLThreeEpsAt X (2 ^ n)) :
    NumList46 (Nat.card X) := by
  rcases h with hM | ⟨n, hn, hSL⟩
  · rcases hM with ⟨n, hn, h⟩ | ⟨f, h⟩
    · have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
      rcases h with h | h | h | h | h
      · obtain ⟨φ⟩ := h
        exact num_projSL_two_even hn φ
      · obtain ⟨φ⟩ := h
        exact num_projSL_three hn (Or.inl rfl) φ
      · obtain ⟨φ⟩ := h
        exact num_projSU_three hn (Or.inl rfl) φ
      · obtain ⟨φ⟩ := h
        have h1 := CFSG.PGLModel.card_projSp_of_charTwo 2 (GaloisField 2 n)
        rw [hK, ← Nat.card_congr φ.toEquiv] at h1
        refine NumList46.sp4 ⟨2, n, 1, Nat.prime_two, hn, Or.inl rfl,
          Or.inl ⟨(Nat.even_pow' (by omega)).mpr even_two, rfl⟩, ?_⟩
        rw [mul_one, h1, show 2 ^ 2 = 4 by norm_num, show Icc 1 2 = {1, 2} by rfl,
          prod_pair (by norm_num)]
      · obtain ⟨φ⟩ := h
        have h1 := CFSG.RankThree.PartTwo.Sec11.KSListsProof.card_projSU_four_mul 2 n hn
        rw [← Nat.card_congr φ.toEquiv] at h1
        exact NumList46.u4 ⟨2, n, _, Nat.prime_two, hn, Or.inl rfl, Nat.gcd_dvd_left _ _,
          Nat.gcd_dvd_right _ _, h1⟩
    · rcases h with hG | hD | hS | hF | hT
      · obtain ⟨⟨-, hf, -⟩, -⟩ := id hG
        have h1 := (CFSG.Timmesfeld.card_chevalleyExceptionalModel_untwisted hG).1 rfl
        exact NumList46.g2 ⟨2, f, Nat.prime_two, hf, Or.inl rfl, h1⟩
      · obtain ⟨⟨-, hf, -⟩, -⟩ := id hD
        have h1 : Nat.card X = ordTrialityD4 (2 ^ f) :=
          CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hD
        exact NumList46.d4 ⟨f, hf, h1⟩
      · obtain ⟨-, a, ha, hf, h1⟩ := CFSG.GH74.card_of_suzukiModel hS
        exact NumList46.sz ⟨f, by omega, h1⟩
      · obtain ⟨⟨-, hf, -⟩, -⟩ := id hF
        exact NumList46.f4t ⟨f, hf, CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_twistedF4 hF⟩
      · refine NumList46.explicit ⟨17971200, by decide +kernel, ?_⟩
        rw [CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_Tits hT]
        exact (by decide : ordTits ∣ 17971200)
  · exact num_sl3eps Nat.prime_two hn (Or.inl rfl) hSL

end Certs

end CFSG.RankThree.PartTwo.Sec4.HeringPin

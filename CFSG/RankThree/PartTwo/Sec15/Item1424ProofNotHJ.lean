module

public import CFSG.RankThree.PartTwo.Sec15.Item1424ProofSteps
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14

theorem two_pow_dvd_card_of_isoLThreePi {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (h : Sec4.IsoLThreePi X 2 n) : 2 ^ (3 * n) ∣ Nat.card X := by
  have hodd : ∀ m : ℕ, Nat.Coprime (2 ^ (3 * n)) (Nat.gcd 3 m) := fun m =>
    Nat.Coprime.pow_left _ (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 m) (by norm_num))
  rcases h with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
  · have h1 := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 n)
    rw [GaloisField.card 2 n (by omega)] at h1
    rw [Nat.card_congr φ.toEquiv]
    refine (hodd (2 ^ n - 1)).dvd_of_dvd_mul_right ?_
    rw [h1]
    exact Dvd.dvd.mul_right (by rw [← pow_mul, mul_comm n 3]) _
  · have h1 := KFacts.KS14.card_projSU_three_mul_gcd 2 n hn
    rw [Nat.card_congr φ.toEquiv]
    refine (hodd (2 ^ n + 1)).dvd_of_dvd_mul_right ?_
    rw [h1]
    exact Dvd.dvd.mul_right (by rw [← pow_mul, mul_comm n 3]) _

variable {G : Type} [Group G] [Finite G]

theorem step1424NotHJ : Step1424NotHJ := by
  intro G _ _ A c L Y n hctx ⟨φ⟩
  have h := hctx.std
  have hD := h.toSec13Data
  have : IsSimpleGroup ↥L := hctx.simple
  have hJ1 : 1 < Nat.card CFSG.Blueprint.NativeSporadic.J2 := by
    rw [KFacts.KS14.card_nativeJ2]
    norm_num
  have hθ : aschbacherSolvableCore 3 ↥L = ⊥ := by
    have hn : (aschbacherSolvableCore 3 ↥L).Normal := aschbacherSolvableCore_normal 3 ↥L
    rcases hn.eq_bot_or_eq_top with h1 | h1
    · exact h1
    · exfalso
      have h2 := Nat.card_congr φ.toEquiv
      have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥L)
      have h4 : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 1 := by
        have h5 := Subgroup.index_eq_card (aschbacherSolvableCore 3 ↥L)
        rw [← h5, h1, Subgroup.index_top]
      omega
  have hLcard : Nat.card L = 604800 := by
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥L)
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeJ2, hθ, Subgroup.card_bot,
      mul_one] at h3
    exact h3
  let _ := kerAO2_normal hctx.le_normalizer
  obtain ⟨T, _, hT, ⟨ψ⟩⟩ := hctx.iso
  set P := CFSG.Open.pCoreOf 2 Y with hP
  have hPY : P ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Sec15.kerAO2 A Y : Subgroup ↥(A ⊔ Y))
  have hqT : Nat.card (↥(A ⊔ Y) ⧸ Sec15.kerAO2 A Y) = 3 * Nat.card T := by
    rw [Nat.card_congr ψ.toEquiv, Nat.card_prod, Nat.card_congr Multiplicative.toAdd,
      Nat.card_zmod]
  have hker : Nat.card (Sec15.kerAO2 A Y : Subgroup ↥(A ⊔ Y)) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hPY.trans le_sup_right)).toEquiv
  have hAY := Sec6.card_sup_mul_card_inf hctx.le_normalizer
  have hYLN : Y ⊓ L ≤ Subgroup.normalizer (P : Set G) :=
    inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
  have hYL := Sec6.card_sup_mul_card_inf hYLN
  rw [← hctx.eq_sup] at hYL
  rw [hqT, hker] at hq
  rw [hq, hD.card_eq] at hAY
  have hPpos : 0 < Nat.card P := Nat.card_pos
  have hdvd : Nat.card T ∣ 9 * Nat.card (Y ⊓ L : Subgroup G) := by
    refine ⟨Nat.card (A ⊓ Y : Subgroup G) * Nat.card ((Y ⊓ L) ⊓ P : Subgroup G), ?_⟩
    have e1 : 3 * (Nat.card T * (Nat.card (A ⊓ Y : Subgroup G) *
        Nat.card ((Y ⊓ L) ⊓ P : Subgroup G))) * Nat.card P =
        27 * Nat.card (Y ⊓ L : Subgroup G) * Nat.card P := by
      calc 3 * (Nat.card T * (Nat.card (A ⊓ Y : Subgroup G) *
            Nat.card ((Y ⊓ L) ⊓ P : Subgroup G))) * Nat.card P
          = 3 * Nat.card T * Nat.card P * Nat.card (A ⊓ Y : Subgroup G) *
            Nat.card ((Y ⊓ L) ⊓ P : Subgroup G) := by ring
        _ = 27 * (Nat.card Y * Nat.card ((Y ⊓ L) ⊓ P : Subgroup G)) := by rw [hAY]; ring
        _ = 27 * Nat.card (Y ⊓ L : Subgroup G) * Nat.card P := by rw [hYL]; ring
    have e2 := Nat.eq_of_mul_eq_mul_right hPpos e1
    omega
  have hYLd : Nat.card (Y ⊓ L : Subgroup G) ∣ 604800 :=
    hLcard ▸ Subgroup.card_dvd_of_le inf_le_right
  have h2T := two_pow_dvd_card_of_isoLThreePi (by have := hctx.four_le; omega) hT
  have h12 : 2 ^ 12 ∣ 2 ^ (3 * n) := Nat.pow_dvd_pow 2 (by have := hctx.four_le; omega)
  have hfin : 2 ^ 12 ∣ 9 * 604800 :=
    (h12.trans h2T).trans (hdvd.trans (Nat.mul_dvd_mul_left 9 hYLd))
  norm_num at hfin

end CFSG.RankThree.PartTwo.Sec15

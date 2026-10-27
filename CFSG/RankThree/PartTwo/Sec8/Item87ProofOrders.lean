module

public import CFSG.RankThree.PartTwo.Sec8.Item87Proof84
import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard
import CFSG.RankThree.PartTwo.KFacts.K71OddChar
import CFSG.RankThree.PartTwo.Sec21.Item229Orders
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Open (ordTrialityD4 ordG2 ordTwistedF4)

namespace Item87Proof

theorem not_two_pow_dvd_two_pow_mul_odd {a b o : ℕ} (hab : a < b) (ho : Odd o) :
    ¬ 2 ^ b ∣ 2 ^ a * o := by
  intro h
  have h1 : 2 ^ (a + 1) ∣ 2 ^ a * o := (Nat.pow_dvd_pow 2 (by omega)).trans h
  rw [pow_succ] at h1
  have h2 : 2 ∣ o := Nat.dvd_of_mul_dvd_mul_left (by positivity) h1
  exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr h2)

theorem odd_two_pow_sq_sub_one {f : ℕ} (hf : 1 ≤ f) : Odd ((2 ^ f) ^ 2 - 1) := by
  have h : Even ((2 ^ f) ^ 2) := by
    rw [← pow_mul]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have h1 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  exact Nat.Even.sub_odd h1 h odd_one

theorem odd_two_pow_cube_add_one {f : ℕ} (hf : 1 ≤ f) : Odd ((2 ^ f) ^ 3 + 1) := by
  have h : Even ((2 ^ f) ^ 3) := by
    rw [← pow_mul]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  exact h.add_one

theorem card_projSL_two_three {m : ℕ} (hm : 1 ≤ m) :
    Nat.card (projSL 2 (GaloisField 2 (3 * m))) = 2 ^ (3 * m) * ((2 ^ (3 * m)) ^ 2 - 1) :=
  Sec21.card_projSL_two _ (by omega)

theorem card_statedSU_three_two {F : Type} [Field F] [Finite F] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) :
    Nat.card (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ f) F) =
      2 ^ (3 * f) * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := 2 * f)
    (by rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm])
  rw [CFSG.SectionRank.OddCover.card_statedSU_three hF, mul_assoc, ← pow_mul, mul_comm f 3]

end Item87Proof


namespace Item87Proof

theorem two_pow_dvd_card_of_isGammaTypeL2 {X : Type} [Group X] {m : ℕ} (hm : 1 ≤ m)
    (h : IsGammaTypeL2 X m) : 2 ^ (9 * m) ∣ Nat.card X := by
  rcases h with ⟨q, hq, hp, hexp, ⟨e⟩⟩ | ⟨q, hp, hexp, hv, ⟨e⟩⟩ | ⟨⟨e⟩⟩ |
    ⟨F, hF, hFf, hFc, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv, Sec11.KSListsProof.card_trialityD4_carrier,
      TauCeti.PrimePower.card_def, hp, hexp, ordTrialityD4]
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _) _
    rw [← pow_mul]
    exact Nat.pow_dvd_pow 2 (by omega)
  · rw [Nat.card_congr e.toEquiv, Sec11.KSListsProof.card_G2_carrier, TauCeti.PrimePower.card_def,
      hp, hexp, ordG2]
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
    rw [← pow_mul]
    exact Nat.pow_dvd_pow 2 (by omega)
  · have h1 := (KFacts.padicValNat_card_and_card_cube_lt (by omega) e).1
    have h2 := pow_padicValNat_dvd (p := 2) (n := Nat.card X)
    rw [h1] at h2
    exact (Nat.pow_dvd_pow 2 (by omega)).trans h2
  · rw [Nat.card_congr e.toEquiv, card_statedSU_three_two hFc]
    exact Dvd.dvd.mul_right (Nat.pow_dvd_pow 2 (by omega)) _
  · rw [Nat.card_congr e.toEquiv, Sec21.card_projSp_two (by omega),
      Sec21.ordBC_two_eq (by omega)]
    refine Dvd.dvd.mul_right ?_ _
    rw [← pow_mul]
    exact Nat.pow_dvd_pow 2 (by omega)

theorem two_pow_dvd_card_of_isGammaTypeRee {X : Type} [Group X] {m : ℕ}
    (h : IsGammaTypeRee X m) : 2 ^ (36 * m) ∣ Nat.card X := by
  obtain ⟨k, hk, hkm, ⟨e⟩⟩ := h
  have hc := CFSG.AGLEmbedding.card_catGroup_reeF4 (d := ⟨.reeF4 k, hk⟩) (m := k) rfl
  rw [Nat.card_congr e.toEquiv]
  change 2 ^ (36 * m) ∣ Nat.card (CFSG.AGLEmbedding.CatGroup ⟨.reeF4 k, hk⟩)
  rw [hc, ordTwistedF4, hkm]
  refine Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _) _) _
  rw [← pow_mul]
  exact Nat.pow_dvd_pow 2 (by omega)

end Item87Proof

theorem kF84Proper : KF84Proper := by
  intro X _ m hm
  refine ⟨fun hRee ⟨F, hF, hFf, hFc, ⟨φ⟩⟩ => ?_, fun hL2 ⟨φ⟩ => ?_⟩
  · have h36 := Item87Proof.two_pow_dvd_card_of_isGammaTypeRee hRee
    rw [Nat.card_congr φ.toEquiv, Item87Proof.card_statedSU_three_two hFc] at h36
    exact Item87Proof.not_two_pow_dvd_two_pow_mul_odd (by omega)
      ((Item87Proof.odd_two_pow_sq_sub_one (by omega)).mul
        (Item87Proof.odd_two_pow_cube_add_one (by omega))) h36
  · have h9 := Item87Proof.two_pow_dvd_card_of_isGammaTypeL2 hm hL2
    rw [Nat.card_congr φ.toEquiv, Item87Proof.card_projSL_two_three hm] at h9
    exact Item87Proof.not_two_pow_dvd_two_pow_mul_odd (by omega)
      (Item87Proof.odd_two_pow_sq_sub_one (by omega)) h9

theorem pair84Sym_of_gamma (hΓ : Pair84Gamma) : Pair84Sym :=
  pair84Sym_of hΓ kF84Proper

end CFSG.RankThree.PartTwo.Sec8

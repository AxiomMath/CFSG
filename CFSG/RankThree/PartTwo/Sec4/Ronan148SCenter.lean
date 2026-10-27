module

public import CFSG.RankThree.PartTwo.Sec4.T444.DiagGriess
public import CFSG.RankThree.PartTwo.Sec4.Item426A6Proof
public import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.Models.PGLOrders
public import CFSG.Sporadic.ON

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem center_eq_bot_of_card {L : Type} [Group L] [Finite L]
    (hS : SectionFourHyp L)
    (hL : IsQuasisimple L) (hZ3 : IsPGroup 3 (Subgroup.center L)) {N : ℕ}
    (hN : Nat.card (L ⧸ Subgroup.center L) = N)
    (hSL : ∀ q, 2 ≤ q → q ^ 3 ∣ N → N * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)))
    (hSU : ∀ q, 2 ≤ q → q ^ 3 ∣ N → N * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)))
    (h5 : 5 ∣ N) (h6 : N ≠ 360) (h7 : N ≠ 2520) (hU : N ≠ 3265920) (hM22 : N ≠ 443520)
    (hJ3 : N ≠ 50232960) (hMcL : N ≠ 898128000) (hON : N ≠ 460815505920) :
    Subgroup.center L = ⊥ := by
  by_contra hne
  have h3 : 3 ∣ Nat.card (Subgroup.center L) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3)).1 hZ3
    have h1 : 1 < Nat.card (Subgroup.center L) :=
      (Subgroup.one_lt_card_iff_ne_bot (H := Subgroup.center L)).2 hne
    rw [hn] at h1 ⊢
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp at h1
    exact dvd_pow_self 3 hn0
  have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [CFSG.RankThree.PartTwo.KFacts.KS14.card_alternatingGroup_fin (n := 6) (by norm_num)]
    decide
  have hA7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [CFSG.RankThree.PartTwo.KFacts.KS14.card_alternatingGroup_fin (n := 7) (by norm_num)]
    decide
  rcases diag_item43_holds L hS hL h3 with
    hI | hSix | hSeven | hG2 | hU43 | hM22' | hJ3' | hMcL' | hON'
  · obtain ⟨p, e, hp, -, hiso⟩ := hI
    exact CFSG.RankThree.PartTwo.KFacts.KS14.not_isoLThreePi_of_card hN hSL hSU p e hiso
  · obtain ⟨φ⟩ := hSix
    exact h6 (hN.symm.trans ((Nat.card_congr φ.toEquiv).trans hA6))
  · obtain ⟨φ⟩ := hSeven
    exact h7 (hN.symm.trans ((Nat.card_congr φ.toEquiv).trans hA7))
  · exact CFSG.RankThree.PartTwo.Sec4.Item426.not_five_dvd_card_of_G2_three hG2
      (by rw [hN]; exact h5)
  · obtain ⟨φ⟩ := hU43
    exact hU (hN.symm.trans
      ((Nat.card_congr φ.toEquiv).trans CFSG.PGLModel.card_projSU_four_three))
  · obtain ⟨φ⟩ := hM22'
    exact hM22 (hN.symm.trans
      ((Nat.card_congr φ.toEquiv).trans CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeM22))
  · obtain ⟨φ⟩ := hJ3'
    exact hJ3 (hN.symm.trans ((Nat.card_congr φ.toEquiv).trans CFSG.Sporadic.J3.card_J3))
  · obtain ⟨φ⟩ := hMcL'
    exact hMcL (hN.symm.trans ((Nat.card_congr φ.toEquiv).trans CFSG.Sporadic.McL.card_McL))
  · obtain ⟨φ⟩ := hON'
    exact hON (hN.symm.trans ((Nat.card_congr φ.toEquiv).trans CFSG.Sporadic.ON.card_ON))

end CFSG.RankThree.PartTwo.Sec4.Ronan148S

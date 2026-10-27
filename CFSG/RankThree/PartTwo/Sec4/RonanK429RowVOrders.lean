module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVTools
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemL43
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherU54

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace RowV

theorem gcd_three_pow_sub_one {e : ℕ} (he : 1 ≤ e) : Nat.gcd 3 (3 ^ e - 1) = 1 := by
  have h1 : 3 ∣ 3 ^ e := dvd_pow_self 3 (by omega)
  have h2 : 1 ≤ 3 ^ e := Nat.one_le_pow _ _ (by norm_num)
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)

theorem gcd_three_pow_add_one {e : ℕ} (he : 1 ≤ e) : Nat.gcd 3 (3 ^ e + 1) = 1 := by
  have h1 : 3 ∣ 3 ^ e := dvd_pow_self 3 (by omega)
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)

theorem card_projSL_three_char_three {e : ℕ} (he : 1 ≤ e) :
    Nat.card (projSL 3 (GaloisField 3 e)) =
      (3 ^ e) ^ 3 * (((3 ^ e) ^ 2 - 1) * ((3 ^ e) ^ 3 - 1)) := by
  have h := KS14.card_projSL_three_mul_gcd (GaloisField 3 e)
  rw [GaloisField.card 3 e (by omega), gcd_three_pow_sub_one he, mul_one] at h
  exact h

theorem card_projSU_three_char_three {e : ℕ} (he : 1 ≤ e) :
    Nat.card (projSU 3 3 e) = (3 ^ e) ^ 3 * (((3 ^ e) ^ 2 - 1) * ((3 ^ e) ^ 3 + 1)) := by
  have h := KS14.card_projSU_three_mul_gcd 3 e he
  rw [gcd_three_pow_add_one he, mul_one] at h
  exact h

theorem noCfgS429_projSL_three_char_three {S : Type} [Group S] [Finite S] {e : ℕ}
    (he : e = 1 ∨ e = 3) (φ : S ≃* projSL 3 (GaloisField 3 e)) : NoCfgS429 S := by
  have hS := (Nat.card_congr φ.toEquiv).trans (card_projSL_three_char_three (by omega))
  rcases he with rfl | rfl
  · exact noCfgS429_of_card (B := 4) hS.dvd (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact noCfgS429_of_card (B := 32) hS.dvd (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

theorem noCfgS429_projSU_three_char_three {S : Type} [Group S] [Finite S] {e : ℕ}
    (he1 : 1 ≤ e) (he3 : e ≤ 3) (φ : S ≃* projSU 3 3 e) : NoCfgS429 S := by
  have hS := (Nat.card_congr φ.toEquiv).trans (card_projSU_three_char_three he1)
  obtain rfl | rfl | rfl : e = 1 ∨ e = 2 ∨ e = 3 := by omega
  · exact noCfgS429_of_card (B := 4) hS.dvd (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact noCfgS429_of_card (B := 11) hS.dvd (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact noCfgS429_of_card (B := 32) hS.dvd (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

theorem card_projSL_four_three_dvd :
    Nat.card (projSL 4 (GaloisField 3 1)) ∣ 3 ^ 6 * 16640 := by
  rw [Nat.card_congr Item434RemL43.projSLEquivPSL43.toEquiv]
  have hsplit : Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 3)) =
      Nat.card Item434RemL43.PSL43 * Nat.card (scalars 4 (ZMod 3)) :=
    (scalars 4 (ZMod 3)).card_eq_card_quotient_mul_card_subgroup
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 3)) = 3 ^ 6 * 16640 := by
    rw [card_SL_eq (K := ZMod 3) (by norm_num : 1 ≤ 4), Nat.card_zmod]
    first
    | decide
    | rfl
    | norm_num [Finset.prod_Icc_succ_top]
  rw [← hSL, hsplit]
  exact Dvd.intro _ rfl

theorem noCfgS429_projSL_four_three {S : Type} [Group S] [Finite S]
    (φ : S ≃* projSL 4 (GaloisField 3 1)) : NoCfgS429 S :=
  noCfgS429_of_card (N := 3 ^ 6 * 16640) (B := 9)
    (by rw [Nat.card_congr φ.toEquiv]; exact card_projSL_four_three_dvd)
    (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem noCfgS429_projSU_five_four {S : Type} [Group S] [Finite S]
    (φ : S ≃* projSU 5 2 2) : NoCfgS429 S :=
  noCfgS429_of_card (B := 63)
    ((Nat.card_congr φ.toEquiv).trans Item434SmallTwoOther.U54.card_U54).dvd
    (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end RowV

end CFSG.RankThree.PartTwo.Sec4.RonanK429

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.BranchHelpers
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.Pow3Classical
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.Pow3OmegaMinus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.Pow3OmegaPlusSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo

private theorem natOrderClass_of_natural_low {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {n : ℕ}
    (h : (IsSp4 ↥H n ∧ NatSpn H ⊤ ⊥ 4 n) ∨
      (IsSLn ↥H 3 n ∧ BinaryNaturalSL H ⊤ ⊥ 3 n) ∨
      (∃ a : ℕ, n = 2 * a ∧ IsSUn ↥H 4 a ∧ NatSUn H ⊤ ⊥ 4 a)) :
    NatOrderClass H n := by
  rcases h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨a, hn, -, h⟩
  · obtain ⟨-, K, hKfield, hKfin, hKcard, hR⟩ := h
    rw [show (4 / 2 : ℕ) = 2 from rfl] at hR
    letI : Field K := hKfield
    letI : Finite K := hKfin
    exact natOrderClass_of_pow_three_dvd hKcard hR pow_three_dvd_card_statedSp_two
  · obtain ⟨K, hKfield, hKfin, hKcard, hR⟩ := h
    letI : Field K := hKfield
    letI : Finite K := hKfin
    exact natOrderClass_of_pow_three_dvd hKcard hR pow_three_dvd_card_statedSL_three
  · subst hn
    obtain ⟨K, hKfield, hKfin, hKcard, hR⟩ := h
    letI : Field K := hKfield
    letI : Finite K := hKfin
    have hK' : Nat.card K = 2 ^ (2 * a) := by rw [hKcard, ← pow_mul, mul_comm]
    exact natOrderClass_of_pow_three_dvd hK' hR (pow_three_dvd_card_statedSU_four hKcard)

private theorem natOrderClass_of_natural_high {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {n : ℕ}
    (h : (IsOmegaMinus ↥H 6 n ∧ NatOmegaMinus H ⊤ ⊥ 6 n) ∨
      (IsSLn ↥H 4 n ∧ BinaryNaturalSL H ⊤ ⊥ 4 n) ∨
      (IsOmegaPlus ↥H 6 n ∧ NatOmegaPlus H ⊤ ⊥ 6 n) ∨
      (IsSpn ↥H 6 n ∧ NatSpn H ⊤ ⊥ 6 n) ∨
      (IsOmega8m ↥H n ∧ NatOmegaMinus H ⊤ ⊥ 8 n)) :
    NatOrderClass H n := by
  rcases h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
  · obtain ⟨-, K, hKfield, hKfin, b, c, hKcard, hirr, hR⟩ := h
    rw [show (6 / 2 : ℕ) = 3 from rfl] at hR
    letI : Field K := hKfield
    letI : Finite K := hKfin
    haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
    exact natOrderClass_of_pow_three_dvd hKcard hR
      (pow_three_dvd_card_statedOmega_quadMinus_three hirr)
  · obtain ⟨K, hKfield, hKfin, hKcard, hR⟩ := h
    letI : Field K := hKfield
    letI : Finite K := hKfin
    exact natOrderClass_of_pow_three_dvd hKcard hR pow_three_dvd_card_statedSL_four
  · obtain ⟨-, K, hKfield, hKfin, hKcard, hR⟩ := h
    rw [show (6 / 2 : ℕ) = 3 from rfl] at hR
    letI : Field K := hKfield
    letI : Finite K := hKfin
    haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
    exact natOrderClass_of_pow_three_dvd hKcard hR pow_three_dvd_card_statedOmega_quadPlus_three
  · obtain ⟨-, K, hKfield, hKfin, hKcard, hR⟩ := h
    rw [show (6 / 2 : ℕ) = 3 from rfl] at hR
    letI : Field K := hKfield
    letI : Finite K := hKfin
    exact natOrderClass_of_pow_three_dvd hKcard hR pow_three_dvd_card_statedSp_three
  · obtain ⟨-, K, hKfield, hKfin, b, c, hKcard, hirr, hR⟩ := h
    rw [show (8 / 2 : ℕ) = 4 from rfl] at hR
    letI : Field K := hKfield
    letI : Finite K := hKfin
    haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
    exact natOrderClass_of_pow_three_dvd hKcard hR
      (pow_three_dvd_card_statedOmega_quadMinus_four hirr)

theorem natOrderClass_of_natural {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {n : ℕ}
    (h : IsNaturalClassicalModule H n) : NatOrderClass H n := by
  rcases h with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
  · exact natOrderClass_of_binaryNaturalSL_two h1.2
  · exact natOrderClass_of_natOmegaMinus_four h2.2
  · exact natOrderClass_of_natOmegaPlus_four h3.2
  · exact natOrderClass_of_natural_low (Or.inl h4)
  · exact natOrderClass_of_natural_low (Or.inr (Or.inl h5))
  · exact natOrderClass_of_natural_low (Or.inr (Or.inr h6))
  · exact natOrderClass_of_natural_high (Or.inl h7)
  · exact natOrderClass_of_natural_high (Or.inr (Or.inl h8))
  · exact natOrderClass_of_natural_high (Or.inr (Or.inr (Or.inl h9)))
  · exact natOrderClass_of_natural_high (Or.inr (Or.inr (Or.inr (Or.inl h10))))
  · exact natOrderClass_of_natural_high (Or.inr (Or.inr (Or.inr (Or.inr h11))))

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

end

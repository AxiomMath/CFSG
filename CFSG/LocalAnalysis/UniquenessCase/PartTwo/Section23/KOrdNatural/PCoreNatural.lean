module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.Realize
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.PCoreSL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.PCoreSp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.PCoreSU
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.PCoreOmegaPlus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.PCoreOmegaMinus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin

private theorem pCore_eq_bot_of_binaryNaturalSL {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {n d : ℕ} (h : BinaryNaturalSL H ⊤ ⊥ d n) :
    CFSG.pCore 2 ↥H = ⊥ := by
  obtain ⟨K, hKf, hKfin, hKcard, hR⟩ := h
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  exact natRealizes_pCore_eq_bot 2 hR (pCore_statedSL_eq_bot 2 d)

private theorem pCore_eq_bot_of_natOmegaMinus_four {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {n : ℕ} (h : NatOmegaMinus H ⊤ ⊥ 4 n) :
    CFSG.pCore 2 ↥H = ⊥ := by
  obtain ⟨-, K, hKf, hKfin, b, c, hKcard, hirr, hR⟩ := h
  have h42 : (4 / 2 : ℕ) = 2 := by norm_num
  rw [h42] at hR
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  exact natRealizes_pCore_eq_bot 2 hR
    (pCore_statedOmega_minus_eq_bot 2 (m := 2) (by norm_num) hirr)

private theorem pCore_eq_bot_of_natOmegaPlus_four {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {n : ℕ} (h : NatOmegaPlus H ⊤ ⊥ 4 n) :
    CFSG.pCore 2 ↥H = ⊥ := by
  obtain ⟨-, K, hKf, hKfin, hKcard, hR⟩ := h
  have h42 : (4 / 2 : ℕ) = 2 := by norm_num
  rw [h42] at hR
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  exact natRealizes_pCore_eq_bot 2 hR (pCore_statedOmega_plus_eq_bot 2 (m := 2) (by norm_num))

private theorem pCore_eq_bot_of_natSpn_four {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {n : ℕ} (h : NatSpn H ⊤ ⊥ 4 n) :
    CFSG.pCore 2 ↥H = ⊥ := by
  obtain ⟨-, K, hKf, hKfin, hKcard, hR⟩ := h
  have h42 : (4 / 2 : ℕ) = 2 := by norm_num
  rw [h42] at hR
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  exact natRealizes_pCore_eq_bot 2 hR (pCore_statedSp_eq_bot 2 2)

private theorem pCore_eq_bot_of_natSUn_four {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {a : ℕ} (h : NatSUn H ⊤ ⊥ 4 a) :
    CFSG.pCore 2 ↥H = ⊥ := by
  obtain ⟨K, hKf, hKfin, hKcard, hR⟩ := h
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hK' : Nat.card K = 2 ^ (2 * a) := by
    rw [hKcard, pow_two, ← pow_add, two_mul]
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK'
  exact natRealizes_pCore_eq_bot 2 hR (pCore_statedSU_eq_bot 2 hKcard 4)

private theorem pCore_eq_bot_of_natOmegaMinus_six {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {n : ℕ} (h : NatOmegaMinus H ⊤ ⊥ 6 n) :
    CFSG.pCore 2 ↥H = ⊥ := by
  obtain ⟨-, K, hKf, hKfin, b, c, hKcard, hirr, hR⟩ := h
  have h63 : (6 / 2 : ℕ) = 3 := by norm_num
  rw [h63] at hR
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  exact natRealizes_pCore_eq_bot 2 hR
    (pCore_statedOmega_minus_eq_bot 2 (m := 3) (by norm_num) hirr)

private theorem pCore_eq_bot_of_natOmegaPlus_six {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {n : ℕ} (h : NatOmegaPlus H ⊤ ⊥ 6 n) :
    CFSG.pCore 2 ↥H = ⊥ := by
  obtain ⟨-, K, hKf, hKfin, hKcard, hR⟩ := h
  have h63 : (6 / 2 : ℕ) = 3 := by norm_num
  rw [h63] at hR
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  exact natRealizes_pCore_eq_bot 2 hR (pCore_statedOmega_plus_eq_bot 2 (m := 3) (by norm_num))

private theorem pCore_eq_bot_of_natSpn_six {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {n : ℕ} (h : NatSpn H ⊤ ⊥ 6 n) :
    CFSG.pCore 2 ↥H = ⊥ := by
  obtain ⟨-, K, hKf, hKfin, hKcard, hR⟩ := h
  have h63 : (6 / 2 : ℕ) = 3 := by norm_num
  rw [h63] at hR
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  exact natRealizes_pCore_eq_bot 2 hR (pCore_statedSp_eq_bot 2 3)

private theorem pCore_eq_bot_of_natOmegaMinus_eight {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {n : ℕ} (h : NatOmegaMinus H ⊤ ⊥ 8 n) :
    CFSG.pCore 2 ↥H = ⊥ := by
  obtain ⟨-, K, hKf, hKfin, b, c, hKcard, hirr, hR⟩ := h
  have h84 : (8 / 2 : ℕ) = 4 := by norm_num
  rw [h84] at hR
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  exact natRealizes_pCore_eq_bot 2 hR
    (pCore_statedOmega_minus_eq_bot 2 (m := 4) (by norm_num) hirr)

theorem kOrd_pCore_eq_bot {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {n : ℕ}
    (h : IsNaturalClassicalModule H n) : CFSG.pCore 2 ↥H = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold IsNaturalClassicalModule at h
  rcases h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨a, -, -, h⟩ | ⟨-, h⟩ |
    ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
  · exact pCore_eq_bot_of_binaryNaturalSL h
  · exact pCore_eq_bot_of_natOmegaMinus_four h
  · exact pCore_eq_bot_of_natOmegaPlus_four h
  · exact pCore_eq_bot_of_natSpn_four h
  · exact pCore_eq_bot_of_binaryNaturalSL h
  · exact pCore_eq_bot_of_natSUn_four h
  · exact pCore_eq_bot_of_natOmegaMinus_six h
  · exact pCore_eq_bot_of_binaryNaturalSL h
  · exact pCore_eq_bot_of_natOmegaPlus_six h
  · exact pCore_eq_bot_of_natSpn_six h
  · exact pCore_eq_bot_of_natOmegaMinus_eight h

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

end

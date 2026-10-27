module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.Transport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.OmegaMinusFour
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.OmegaMinusSix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.OmegaMinusEight
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.FixedLineOmega
import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem borelIrr_of_omegaMinusFour {W : Type} [CommGroup W] [Finite W]
    {H S P : Subgroup (MulAut W)} {n : ℕ} (h : NatOmegaMinus H ⊤ ⊥ 4 n)
    (hS : IsSylowIn 2 S H) (hNP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPH : P ≤ H)
    (hP : ¬ P ≤ stabSub (fixV S)) {J : Subgroup W} (hJ : J ≤ fixV S)
    (hstab : StableUnder (Hinf P ⊓ normalizer (S : Set (MulAut W))) J) :
    J = ⊥ ∨ J = fixV S := by
  obtain ⟨-, K, hField, hFinite, b, c, hK, hirr, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  rw [show 4 / 2 = 2 by norm_num] at hR
  have he0 : (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (2 - 1))) 1 :
      Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) ≠ 0 := by
    intro h0
    have h1 : (1 : K) = 0 := by
      simpa using congr_fun h0 (Sum.inl (⟨0, by omega⟩ : Fin (2 - 1)))
    exact one_ne_zero h1
  exact borelIrr_of_hasBorelScalars hR he0
    (KTabD.sylowFixedLine_omegaMinus (K := K) (m := 2) (by norm_num) hirr)
    (hasBorelScalars_omegaMinusFour hirr) hS hNP hPH hP hJ hstab

theorem borelIrr_of_omegaMinusSix {W : Type} [CommGroup W] [Finite W]
    {H S P : Subgroup (MulAut W)} {n : ℕ} (h : NatOmegaMinus H ⊤ ⊥ 6 n)
    (hS : IsSylowIn 2 S H) (hNP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPH : P ≤ H)
    (hP : ¬ P ≤ stabSub (fixV S)) {J : Subgroup W} (hJ : J ≤ fixV S)
    (hstab : StableUnder (Hinf P ⊓ normalizer (S : Set (MulAut W))) J) :
    J = ⊥ ∨ J = fixV S := by
  obtain ⟨-, K, hField, hFinite, b, c, hK, hirr, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  rw [show 6 / 2 = 3 by norm_num] at hR
  have he0 : (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (3 - 1))) 1 :
      Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) ≠ 0 := by
    intro h0
    have h1 : (1 : K) = 0 := by
      simpa using congr_fun h0 (Sum.inl (⟨0, by omega⟩ : Fin (3 - 1)))
    exact one_ne_zero h1
  have hline := KTabD.sylowFixedLine_omegaMinus (K := K) (m := 3) (by norm_num) hirr
  exact borelIrr_of_hasBorelScalars hR he0 hline
    (hasBorelScalars_of_four_le hline hK (fun h4 =>
      hasBorelScalars_of_hasRootSL2 h4 (hasRootSL2_omegaMinusSix hirr h4)))
    hS hNP hPH hP hJ hstab

theorem borelIrr_of_omegaMinusEight {W : Type} [CommGroup W] [Finite W]
    {H S P : Subgroup (MulAut W)} {n : ℕ} (h : NatOmegaMinus H ⊤ ⊥ 8 n)
    (hS : IsSylowIn 2 S H) (hNP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPH : P ≤ H)
    (hP : ¬ P ≤ stabSub (fixV S)) {J : Subgroup W} (hJ : J ≤ fixV S)
    (hstab : StableUnder (Hinf P ⊓ normalizer (S : Set (MulAut W))) J) :
    J = ⊥ ∨ J = fixV S := by
  obtain ⟨-, K, hField, hFinite, b, c, hK, hirr, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  rw [show 8 / 2 = 4 by norm_num] at hR
  have he0 : (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin (4 - 1))) 1 :
      Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) ≠ 0 := by
    intro h0
    have h1 : (1 : K) = 0 := by
      simpa using congr_fun h0 (Sum.inl (⟨0, by omega⟩ : Fin (4 - 1)))
    exact one_ne_zero h1
  have hline := KTabD.sylowFixedLine_omegaMinus (K := K) (m := 4) (by norm_num) hirr
  exact borelIrr_of_hasBorelScalars hR he0 hline
    (hasBorelScalars_of_four_le hline hK (fun h4 =>
      hasBorelScalars_of_hasRootSL2 h4 (hasRootSL2_omegaMinusEight hirr)))
    hS hNP hPH hP hJ hstab

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.Transport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.OmegaPlusFour
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.OmegaPlusSix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.Perfect
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.PlusTwoNotPerfect
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.SylowLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KGenO6p.FixedLine
import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

open CFSG.Open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

theorem borelIrr_of_omegaPlusFour {W : Type} [CommGroup W] [Finite W]
    {H S P : Subgroup (MulAut W)} {n : ℕ} (h : NatOmegaPlus H ⊤ ⊥ 4 n) (hperf : ⁅H, H⁆ = H)
    (hS : IsSylowIn 2 S H) (hNP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPH : P ≤ H)
    (hP : ¬ P ≤ stabSub (fixV S)) {J : Subgroup W} (hJ : J ≤ fixV S)
    (hstab : StableUnder (Hinf P ⊓ normalizer (S : Set (MulAut W))) J) :
    J = ⊥ ∨ J = fixV S := by
  obtain ⟨-, K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  by_cases hK2 : 2 < Nat.card K
  · have hn2 : 2 ≤ n := by
      rcases n with _ | _ | k
      · rw [pow_zero] at hK
        omega
      · rw [pow_one] at hK
        omega
      · omega
    have hK4 : 4 ≤ Nat.card K := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
        _ = Nat.card K := hK.symm
    rw [show 4 / 2 = 2 by norm_num] at hR
    have he0 : KTabC.e1P K ≠ 0 := by simp [KTabC.e1P]
    refine borelIrr_of_hasBorelScalars (Γ := StatedOmega (StatedQuadPlus 2 K))
      (e₀ := KTabC.e1P K) hR he0 (KTabC.sylowFixedLine_plus K hK4) ?_ hS hNP hPH hP hJ hstab
    exact hasBorelScalars_omegaPlusFour hK4
  · have hKge : 2 ≤ Nat.card K := by
      have := Finite.one_lt_card (α := K)
      omega
    have hKeq : Nat.card K = 2 := le_antisymm (not_lt.mp hK2) hKge
    rw [show 4 / 2 = 2 by norm_num] at hR
    have htop : commutator ↥(StatedOmega (StatedQuadPlus 2 K)) = ⊤ :=
      KTabA.commutator_eq_top_of_realizes hR hperf
    exact absurd htop (KTabA.commutator_statedOmega_plus_two_ne_top hKeq)

theorem borelIrr_of_omegaPlusSix {W : Type} [CommGroup W] [Finite W]
    {H S P : Subgroup (MulAut W)} {n : ℕ} (h : NatOmegaPlus H ⊤ ⊥ 6 n)
    (hS : IsSylowIn 2 S H) (hNP : H ⊓ normalizer (S : Set (MulAut W)) ≤ P) (hPH : P ≤ H)
    (hP : ¬ P ≤ stabSub (fixV S)) {J : Subgroup W} (hJ : J ≤ fixV S)
    (hstab : StableUnder (Hinf P ⊓ normalizer (S : Set (MulAut W))) J) :
    J = ⊥ ∨ J = fixV S := by
  obtain ⟨-, K, hField, hFinite, hK, hR⟩ := h
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  rw [show 6 / 2 = 3 by norm_num] at hR
  have he0 : (Pi.single (Sum.inl 0) (1 : K) : Fin 3 ⊕ Fin 3 → K) ≠ 0 := by
    intro h0
    have h1 : (1 : K) = 0 := by simpa using congr_fun h0 (Sum.inl 0)
    exact one_ne_zero h1
  have hline : KTabC.SylowFixedLine (StatedOmega (StatedQuadPlus 3 K))
      (Pi.single (Sum.inl 0) (1 : K) : Fin 3 ⊕ Fin 3 → K) :=
    KGenO6pProof.sylowFixedLine_omegaPlusSix K
  have hmodel : HasBorelScalars (StatedOmega (StatedQuadPlus 3 K))
      (Pi.single (Sum.inl 0) (1 : K) : Fin 3 ⊕ Fin 3 → K) :=
    hasBorelScalars_of_four_le hline hK
      (fun h4 => hasBorelScalars_of_hasRootSL2 h4 hasRootSL2_omegaPlusSix)
  exact borelIrr_of_hasBorelScalars hR he0 hline hmodel hS hNP hPH hP hJ hstab

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

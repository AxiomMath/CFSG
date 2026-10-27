module

public import CFSG.Sporadic.Fi24I301.Elements

public section

namespace CFSG.Sporadic.Fi24I301

open CFSG.Sporadic.FischerOddCore
  CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime CFSG.EvenSporadicStandard.TwoFi22.DS81


theorem card_fi24P_inf_centralizer_psi :
    Nat.card ↥(fi24P ⊓ Subgroup.centralizer
      ({fi24Psi ⟨dJ, xJ_mem 0⟩} : Set (Equiv.Perm (Fin 378)))) = 5832 := by
  rw [fi24Psi_xJ 0, fi24PLetterG_eq]
  exact rowFacts.2.2.2.2.2

end CFSG.Sporadic.Fi24I301

module

public import CFSG.Open.GoldschmidtStronglyClosedAbelianMilestoneDefs
import CFSG.Goldschmidt.OddCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open

theorem goldschmidtOddCore_eq_bot_of_normal {X : Type} [Group X] [Finite X]
    (hX : ∀ N : Subgroup X, N.Normal → Odd (Nat.card N) → N = ⊥) {M : Subgroup X}
    (hM : M.Normal) : goldschmidtOddCore M = ⊥ := by
  haveI : M.Normal := hM
  rw [CFSG.Goldschmidt.goldschmidtOddCore_eq_pPrimeCore M]
  have hodd : Odd (Nat.card ((CFSG.pPrimeCore 2 ↥M).map M.subtype)) := by
    rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hbot : (CFSG.pPrimeCore 2 ↥M).map M.subtype = ⊥ := hX _ inferInstance hodd
  exact (Subgroup.map_eq_bot_iff_of_injective (CFSG.pPrimeCore 2 ↥M)
    M.subtype_injective).mp hbot

end CFSG.StandardType.FrameRoute.FS81

end

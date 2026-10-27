module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowHS119Transport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsB
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowFstarLift
import CFSG.Quasithin.Background.RonanE42Small
import CFSG.Quasithin.EmptyFaithful.ModHHSEl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1
  CFSG.QuasithinUnique.Bridge.HSExcl CFSG.Quasithin.B45Exc.HSRu CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore

theorem w4Lem11_9_holds :
    W4Lem11_9 := by
  intro W _ _ _ Y L T hLY hLn hF hq _ hs _ hT hfix
  obtain ⟨e₀⟩ := hs
  have hZ : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : e₀ x ∈ Subgroup.center (NativeSporadic.Carrier .HS) := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro y
      obtain ⟨z, rfl⟩ := e₀.surjective y
      rw [← map_mul, ← map_mul, hx z]
    rw [CFSG.Quasithin.ModH.HSEl.center_eq_bot_hs, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.2 (e₀.injective (hx'.trans (map_one e₀).symm))
  let e : (↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .HS :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e₀)
  have hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).1 hLn
  obtain ⟨Φ, hΦ⟩ := hs_aut_model
  exact RonanE42.aParam_le_of_aSet_empty Y 2 (W4Row.HS119.not_mem_aSet_three_of_lift hLY
    (W4Row.liftOfFstar hLY hF hq.1 hY e hZ hsP_le_hsR Φ hsEquivC hΦ) hT hfix)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

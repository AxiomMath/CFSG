module

public import CFSG.Sporadic.SuzRecog.GluingProof2
public import CFSG.Sporadic.SuzRecog.LevelTwoCover
public import CFSG.Sporadic.SuzRecog.ChartTransfer
public import CFSG.Sporadic.SuzRecog.LevelTwoCoverW

public section

namespace CFSG.Sporadic.SuzRecog

open Subgroup CFSG.Sporadic.SuzOddCore LevelTwo LevelTwoCover


theorem suzLevelTwoGluing_of_open
    (hp : ∀ x ∈ coverData.Xp, (proj x : Equiv.Perm (Fin 1782)) ∈ invE 1)
    (hp' : ∀ y (hy : y ∈ Model.Crho1), y ∈ invE 1 → ∃ x ∈ coverData.Xp, proj x = ⟨y, hy⟩)
    (hq : ∀ x ∈ coverData.Xq, (proj x : Equiv.Perm (Fin 1782)) ∈ Model.NR0)
    (hq' : ∀ y (hy : y ∈ Model.Crho1), y ∈ Model.NR0 → ∃ x ∈ coverData.Xq, proj x = ⟨y, hy⟩)
    (hplus : ∀ x ∈ coverData.Xp, x ∈ coverData.Xq →
      (proj x : Equiv.Perm (Fin 1782)) ∈ B0Plus)
    (he : ∀ x ∈ coverData.Xe, (proj x : Equiv.Perm (Fin 1782)) ∈ centM (suzInv 1 * aP p1))
    (hG4 : SuzB0Gluing) (hdich : MixedCellDichotomy coverData proj (suzInv 1 * aP p1))
    (hroot : RootTwistTrivial' coverData proj d (suzInv 1 * aP p1)) (hex : B0TwistExcluded) :
    SuzLevelTwoGluing := by
  have hchart : SuzChartTransfer (suzInv 1 * aP p1) := by
    rw [w_eq_conj]
    exact suzChartTransfer_conj wC_mem
  exact suzLevelTwoGluing_of_cover₂ coverData proj proj_surjective d ker_proj hp hp' hq hq' hplus
    he hG4 hchart hdich hroot hex

end CFSG.Sporadic.SuzRecog

module

public import CFSG.Sporadic.SuzRecog.LevelTwoGluingOpen
public import CFSG.Sporadic.SuzRecog.LevelTwoCoverMaps

public section

namespace CFSG.Sporadic.SuzRecog

open CFSG.Sporadic.SuzOddCore LevelTwo LevelTwoCover

@[expose] def SuzMixedCells :
    Prop :=
  MixedCellDichotomy coverData proj (suzInv 1 * aP p1)

theorem suzLevelTwoGluing_of_leaf
    (hG4 : SuzB0Gluing) (hdich : SuzMixedCells)
    (hroot : RootTwistTrivial' coverData proj d (suzInv 1 * aP
        p1)) (hex : B0TwistExcluded) : SuzLevelTwoGluing :=
  suzLevelTwoGluing_of_open (proj_mem_invE coverData rfl)
    (exists_proj_eq_of_mem_invE coverData rfl) (proj_mem_NR0 coverData rfl)
    (exists_proj_eq_of_mem_NR0 coverData rfl) (proj_mem_B0Plus coverData rfl rfl)
    (proj_mem_centM coverData rfl rfl) hG4 hdich hroot hex

end CFSG.Sporadic.SuzRecog

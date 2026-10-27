module

public import CFSG.Quasithin.H13.NQCoreFourGroup
public import CFSG.Quasithin.H13.NQBlockTerminalInputs

public section

namespace CFSG.Quasithin.H13.NQCore

theorem configurationFourGroupObstruction :
    NQBlock.ConfigurationFourGroupObstruction :=
  fun _ _ _ _ _ _ h B hBM hB2 hB4 => configuration_four_group_obstruction h B hBM hB2 hB4

end CFSG.Quasithin.H13.NQCore

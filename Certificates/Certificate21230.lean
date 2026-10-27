module

public import CFSG.LargeExtraspecial.A2ModD4Inputs
import all Init.Data.Nat.Fold
import all Init.Data.Array.Basic

public section

open CFSG.LargeExtraspecial.A2Mod

namespace Certificates

open CFSG.LargeExtraspecial.A2Mod in
theorem certificate21230 : d4SqueezeCheckZ = true := by decide +kernel

end Certificates

module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentSporHSTwoBInputs
import Certificates.Kernel.LocalQT.TwoB.F4150

public section

namespace Certificates

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519 CFSG.QuasithinUnique.Id2519.SporHS in
open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native in
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native in
open scoped commutatorElement in
theorem certificate4150 : (twoBCheck = true) :=
  CFSG.KD.LQT.TB.twoB_check

end Certificates

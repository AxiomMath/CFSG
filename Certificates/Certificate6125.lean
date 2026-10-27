module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4GenPerm
import Certificates.Kernel.Gen6125.Glue

public section

namespace Certificates

open CFSG.OddStandard.Solomon75.AhatData in
theorem certificate6125 : GenGood 8 (P0 8) true ∧ GenGood 11 (P0 11) false :=
  ⟨CFSG.KD.G6125n8.genGood, CFSG.KD.G6125n11.genGood⟩

end Certificates

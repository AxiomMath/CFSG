module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenHeis3MathieuData
import all CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenHeis3MathieuData

public section

namespace Certificates

open CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis.Mathieu

set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
open CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis.Mathieu in
theorem certificate1322003 : M24Facts ∧ M22Facts := by
  decide +kernel

end Certificates

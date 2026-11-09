module

public import Certificates.Kernel.Census.RuR.Data
import all Certificates.Kernel.Census.RuR.Data
import all Certificates.Data.Kernel.Census.PackedTree
import all Certificates.Data.Kernel.Census.PackedConj
import all Certificates.Data.Kernel.Census.PackedExc
import all Certificates.Data.Kernel.Census.Packed
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.RuR

open CFSG.KC.Census

set_option maxRecDepth 1000000

theorem kN0_0 : nodeF 0 = true := by quickRfl

theorem kN0_1 : nodeF 1 = true := by quickRfl

theorem kN0_2 : nodeF 2 = true := by quickRfl

theorem kN0_3 : nodeF 3 = true := by quickRfl

theorem kN0_4 : nodeF 4 = true := by quickRfl

theorem kN0_5 : nodeF 5 = true := by quickRfl

theorem kN0_6 : nodeF 6 = true := by quickRfl

theorem kN0_7 : nodeF 7 = true := by quickRfl

theorem kN0_8 : nodeF 8 = true := by quickRfl

theorem kN0_9 : nodeF 9 = true := by quickRfl

theorem kN0_10 : nodeF 10 = true := by quickRfl

theorem kN0_11 : nodeF 11 = true := by quickRfl

theorem kN0_12 : nodeF 12 = true := by quickRfl

theorem kN0_13 : nodeF 13 = true := by quickRfl

theorem kN0_14 : nodeF 14 = true := by quickRfl

theorem kN0 : (List.range' 0 15).all nodeF = true := by
  refine List.all_eq_true.2 fun i hi => ?_
  have h := List.mem_range'_1.1 hi
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 := by omega
  exacts [kN0_0, kN0_1, kN0_2, kN0_3, kN0_4, kN0_5, kN0_6, kN0_7, kN0_8, kN0_9, kN0_10, kN0_11, kN0_12, kN0_13, kN0_14]

theorem kN15 : (List.range' 15 72).all nodeF = true := by quickRfl

theorem kN87 : nodeF 87 = true := by quickRfl

theorem kN88 : (List.range' 88 46).all nodeF = true := by quickRfl

end CertificateChecks.KernelCensus.RuR

end

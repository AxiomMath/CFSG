module

public import Certificates.Kernel.A3E6.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelA3E6

open Certificates.A3E6K

set_option maxRecDepth 100000

theorem ch715502r : rootsOK rootsP rootsC = true := by quickRfl

theorem ch715502m : allN 72 (fun i => masksAt rootsP ZP NP i) = true := by quickRfl

theorem ch715502c : allN 72 (fun i => coverAt ZP NP FMP (cvRow cv0 cv1 i) i) = true := by quickRfl

theorem ch715502s0 : framesStruct rootsP ZP NP FMP fr0 0 27 = true := by quickRfl
theorem ch715502s1 : framesStruct rootsP ZP NP FMP fr1 27 54 = true := by quickRfl
theorem ch715502s2 : framesStruct rootsP ZP NP FMP fr2 54 81 = true := by quickRfl
theorem ch715502s3 : framesStruct rootsP ZP NP FMP fr3 81 108 = true := by quickRfl
theorem ch715502s4 : framesStruct rootsP ZP NP FMP fr4 108 135 = true := by quickRfl
theorem ch715502s5 : framesStruct rootsP ZP NP FMP fr5 135 162 = true := by quickRfl
theorem ch715502s6 : framesStruct rootsP ZP NP FMP fr6 162 189 = true := by quickRfl
theorem ch715502s7 : framesStruct rootsP ZP NP FMP fr7 189 216 = true := by quickRfl
theorem ch715502s8 : framesStruct rootsP ZP NP FMP fr8 216 243 = true := by quickRfl
theorem ch715502s9 : framesStruct rootsP ZP NP FMP fr9 243 270 = true := by quickRfl

end CertificateChecks.KernelA3E6

end

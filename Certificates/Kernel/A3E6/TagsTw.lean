module

public import Certificates.Kernel.A3E6.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelA3E6

open Certificates.A3E6K

set_option maxRecDepth 100000

theorem ch715502t0 : framesTags true rootsP ZP fr0 = true := by quickRfl
theorem ch715502t1 : framesTags true rootsP ZP fr1 = true := by quickRfl
theorem ch715502t2 : framesTags true rootsP ZP fr2 = true := by quickRfl
theorem ch715502t3 : framesTags true rootsP ZP fr3 = true := by quickRfl
theorem ch715502t4 : framesTags true rootsP ZP fr4 = true := by quickRfl
theorem ch715502t5 : framesTags true rootsP ZP fr5 = true := by quickRfl
theorem ch715502t6 : framesTags true rootsP ZP fr6 = true := by quickRfl
theorem ch715502t7 : framesTags true rootsP ZP fr7 = true := by quickRfl
theorem ch715502t8 : framesTags true rootsP ZP fr8 = true := by quickRfl
theorem ch715502t9 : framesTags true rootsP ZP fr9 = true := by quickRfl

end CertificateChecks.KernelA3E6

end

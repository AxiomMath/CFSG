module

public import Certificates.Data.Kernel.PermCent.CV
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsL2CertInputs
public import CFSG.GH74.KGroups.L27

public section

namespace CFSG.Certificates.Kernel.PkCV.L27T

open CFSG.GH74.KGroups.L27

@[expose] noncomputable def subC : Bool := (elemsC QP).all fun x => siftC QA x 0

@[expose] noncomputable def normC : Bool :=
  (elemsC QA).all fun y => (elemsC QP).all fun x => siftC QP (y * x * y⁻¹) 0

@[expose] noncomputable def invC : Bool :=
  (elemsC QP).all fun x => !decide (x * x = 1) || decide (x = 1) ||
    (elemsC QA).all fun y => !decide (y * x = x * y) || decide (y ^ 16 = 1)

@[expose] noncomputable def outerC : Bool :=
  (elemsC QA).all fun r => !decide (r * r = 1) || decide (r = 1) || siftC QP r 0 ||
    (((elemsC QP).any fun y => decide (y ^ 3 = 1) && !decide (y = 1) &&
        decide (y * r = r * y) && (elemsC QP).all fun g => !decide (g * r = r * g) ||
          decide (g * y * g⁻¹ = y) || decide (g * y * g⁻¹ = y * y)) &&
      (elemsC QA).all fun y => !decide (y * r = r * y) || !decide (y ^ 16 = 1) ||
        decide (y * y = 1))

end CFSG.Certificates.Kernel.PkCV.L27T

end

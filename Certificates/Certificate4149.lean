module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentMathNoLayerCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentMathData
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22OuterData
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24Data
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentMathCheckInputs
import Certificates.Kernel.SporSch.Mathieu.NoLayer4149
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519 CFSG.QuasithinUnique.Id2519.MathNoLayer in
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native in
theorem certificate4149 : (noLayerOK 23 (toTabs m23E) (allTables m23CentQ1) = true)
    ∧ (noLayerOK 22 (toTabs m22oE) (allTables m22OutCentQ2) = true)
    ∧ (noLayerOK 24 (toTabs m24E) (allTables m24CentQ2) = true) := KernelSporSch.NoLayer.facts

end Certificates

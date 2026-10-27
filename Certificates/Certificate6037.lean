module

public import CFSG.Monster.Existence.StdOdd.Cert.Sylow57Inputs
import Certificates.Kernel.StdOdd.Sylow57

public section

namespace Certificates

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.StdOdd in
open CFSG.Monster.Existence.StdOdd.Cert CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std in
open CFSG.LieType.Chevalley.C2E6Std.MatrixModel in
theorem certificate6037 : (sylow5Check = true)
    ∧ (sylow7Check = true) := CFSG.KD.StdOdd.Sylow57.facts

end Certificates

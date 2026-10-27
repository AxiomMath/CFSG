module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreeD42ConjData
import CFSG.Certificates.Kernel.D42ConjSound
import Certificates.Kernel.D42Conj.C

public section

namespace Certificates

open CFSG.KC.D42ConjP CFSG.KD.D4Plane CFSG.KD.D42Conj

open CFSG.LocalAnalysis.AGL81I.Section3.D42Over in
theorem certificate1322031 : d42ConjCheck = true := by
  refine d42ConjCheck_of (ls := ls) (fun i hi => ?_) enumOK ixOK
  exact beq_iff_eq.1 (List.all_eq_true.1 lettersOK i (List.mem_range.2 hi))

end Certificates

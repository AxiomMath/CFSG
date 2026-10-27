module

public import CFSG.Quasithin.H13.AS91Sec8V1CocData
import Certificates.Kernel.AS91Coc.Checks
import CFSG.Certificates.Kernel.AS91CocSound

public section

namespace Certificates

open CFSG.KS.AS91Coc in
theorem certificate664013 : CFSG.Quasithin.H13.AS91.M24G.cert664013Check () = true :=
  cert664013Check_of (relA_of_letOK letA) (relA_of_letOK letAi) (relA_of_letOK letB)
    (relA_of_letOK letBi) invA invB relOK maOK
    (fun c hc => by
      interval_cases c
      exacts [mw0, mw1, mw2, mw3, mw4])
    walkA walkB

end Certificates

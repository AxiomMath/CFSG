module

public import CFSG.Quasithin.H13.AS91Sec4EightInputs
import Certificates.Kernel.AS91K468.Checks46
import Certificates.Kernel.AS91K468.Checks48
import CFSG.Certificates.Kernel.AS91K468.Sound48

public section

namespace Certificates

open CertificateChecks.KernelAS91K468 in
open CFSG.Quasithin.H13.AS91 in
theorem certificate89408 : Two.ok48 () = true :=
  Certificates.Kernel.AS91K468.ok48_of ch89406_words ch89406_pnodup ch89408_crd ch89408_s48
    ch89408_pbar ch89408_b7 ch89408_r64 ch89408_stab ch89408_c3 ch89408_i ch89408_tb
    (fun i hi => match i, hi with
      | 0, _ => ch89408_tn0 | 1, _ => ch89408_tn1 | 2, _ => ch89408_tn2 | 3, _ => ch89408_tn3
      | 4, _ => ch89408_tn4 | 5, _ => ch89408_tn5 | 6, _ => ch89408_tn6 | 7, _ => ch89408_tn7
      | 8, _ => ch89408_tn8 | 9, _ => ch89408_tn9 | 10, _ => ch89408_tn10
      | 11, _ => ch89408_tn11 | 12, _ => ch89408_tn12 | 13, _ => ch89408_tn13
      | 14, _ => ch89408_tn14 | 15, _ => ch89408_tn15
      | _ + 16, h => absurd h (by omega))
    ch89408_tc ch89408_fus ch89408_orb

end Certificates

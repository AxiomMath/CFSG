module

public import Certificates.Data.AE6ParData
import Certificates.Kernel.AE6Par.Checks
import Certificates.Kernel.AE6Par.Tree
import Certificates.Kernel.AE6Par.Words
import Certificates.Kernel.AE6Par.Stab
import Certificates.Kernel.AE6Par.Quads
import CFSG.Certificates.Kernel.AE6ParSound

public section

namespace Certificates

open CertificateChecks.KernelAE6Par

open Certificates.AE6Par in
theorem certificate517601 : chkAgl () = true ∧ chkDc () = true ∧ chkWords () = true ∧ Certificates.AE6Par.chkTree () = true ∧
    chkVK () = true ∧ chkPlanes () = true ∧ chkSym () = true :=
  CFSG.KC.AE6Par.chk_all ae6par_tree ae6par_keys ae6par_keys_nodup ae6par_gens ae6par_rows
    ae6par_codes ae6par_t01 ae6par_words ae6par_notin ae6par_gstab ae6par_p2 ae6par_vk ae6par_six
    ae6par_masksP ae6par_masksT ae6par_quads ae6par_pfst ae6par_ptab

end Certificates

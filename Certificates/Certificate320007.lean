
module

public import Certificates.Data.G23RecogGlueInputs
import Certificates.Kernel.HcReplay.EltsGlue
import Certificates.Kernel.HcReplay.EltsLen
import CFSG.Certificates.Kernel.HcCount

public section

open CFSG.GH74.QTGen4.Recog.G23

namespace Certificates

open CFSG.GH74.QTGen4.Recog.G23 in
theorem certificate320007 : (elts.length = 576) ∧ elts.Nodup ∧
    (∀ s ∈ elts, ∀ g ∈ gensL, mulL s g ∈ elts) ∧ idL ∈ elts := by
  have h := congrArg List.length CFSG.KC.HcPack.elts_map_pk_eq
  rw [List.length_map, CFSG.KC.HcPack.E_len] at h
  exact CFSG.KC.HcPack.elts_facts h

end Certificates

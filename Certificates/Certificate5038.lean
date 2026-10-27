
module

public import CFSG.GH74.GLS.C3.Layer2.FinModelClaim
import Certificates.Kernel.GH74Tab.BGlue

public section

namespace Certificates

open CFSG.KD.GH74Tab

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5038 : ((mkTab 6).claimB = true)
    ∧ ((mkTab 7).claimB = true) :=
  ⟨c5038_claimB6, c5038_claimB7⟩

end Certificates

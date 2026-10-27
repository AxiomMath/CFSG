
module

public import CFSG.GH74.GLS.C3.Layer2.L5C5cInputs
import CFSG.Certificates.Kernel.L5.Sh0GamSound
import Certificates.Kernel.L5.Sh0Checks
import Certificates.Kernel.L5.Sh0GamChecks

public section

open CFSG.GH74.GLS.C3.Layer2.L5 CFSG.Certificates.Kernel.L5S

namespace Certificates

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5066 : (wdChk = true)
    ∧ (relsChk = true)
    ∧ ((List.range 4).all gamChk = true) :=
  ⟨wdChk_of sh0Chk_true sh0C_codes wdChkK_true,
    relsChk_of sh0Chk_true sh0C_codes relK_mem relsChkK_true,
    gamChk_of sh0Chk_true sh0C_codes fun m hm => by
      interval_cases m
      exacts [gamK0, gamK1, gamK2, gamK3]⟩

end Certificates

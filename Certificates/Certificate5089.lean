module

public import CFSG.GH74.GLS.C3.Prop121.FinPosCheckInputs
import Certificates.Kernel.GH74Tab.PosGlue

public section

namespace Certificates

open CFSG.KD.GH74Tab

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.Model in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2 in
theorem certificate5089 : ((mkTab 6).claimPosB = true)
    ∧ ((mkTab 7).claimPosB = true) :=
  ⟨c5089_claimPosB6, c5089_claimPosB7⟩

end Certificates

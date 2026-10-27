module

public import CFSG.GH74.GLS.C3.Layer2.L4ModelE3
import Certificates.Kernel.GH74Tab.E23Glue

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
theorem certificate5044 : ((mkTab 7).claimG ((mkTab 7).e3P (mkTab 7).wActE3 (mkTab 7).wCommE3) = true)
    ∧ ((mkTab 7).wActOKE3 = true) :=
  ⟨c5044_e3P, c5044_wAct⟩

end Certificates

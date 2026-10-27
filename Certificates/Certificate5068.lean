module

public import CFSG.GH74.GLS.C3.Layer2.L5C5eInputs
import CFSG.Certificates.Kernel.L5.Sh2E16Sound
import Certificates.Kernel.L5.Sh0Checks
import Certificates.Kernel.L5.Sh2E16Checks

public section

open CFSG.KD.L5.E16 CFSG.Certificates.Kernel.L5S

namespace Certificates

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5068 : (List.range 4).all (fun m => sh2E16Chk1 m && sh2E16Chk2 m && sh2MoveChk m) = true :=
  sh2Chks_of sh0Chk_true sh0C_codes tabsE16_true fun m hm => by
    interval_cases m
    exacts [ch50680, ch50681, ch50682, ch50683]

end Certificates

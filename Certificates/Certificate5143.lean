
module

public import CFSG.GH74.GLS.C3.Layer2.L5C2gListInputs
import CFSG.GH74.GLS.C3.Layer2.L5C2gTableInputsBase
import CFSG.Certificates.Kernel.L5.TabBuild

public section

open CFSG.GH74.GLS.C3.Layer2.L5.Fus

namespace Certificates

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open CFSG.GH74.GLS.C3.Layer2.L5.Fus in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5143 : 
    tabCheck sh1M sh1Code (buildTab sh1M sh1Code) (buildInv sh1M sh1Code)
    (buildOne sh1M sh1Code) = true := by
  exact tabCheck_build sh1M_complete (by rw [sh1M_codes]; exact sh1WW_chk.2.2)

end Certificates

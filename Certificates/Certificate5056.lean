
module

public import Certificates.Certificate5056Base
import all Certificates.Certificate5056Base

import CFSG.GH74.GLS.C3.Layer2.L5C2fTableInputsBase
import CFSG.Certificates.Kernel.L5.TabBuild

public section

open CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.Fus Equiv Perm

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open CFSG.GH74.GLS.C3.Layer2.L5.Fus in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5056 : 
    tabCheck sh0M sh0Code (buildTab sh0M sh0Code) (buildInv sh0M sh0Code)
    (buildOne sh0M sh0Code) = true := by
  exact tabCheck_build sh0M_complete CertificateChecks.Batch5056.sh0_codes

end Certificates

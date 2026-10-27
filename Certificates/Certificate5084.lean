module

public import CFSG.GH74.GLS.C3.Prop121.CentK7Inputs
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.Assembly.ComponentTypeDefs
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Prop121
open Subgroup Equiv Perm CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2.Model

namespace CertificateChecks.Batch5084

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Prop121
open Subgroup Equiv Perm CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2.Model

set_option maxHeartbeats 0 in
private theorem okSearch7_true_0 : okSearch7 = true := by
  decide +kernel

end CertificateChecks.Batch5084

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Prop121 in
open Subgroup Equiv Perm CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5084 : okSearch7 = true := by
  exact CertificateChecks.Batch5084.okSearch7_true_0

end Certificates

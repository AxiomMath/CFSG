module

public import CFSG.GH74.GLS.C3.Prop121.Card7H1
public import CFSG.GH74.GLS.C3.Prop121.Card7H2Inputs
meta import CFSG.GH74.GLS.C3.Prop121.Card7H1
meta import Mathlib.Algebra.Group.End
meta import Mathlib.GroupTheory.Perm.Sign
meta import Mathlib.GroupTheory.Perm.Basic
meta import Mathlib.GroupTheory.Perm.Fin
meta import Mathlib.Logic.Equiv.Fin.Basic
meta import Mathlib.Logic.Equiv.Option
meta import Mathlib.Data.List.FinRange
meta import CFSG.GH74.GLS.C3.Prop121.Card7H2Inputs

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Prop121
open CFSG.GH74.GLS.C3.Prop121.Card7
open CFSG.GH74.GLS.C3.Prop121.Card7.HC
open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Layer3

namespace CertificateChecks.Batch5081

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Prop121
open CFSG.GH74.GLS.C3.Prop121.Card7
open CFSG.GH74.GLS.C3.Prop121.Card7.HC
open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Layer3

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem ord3Check_true_0 : ord3Check = true := by
  decide +kernel

private theorem centerCheck_true_1 : centerCheck = true := by
  decide +kernel

private theorem ccL_T1_T1_2 : ccL T1 T1 = 576 := by
  decide +kernel

private theorem B0invCheck_true_3 : B0invCheck = true := by
  decide +kernel

end CertificateChecks.Batch5081

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Prop121 in
open CFSG.GH74.GLS.C3.Prop121.Card7 in
open CFSG.GH74.GLS.C3.Prop121.Card7.HC in
open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Layer3 in
theorem certificate5081 : (ord3Check = true)
    ∧ (centerCheck = true)
    ∧ (ccL T1 T1 = 576)
    ∧ (B0invCheck = true) := by
  exact ⟨CertificateChecks.Batch5081.ord3Check_true_0, CertificateChecks.Batch5081.centerCheck_true_1, CertificateChecks.Batch5081.ccL_T1_T1_2, CertificateChecks.Batch5081.B0invCheck_true_3⟩

end Certificates

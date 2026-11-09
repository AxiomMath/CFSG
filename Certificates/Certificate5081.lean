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
import Certificates.Kernel.Card7H2.Codes

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

open CFSG.Certificates.Kernel.Card7H2 in
private theorem hl_codes : (HL.map (CFSG.KS.PCnt.pkw 6) == hlC) = true := by
  decide +kernel

open CFSG.Certificates.Kernel.Card7H2 in
private theorem ord3_codes : ord3C = true := by
  decide +kernel

open CFSG.Certificates.Kernel.Card7H2 in
private theorem r3_codes : r3Ok = true := by
  decide +kernel

open CFSG.Certificates.Kernel.Card7H2 in
private theorem r2_codes : r2Ok = true := by
  decide +kernel

open CFSG.Certificates.Kernel.Card7H2 in
private theorem center_codes : centerC = true := by
  decide +kernel

open CFSG.Certificates.Kernel.Card7H2 in
private theorem ccT1_codes : ccC t1C t1C = 576 := by
  decide +kernel

open CFSG.Certificates.Kernel.Card7H2 in
private theorem b0inv_codes : b0invC = true := by
  decide +kernel

private theorem ord3Check_true_0 : ord3Check = true :=
  CFSG.Certificates.Kernel.Card7H2.ord3Check_of (eq_of_beq hl_codes) r3_codes ord3_codes

private theorem centerCheck_true_1 : centerCheck = true :=
  CFSG.Certificates.Kernel.Card7H2.centerCheck_of (eq_of_beq hl_codes) center_codes

private theorem ccL_T1_T1_2 : ccL T1 T1 = 576 :=
  CFSG.Certificates.Kernel.Card7H2.ccL_T1_of (eq_of_beq hl_codes) ccT1_codes

private theorem B0invCheck_true_3 : B0invCheck = true :=
  CFSG.Certificates.Kernel.Card7H2.B0invCheck_of (eq_of_beq hl_codes) r2_codes b0inv_codes

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

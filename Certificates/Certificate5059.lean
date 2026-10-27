module

public import CFSG.GH74.GLS.C3.Layer2.L5C0Inputs

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

namespace CertificateChecks.Batch5059

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

set_option maxRecDepth 100000

private theorem sh0_R1_not_ge_chk_0 : RhatL0.any (fun p => !(decide (p ∈ R1L))) = true := by
  decide +kernel

private theorem RhatL1_nodup_1 : RhatL1.Nodup := by
  decide +kernel

private theorem RhatL1_length_2 : RhatL1.length = 16 := by
  decide +kernel

private theorem RhatL1_sq_chk_3 : RhatL1.all (fun a => decide (a * a = 1)) = true := by
  decide +kernel

private theorem RhatL1_comm_chk_4 : RhatL1.all (fun a => RhatL1.all fun b => decide (a * b = b * a)) = true := by
  decide +kernel

end CertificateChecks.Batch5059

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5059 : (RhatL0.any (fun p => !(decide (p ∈ R1L))) = true)
    ∧ (RhatL1.Nodup)
    ∧ (RhatL1.length = 16)
    ∧ (RhatL1.all (fun a => decide (a * a = 1)) = true)
    ∧ (RhatL1.all (fun a => RhatL1.all fun b => decide (a * b = b * a)) = true) := by
  exact ⟨CertificateChecks.Batch5059.sh0_R1_not_ge_chk_0, CertificateChecks.Batch5059.RhatL1_nodup_1, CertificateChecks.Batch5059.RhatL1_length_2, CertificateChecks.Batch5059.RhatL1_sq_chk_3, CertificateChecks.Batch5059.RhatL1_comm_chk_4⟩

end Certificates

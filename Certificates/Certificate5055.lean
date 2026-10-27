module

public import CFSG.GH74.GLS.C3.Layer2.L5C0Inputs
public import CFSG.GH74.GLS.C3.Layer2.L5C14
public import CFSG.GH74.GLS.C3.Layer2.L5C6
public import CFSG.GH74.GLS.C3.Layer2.L5C7
meta import Mathlib.GroupTheory.SpecificGroups.Alternating
meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
meta import CFSG.GH74.GLS.C3.Layer2.L5A1
meta import CFSG.GH74.GLS.C3.Layer2.L5B2
meta import CFSG.GH74.GLS.C3.Layer2.L5C0
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Goldschmidt.StatementsH
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian_models
public import CFSG.Walter.J1
public import CFSG.Walter.J1Recog
public import CFSG.Walter.Ree.Thompson2.BaseFin
public import CFSG.Walter.ReeOrder.WardLocal
public import CFSG.Walter.W67.Section8.Prop83
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

namespace CertificateChecks.Batch5055

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

set_option maxRecDepth 100000

private theorem tr16_inj_chk_0 : (List.finRange 16).all (fun i => (List.finRange 16).all fun j =>
    CFSG.GH74.GLS.C3.Layer2.L5.imp (decide (tr16 i = tr16 j)) (decide (i = j))) = true := by
  decide +kernel

private theorem tr1_inj_chk_1 : (List.finRange 16).all (fun i => (List.finRange 16).all fun j =>
    CFSG.GH74.GLS.C3.Layer2.L5.imp (decide (tr1 i = tr1 j)) (decide (i = j))) = true := by
  decide +kernel

private theorem R1L_comm_chk_2 : R1L.all (fun a => R1L.all fun b => decide (a * b = b * a)) = true := by
  decide +kernel

private theorem R1L_ne_one_chk_3 : R1L.any (fun r => decide (r ≠ 1)) = true := by
  decide +kernel

private theorem R1L_sq_chk_4 : R1L.all (fun r => decide (r * r = 1)) = true := by
  decide +kernel

end CertificateChecks.Batch5055

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5055 : ((List.finRange 16).all (fun i => (List.finRange 16).all fun j =>
    CFSG.GH74.GLS.C3.Layer2.L5.imp (decide (CFSG.GH74.GLS.C3.Layer2.L5.tr16 i = CFSG.GH74.GLS.C3.Layer2.L5.tr16 j)) (decide (i = j))) = true)
    ∧ ((List.finRange 16).all (fun i => (List.finRange 16).all fun j =>
    CFSG.GH74.GLS.C3.Layer2.L5.imp (decide (tr1 i = tr1 j)) (decide (i = j))) = true)
    ∧ (R1L.all (fun a => R1L.all fun b => decide (a * b = b * a)) = true)
    ∧ (R1L.any (fun r => decide (r ≠ 1)) = true)
    ∧ (R1L.all (fun r => decide (r * r = 1)) = true) := by
  exact ⟨CertificateChecks.Batch5055.tr16_inj_chk_0, CertificateChecks.Batch5055.tr1_inj_chk_1, CertificateChecks.Batch5055.R1L_comm_chk_2, CertificateChecks.Batch5055.R1L_ne_one_chk_3, CertificateChecks.Batch5055.R1L_sq_chk_4⟩

end Certificates

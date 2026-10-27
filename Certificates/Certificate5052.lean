module

public import CFSG.GH74.GLS.C3.Layer2.L5C0Inputs
public import CFSG.GH74.GLS.C3.Layer2.L5C10Inputs
public import Certificates.Data.A5
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.Assembly.ComponentTypeDefs
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

namespace CertificateChecks.Batch5052

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

set_option maxRecDepth 100000

private theorem el16_Qm_iff_chk_0 : (List.finRange 16).all
    (fun i => decide (el16 i ∈ Qml ↔ i ∈ QplG)) = true := by
  decide +kernel

private theorem el16_Pm_iff_chk_1 : (List.finRange 16).all
    (fun i => decide (el16 i ∈ Pml ↔ i ∈ PplG)) = true := by
  decide +kernel

end CertificateChecks.Batch5052

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5052 : ((List.finRange 16).all
    (fun i => decide (el16 i ∈ Qml ↔ i ∈ QplG)) = true)
    ∧ ((List.finRange 16).all
    (fun i => decide (el16 i ∈ Pml ↔ i ∈ PplG)) = true) := by
  exact ⟨CertificateChecks.Batch5052.el16_Qm_iff_chk_0, CertificateChecks.Batch5052.el16_Pm_iff_chk_1⟩

end Certificates

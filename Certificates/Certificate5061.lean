module

public import CFSG.GH74.GLS.C3.Layer2.L5C4Inputs

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open CFSG.GH74.GLS.C3.Layer2.L5.Rec1
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

namespace CertificateChecks.Batch5061

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open CFSG.GH74.GLS.C3.Layer2.L5.Rec1
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

set_option maxRecDepth 100000

private theorem cr_cocycle_0 : ∀ (j k : Fin 8) (r : Fin 16),
    xor16 (xor16 (cr j r) (Dg j (cr k r))) (cr (mulIdx j k) r) = 0 := by
  decide +kernel

private theorem fix_im_1 : ∀ z : Fin 16, xor16 z (Dg 1 z) = 0 → ∃ r : Fin 16, z = cr 1 r := by
  decide +kernel

end CertificateChecks.Batch5061

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open CFSG.GH74.GLS.C3.Layer2.L5.Rec1 in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5061 : (∀ (j k : Fin 8) (r : Fin 16),
    xor16 (xor16 (cr j r) (Dg j (cr k r))) (cr (mulIdx j k) r) = 0)
    ∧ (∀ z : Fin 16, xor16 z (Dg 1 z) = 0 → ∃ r : Fin 16, z = cr 1 r) := by
  exact ⟨CertificateChecks.Batch5061.cr_cocycle_0, CertificateChecks.Batch5061.fix_im_1⟩

end Certificates

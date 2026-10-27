module

public import CFSG.GH74.GLS.C3.Layer2.L5C3a
public import CFSG.GH74.GLS.C3.Layer2.L5C3Inputs
public import CFSG.Certificates.Kernel.L5.E16Sound
public import Certificates.Kernel.L5E16.Checks
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib

public section

open CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.Model CFSG.Certificates.Kernel.L5E16S
  CertificateChecks.KernelL5E16 CFSG.KD.L5E16

namespace CertificateChecks.Batch5058

open CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.Model CFSG.Certificates.Kernel.L5E16S
  CertificateChecks.KernelL5E16 CFSG.KD.L5E16

theorem code_one : code 1 = oneK := by
  have h : Nat.beq (code 1) oneK = true := by quickRfl
  exact Nat.eq_of_beq_eq_true h

theorem code_gens : sh1Gens.map code = G := by
  have h : (sh1Gens.map code == G) = true := by quickRfl
  exact beq_iff_eq.1 h

theorem code_R : RhatL1.map code = R := by
  have h : (RhatL1.map code == R) = true := by quickRfl
  exact beq_iff_eq.1 h

theorem e16Chk_true : e16Chk Sh1L RhatL1 = true :=
  e16Chk_of code_one code_gens code_R ch5058_closed ch5058_e16

end CertificateChecks.Batch5058

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5058 : e16Chk Sh1L RhatL1 = true := CertificateChecks.Batch5058.e16Chk_true

end Certificates

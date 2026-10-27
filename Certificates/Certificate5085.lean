module

public import CFSG.GH74.GLS.C3.Prop121.MooreFinite7
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import CFSG.GH74.GLS.C3.Prop121.CentKFinInputs
meta import CFSG.GH74.GLS.C3.Prop121.MooreFinite7
meta import Mathlib.Algebra.Group.End
meta import Mathlib.GroupTheory.Perm.Sign
meta import Mathlib.GroupTheory.Perm.Basic
meta import Mathlib.GroupTheory.Perm.Fin
meta import Mathlib.GroupTheory.Perm.Support
meta import Mathlib.GroupTheory.Perm.Cycle.Basic
meta import Mathlib.GroupTheory.Perm.Cycle.Type
meta import Mathlib.Logic.Equiv.Fin.Basic
meta import Mathlib.Logic.Equiv.Option
meta import Mathlib.Data.List.FinRange
meta import CFSG.GH74.GLS.C3.Prop121.CentKFinInputs
import Certificates.Kernel.CentKFin.Checks
import CFSG.Certificates.Kernel.PermCent.CentK6CSound

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Prop121
open Equiv Perm

namespace CertificateChecks.Batch5085

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Prop121
open Equiv Perm

private theorem okC6_true_0 : okC6 = true :=
  CFSG.Certificates.Kernel.PkCV.okC6_eq.trans Certificates.Kernel.CentKFin.c6F_true

private theorem finite_cent_five_check_1 : ((allPerms 5).all fun τ =>
      !(decide (τ * τ * τ = 1 ∧ τ ≠ 1)) ||
        (allPerms 5).all fun b =>
          !(decide (sign b = 1 ∧ b * τ = τ * b)) ||
            decide (b = 1 ∨ b = τ ∨ b = τ⁻¹)) = true :=
  CFSG.Certificates.Kernel.PkCV.five_eq.trans Certificates.Kernel.CentKFin.f5F_true

end CertificateChecks.Batch5085

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Prop121 in
open Equiv Perm in
theorem certificate5085 : (okC6 = true)
    ∧ (((allPerms 5).all fun τ =>
      !(decide (τ * τ * τ = 1 ∧ τ ≠ 1)) ||
        (allPerms 5).all fun b =>
          !(decide (sign b = 1 ∧ b * τ = τ * b)) ||
            decide (b = 1 ∨ b = τ ∨ b = τ⁻¹)) = true) := by
  exact ⟨CertificateChecks.Batch5085.okC6_true_0, CertificateChecks.Batch5085.finite_cent_five_check_1⟩

end Certificates

module

public import CFSG.GH74.GLS.C3.Prop121.L122Fin
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import CFSG.GH74.GLS.C3.Prop121.Fin6ClauseInputs
meta import CFSG.GH74.GLS.C3.Prop121.L122Fin
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
meta import CFSG.GH74.GLS.C3.Prop121.Fin6ClauseInputs

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Prop121
open Equiv Perm

namespace CertificateChecks.Batch5087

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Prop121
open Equiv Perm

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem ok6c_true_0 : ok6c = true := by
  decide +kernel

private theorem exists_comm_ord3_six_check_1 : ((allPerms 6).all fun σ =>
      !(decide (σ * σ * σ = 1 ∧ σ ≠ 1)) ||
        (allPerms 6).any fun k =>
          decide (k * k * k = 1 ∧ k ≠ 1 ∧ k * σ = σ * k ∧ k ≠ σ ∧ k ≠ σ⁻¹)) = true := by
  decide +kernel

end CertificateChecks.Batch5087

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Prop121 in
open Equiv Perm in
theorem certificate5087 : (ok6c = true)
    ∧ (((allPerms 6).all fun σ =>
      !(decide (σ * σ * σ = 1 ∧ σ ≠ 1)) ||
        (allPerms 6).any fun k =>
          decide (k * k * k = 1 ∧ k ≠ 1 ∧ k * σ = σ * k ∧ k ≠ σ ∧ k ≠ σ⁻¹)) = true) := by
  exact ⟨CertificateChecks.Batch5087.ok6c_true_0, CertificateChecks.Batch5087.exists_comm_ord3_six_check_1⟩

end Certificates

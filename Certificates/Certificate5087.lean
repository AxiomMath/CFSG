module

public import CFSG.GH74.GLS.C3.Prop121.L122Fin
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import CFSG.GH74.GLS.C3.Prop121.Fin6ClauseInputs
import CFSG.Certificates.Kernel.PermCent.Ok122CSound
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

private def ok6G {G : Type*} [Group G] [DecidableEq G] (I O : List G) (f0 : G → Bool)
    (nm : G → ℕ) : Bool :=
  I.all fun a => I.all fun b =>
    !(decide (a * b = b * a) && !decide (a = b) && f0 a && f0 b) ||
    !(O.any fun ρ => decide (ρ * a = a * ρ) && decide (ρ * b = b * ρ)) ||
    O.all fun τ =>
      !((decide (τ * a * τ⁻¹ = b) || decide (τ * a * τ⁻¹ = a * b)) &&
        (decide (τ * b * τ⁻¹ = a) || decide (τ * b * τ⁻¹ = b) || decide (τ * b * τ⁻¹ = a * b)) &&
        f0 τ) ||
      decide (nm τ = 3)

private theorem ok6c_eq_G :
    ok6c = ok6G inv7 ord3 (fun σ => decide (σ 0 = 0)) fun σ => σ.support.card := by
  unfold ok6c ok6G
  simp only [CFSG.Certificates.Kernel.PkCV.ite_true_eq, Bool.decide_and, decide_not,
    Bool.decide_or, Bool.decide_eq_true, Bool.not_and, Bool.not_not, Bool.or_assoc, Bool.and_assoc]

private theorem ok6G_map {G H : Type*} [Group G] [DecidableEq G] [Group H] [DecidableEq H]
    (f : H → G) (hmul : ∀ a b, f (a * b) = f a * f b) (hinv : ∀ a, f a⁻¹ = (f a)⁻¹)
    (hf : Function.Injective f) (I O : List H) (f0 : G → Bool) (nm : G → ℕ) :
    ok6G (I.map f) (O.map f) f0 nm = ok6G I O (fun x => f0 (f x)) fun σ => nm (f σ) := by
  unfold ok6G
  simp only [List.all_map, List.any_map, Function.comp_def, ← hmul, ← hinv, hf.eq_iff]

private theorem ok6c_eq : ok6c = ok6G CFSG.Certificates.Kernel.PkCV.inv7P
    CFSG.Certificates.Kernel.PkCV.ord3P (fun x => decide (CFSG.Certificates.Kernel.PkCV.ev x 0 = 0))
    fun σ => (CFSG.Certificates.Kernel.PkCV.ev σ).support.card := by
  rw [ok6c_eq_G, CFSG.Certificates.Kernel.PkCV.inv7_eq, CFSG.Certificates.Kernel.PkCV.ord3_eq,
    ok6G_map CFSG.Certificates.Kernel.PkCV.ev CFSG.Certificates.Kernel.PkCV.ev_mul
      CFSG.Certificates.Kernel.PkCV.ev_inv CFSG.Certificates.Kernel.PkCV.ev_injective]

private theorem ok6c_true_0 : ok6c = true := by
  rw [ok6c_eq]
  unfold ok6G
  simp only [CFSG.Certificates.Kernel.PkCV.comm_fast, CFSG.Certificates.Kernel.PkCV.conj_fast]
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

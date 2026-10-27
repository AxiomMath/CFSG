module

public import CFSG.Monster.Existence.Census.RigidInputs
public import Certificates.Certificate6007
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open CFSG.Monster.Existence.Census CFSG.Monster.B.Rep4371

namespace CertificateChecks.Batch6023

open CFSG.Monster.Existence.Census CFSG.Monster.B.Rep4371

@[expose] def pauliOK (a : ℕ) (s : Bool) (d : ℕ) : Bool :=
  !(rigidRows.all fun x => fixRow (s, a, d) x.1 x.2) || (!s && a == 0 && d == 0)

theorem rigid_A : (List.range 4096).all (fun a => !(rigidRows.all fun x => fixRowA a x.2) || a == 0
    || a == 63) = true := by
  decide +kernel

theorem pauli_0_false : (List.range 4096).all (pauliOK 0 false) = true := by decide +kernel
theorem pauli_0_true : (List.range 4096).all (pauliOK 0 true) = true := by decide +kernel
theorem pauli_63_false : (List.range 4096).all (pauliOK 63 false) = true := by decide +kernel
theorem pauli_63_true : (List.range 4096).all (pauliOK 63 true) = true := by decide +kernel

end CertificateChecks.Batch6023

namespace Certificates

open CertificateChecks.Batch6023 in
open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.Census CFSG.Monster.B in
open CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel in
open CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.AxisCount Matrix in
open CFSG.Monster.B.Rep4371 hiding interp interp_eq_sum in
theorem certificate6023 : ((List.range 4096).all (fun a => !(rigidRows.all fun x => fixRowA a x.2) || a == 0
      || a == 63) = true)
    ∧ (([0, 63].all fun a => [false, true].all fun s => (List.range 4096).all fun d =>
      !(rigidRows.all fun x => fixRow (s, a, d) x.1 x.2) || (!s && a == 0 && d == 0)) = true) := by
  refine ⟨rigid_A, List.all_eq_true.2 fun a ha => List.all_eq_true.2 fun s hs => ?_⟩
  change (List.range 4096).all (pauliOK a s) = true
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hs
  rcases ha with rfl | rfl <;> rcases hs with rfl | rfl
  exacts [pauli_0_false, pauli_0_true, pauli_63_false, pauli_63_true]

end Certificates

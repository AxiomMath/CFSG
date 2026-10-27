module

public import CFSG.Monster.Existence.Census.FusionGensInputs
public import Certificates.Kernel.MonsterExist.RigidW

public section

open CFSG.Monster.AxisCount CFSG.Monster.Existence.Census CertificateChecks.MonsterExist.RigidW

namespace CertificateChecks.Batch6022

open CFSG.Monster.AxisCount CFSG.Monster.Existence.Census CertificateChecks.MonsterExist.RigidW

@[expose] def lhs (j : ℕ) : List Native.Gen := [Native.Gen.sign 3, Native.Gen.perm idArr] ++ [fusGen j]

@[expose] def rhs (j : ℕ) : List Native.Gen :=
  [fusGen j, Native.Gen.rho (fusShift j)] ++ [Native.Gen.sign 3, Native.Gen.perm idArr]

theorem w0 : checkW (lhs 0) (rhs 0) = true := by decide +kernel
theorem w1 : checkW (lhs 1) (rhs 1) = true := by decide +kernel
theorem w2 : checkW (lhs 2) (rhs 2) = true := by decide +kernel
theorem w3 : checkW (lhs 3) (rhs 3) = true := by decide +kernel
theorem w4 : checkW (lhs 4) (rhs 4) = true := by decide +kernel
theorem w5 : checkW (lhs 5) (rhs 5) = true := by decide +kernel
theorem w6 : checkW (lhs 6) (rhs 6) = true := by decide +kernel
theorem w7 : checkW (lhs 7) (rhs 7) = true := by decide +kernel
theorem w8 : checkW (lhs 8) (rhs 8) = true := by decide +kernel
theorem w9 : checkW (lhs 9) (rhs 9) = true := by decide +kernel

theorem w10_letters :
    ((lhs 10 ++ rhs 10).all (fun g => g.validB) && (lhs 10 ++ rhs 10).all (fun g => !isTau g)) = true := by
  decide +kernel

theorem w10_a : (rigidGroups.take 5).all (fun G => groupOK (lhs 10) (rhs 10) G.1 G.2) = true := by
  decide +kernel

theorem w10_b : ((rigidGroups.drop 5).take 5).all (fun G => groupOK (lhs 10) (rhs 10) G.1 G.2) = true := by
  decide +kernel

theorem w10_c : (rigidGroups.drop 10).all (fun G => groupOK (lhs 10) (rhs 10) G.1 G.2) = true := by
  decide +kernel

theorem w10 : checkW (lhs 10) (rhs 10) = true := by
  have h : rigidGroups = rigidGroups.take 5 ++ ((rigidGroups.drop 5).take 5 ++ rigidGroups.drop 10) := by
    rw [show (10 : ℕ) = 5 + 5 from rfl, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
  unfold checkW
  rw [w10_letters, Bool.true_and, h, List.all_append, List.all_append, w10_a, w10_b, w10_c]
  rfl

theorem fusCheckC_of (lo hi : ℕ) (h : ∀ j < hi, lo ≤ j → checkW (lhs j) (rhs j) = true) :
    fusCheckC (Native.mkCtx ()) lo hi = true := by
  unfold fusCheckC
  refine List.all_eq_true.2 fun j hj => ?_
  have hj' := List.mem_range.1 hj
  by_cases hl : j < lo
  · simp [hl]
  · rw [Bool.or_eq_true]
    exact Or.inr (checkRigid_of_checkW (h j hj' (by omega)))

end CertificateChecks.Batch6022

namespace Certificates

open CertificateChecks.Batch6022 in
open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.Census CFSG.Monster.B in
open CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel in
open CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.AxisCount in
open CFSG.Monster.B.TwoA.Census Matrix in
open CFSG.Monster.B.Rep4371 hiding interp interp_eq_sum in
theorem certificate6022 : (fusCheckC (Native.mkCtx ()) 0 4 = true)
    ∧ (fusCheckC (Native.mkCtx ()) 4 8 = true)
    ∧ (fusCheckC (Native.mkCtx ()) 8 11 = true) := by
  refine ⟨fusCheckC_of 0 4 fun j hj _ => ?_, fusCheckC_of 4 8 fun j hj hl => ?_,
    fusCheckC_of 8 11 fun j hj hl => ?_⟩
  · interval_cases j
    exacts [w0, w1, w2, w3]
  · interval_cases j
    exacts [w4, w5, w6, w7]
  · interval_cases j
    exacts [w8, w9, w10]

end Certificates

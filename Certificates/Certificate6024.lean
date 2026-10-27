module

public import CFSG.Monster.Existence.Census.TrialityWitnessesInputs
public import Certificates.Kernel.MonsterExist.RigidB

public section

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.Census CFSG.Monster.B
open CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
open CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.AxisCount
open CFSG.Monster.B.TwoA.Census
open CFSG.Monster.B.Rep4371 hiding interp interp_eq_sum
open CertificateChecks.MonsterExist.RigidB

namespace CertificateChecks.Batch6024

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.Census CFSG.Monster.B
open CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
open CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.AxisCount
open CFSG.Monster.B.TwoA.Census
open CFSG.Monster.B.Rep4371 hiding interp interp_eq_sum
open CertificateChecks.MonsterExist.RigidB

theorem check_one :
    checkB (Native.Gen.tauPow 1 ++ [Native.Gen.sign 3, Native.Gen.perm CFSG.Monster.Existence.Census.idArr] ++ Native.Gen.tauPow 2)
      [Native.Gen.rho (false, 3, 60)] = true := by
  decide +kernel

theorem check_two :
    checkB (Native.Gen.tauPow 1 ++ ([Native.Gen.sign 3, Native.Gen.perm CFSG.Monster.Existence.Census.idArr] ++
        [Native.Gen.rho (false, 63, 0)]) ++ Native.Gen.tauPow 2)
      [Native.Gen.rho (true, 60, 60)] = true := by
  decide +kernel

theorem check_three :
    checkB (Native.Gen.tauPow 2 ++ ([Native.Gen.sign 3, Native.Gen.perm CFSG.Monster.Existence.Census.idArr] ++
        [Native.Gen.rho (false, 60, 48)]) ++ Native.Gen.tauPow 1)
      [Native.Gen.rho (true, 3, 48)] = true := by
  decide +kernel

theorem check_four :
    checkB (Native.Gen.tauPow 2 ++ ([Native.Gen.sign 734, Native.Gen.perm CFSG.Monster.Existence.Census.idArr] ++
        [Native.Gen.rho (false, 734, 0)]) ++ Native.Gen.tauPow 1)
      [Native.Gen.rho (true, 734, 0)] = true := by
  decide +kernel

theorem alphaN_one : alphaN 1 (false, 63, 0) = (false, 63, 0) := by decide +kernel

theorem conj_alphaN_two :
    Model.conjPauliN (false, 63, 0) (alphaN 1 (false, 63, 0)) = (false, 63, 0) := by
  decide +kernel

theorem conj_alphaN_three :
    Model.conjPauliN (false, 60, 48) (alphaN 1 (false, 63, 0)) = (false, 63, 0) := by
  decide +kernel

theorem conj_alphaN_four :
    Model.conjPauliN (false, 734, 0) (alphaN 2 (false, 63, 0)) = (false, 63, 0) := by
  decide +kernel

theorem tauData_witnesses :
    tauData.map (fun w => (w.cosetIndex, w.sourceQ, w.trialityPower, w.target)) =
      [(1, 0, 2, (0, 3, 60)), (1, 63, 2, (1, 60, 60)), (1, 196668, 1, (1, 3, 48)),
        (2, 734, 1, (1, 734, 0))] := by
  decide +kernel

end CertificateChecks.Batch6024

namespace Certificates

open CertificateChecks.Batch6024 in
open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.Census CFSG.Monster.B in
open CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel in
open CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.AxisCount in
open CFSG.Monster.B.TwoA.Census Matrix in
open CFSG.Monster.B.Rep4371 hiding interp interp_eq_sum in
theorem certificate6024 : (checkRigid (Native.mkCtx ())
      (Native.Gen.tauPow 1 ++ [Native.Gen.sign 3, Native.Gen.perm
          CFSG.Monster.Existence.Census.idArr] ++ Native.Gen.tauPow 2)
      [Native.Gen.rho (false, 3, 60)] = true)
    ∧ (checkRigid (Native.mkCtx ())
      (Native.Gen.tauPow 1 ++ ([Native.Gen.sign 3, Native.Gen.perm
          CFSG.Monster.Existence.Census.idArr] ++
        [Native.Gen.rho (false, 63, 0)]) ++ Native.Gen.tauPow 2)
      [Native.Gen.rho (true, 60, 60)] = true)
    ∧ (checkRigid (Native.mkCtx ())
      (Native.Gen.tauPow 2 ++ ([Native.Gen.sign 3, Native.Gen.perm
          CFSG.Monster.Existence.Census.idArr] ++
        [Native.Gen.rho (false, 60, 48)]) ++ Native.Gen.tauPow 1)
      [Native.Gen.rho (true, 3, 48)] = true)
    ∧ (checkRigid (Native.mkCtx ())
      (Native.Gen.tauPow 2 ++ ([Native.Gen.sign 734, Native.Gen.perm
          CFSG.Monster.Existence.Census.idArr] ++
        [Native.Gen.rho (false, 734, 0)]) ++ Native.Gen.tauPow 1)
      [Native.Gen.rho (true, 734, 0)] = true)
    ∧ (alphaN 1 (false, 63, 0) = (false, 63, 0))
    ∧ (Model.conjPauliN (false, 63, 0) (alphaN 1 (false, 63, 0)) = (false, 63, 0))
    ∧ (Model.conjPauliN (false, 60, 48) (alphaN 1 (false, 63, 0)) = (false, 63, 0))
    ∧ (Model.conjPauliN (false, 734, 0) (alphaN 2 (false, 63, 0)) = (false, 63, 0))
    ∧ (tauData.map (fun w => (w.cosetIndex, w.sourceQ, w.trialityPower, w.target)) =
      [(1, 0, 2, (0, 3, 60)), (1, 63, 2, (1, 60, 60)), (1, 196668, 1, (1, 3, 48)),
        (2, 734, 1, (1, 734, 0))]) :=
  ⟨checkRigid_of_checkB check_one, checkRigid_of_checkB check_two, checkRigid_of_checkB check_three,
    checkRigid_of_checkB check_four, alphaN_one, conj_alphaN_two, conj_alphaN_three, conj_alphaN_four,
    tauData_witnesses⟩

end Certificates

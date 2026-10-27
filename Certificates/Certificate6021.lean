module

public import Certificates.Kernel.MonsterExist.Fusion

public section

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.Census CFSG.Monster.B
open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.Rep4371 CertificateChecks.MonsterExist.Fusion

namespace CertificateChecks.Batch6021

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.Census CFSG.Monster.B
open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.Rep4371 CertificateChecks.MonsterExist.Fusion

theorem genMatches_ok :
    ((List.range 11).all fun j => match fusionData.generators[j]? with
      | some r => genMatches (fusGen j) r && (ofTriple r.shift == fusShift j)
      | none => false) = true := by
  decide +kernel

theorem fusGen_valid : ∀ j < 11, (fusGen j).validB = true := by decide +kernel

theorem fix_ok : fixOK = true := by decide +kernel

theorem tgt0 : tgtOK 0 = true := by decide +kernel
theorem tgt1 : tgtOK 1 = true := by decide +kernel
theorem tgt2 : tgtOK 2 = true := by decide +kernel
theorem tgt3 : tgtOK 3 = true := by decide +kernel
theorem tgt4 : tgtOK 4 = true := by decide +kernel
theorem tgt5 : tgtOK 5 = true := by decide +kernel
theorem tgt6 : tgtOK 6 = true := by decide +kernel
theorem tgt7 : tgtOK 7 = true := by decide +kernel
theorem tgt8 : tgtOK 8 = true := by decide +kernel
theorem tgt9 : tgtOK 9 = true := by decide +kernel
theorem tgt10 : tgtOK 10 = true := by decide +kernel

theorem fusTreeOK_eq : fusTreeOK = true := by decide +kernel

theorem alphaN_one_sixtythree : alphaN 1 (false, 63, 0) = (false, 63, 0) := by decide +kernel

theorem alphaN_one_196668 : alphaN 1 (false, 60, 48) = (false, 60, 48) := by decide +kernel

theorem tgt_all : ∀ j < 11, ∀ k < 137, fusTarget j k < 137 ∧
    ∃ w : List ℕ, w.all (· < 24) = true ∧
      walkEnc w (classEnc (fusTarget j k)) = fusF (fusGen j) (fusShift j) (classEnc k) := by
  intro j hj
  interval_cases j
  exacts [tgt_of_tgtOK tgt0, tgt_of_tgtOK tgt1, tgt_of_tgtOK tgt2, tgt_of_tgtOK tgt3,
    tgt_of_tgtOK tgt4, tgt_of_tgtOK tgt5, tgt_of_tgtOK tgt6, tgt_of_tgtOK tgt7, tgt_of_tgtOK tgt8,
    tgt_of_tgtOK tgt9, tgt_of_tgtOK tgt10]

end CertificateChecks.Batch6021

namespace Certificates

open CertificateChecks.Batch6021 in
open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.Census CFSG.Monster.B in
open CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel in
open CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.AxisCount in
open CFSG.Monster.B.TwoA.Census Matrix in
open CFSG.Monster.B.Rep4371 hiding interp interp_eq_sum in
theorem certificate6021 : (((List.range 11).all fun j => match fusionData.generators[j]? with
      | some r => genMatches (fusGen j) r && (ofTriple r.shift == fusShift j)
      | none => false) = true)
    ∧ (∀ j < 11, (fusGen j).validB = true)
    ∧ (∀ j < 11,
      (∃ w : List ℕ, w.all (· < 24) = true ∧
        walkEnc w (classEnc 0) = fusF (fusGen j) (fusShift j) (classEnc 0)) ∧
      (∃ w : List ℕ, w.all (· < 24) = true ∧
        walkEnc w (classEnc 4) = fusF (fusGen j) (fusShift j) (classEnc 4)))
    ∧ (∀ j < 11, ∀ k < 137, fusTarget j k < 137 ∧
      ∃ w : List ℕ, w.all (· < 24) = true ∧
        walkEnc w (classEnc (fusTarget j k)) = fusF (fusGen j) (fusShift j) (classEnc k))
    ∧ (fusTreeOK = true)
    ∧ (alphaN 1 (false, 63, 0) = (false, 63, 0))
    ∧ (alphaN 1 (false, 60, 48) = (false, 60, 48)) :=
  ⟨genMatches_ok, fusGen_valid, fix_of_fixOK fix_ok, tgt_all, fusTreeOK_eq, alphaN_one_sixtythree,
    alphaN_one_196668⟩

end Certificates

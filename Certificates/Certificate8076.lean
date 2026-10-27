module

public import CFSG.Quasithin.Recognition.CertTitsOvergroupCheckInputs
import Certificates.Kernel.LocalQT.Tits4139.Facts
import Certificates.Kernel.Misc.Tits.Merge8076
import CFSG.Certificates.Kernel.Misc.MergeTSound
import Std.Tactic.BVDecide.Normalize.Bool

public section

open CFSG CFSG.Quasithin CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Tits
open CFSG.KC.Enum CFSG.KS.Raw
open CertificateChecks.KernelLocalQT CertificateChecks.KernelSporSch CertificateChecks.KernelMisc
open CFSG.KS.Raw.Orb (unpack_get)

namespace CertificateChecks.Batch8076

open CFSG CFSG.Quasithin CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Tits
open CFSG.KC.Enum CFSG.KS.Raw
open CertificateChecks.KernelLocalQT CertificateChecks.KernelSporSch CertificateChecks.KernelMisc
open CFSG.KS.Raw.Orb (unpack_get)

private theorem arrs_eq : titsSFlagArrs = CFSG.QuasithinUnique.Setup.X6.TitsLat.titsSFlagArrs := rfl

private theorem forest_eq : titsOverForest = CFSG.QuasithinUnique.Setup.X6.TitsLat.titsSFlagForest :=
  rfl

private theorem reps_eq : titsOverReps.toArray = CFSG.QuasithinUnique.Setup.X6.TitsLat.titsSFlagReps :=
  rfl

private theorem fl_eq : allN 13 (fun i => Nat.beq (Tits8076.FL i) (TitsSF.T i)) = true := by
  decide +kernel

private theorem sl_eq : allN 3 (fun i => Nat.beq (Tits8076.SL i) (TitsSW.W i)) = true := by
  decide +kernel

private theorem lab_at {c x : Nat} {p : Nat → Bool} (hx : x < 8775) (hp : p x = true)
    (h : allLt 8775 (fun y => (CFSG.QuasithinUnique.Setup.X6.TitsLat.titsSFlagForest.1[y]! == c) ==
      p y) = true) : titsOverForest.1[x]! = c := by
  rw [CFSG.Monster.B.Co2.allLt_iff] at h
  have := h x hx
  rw [hp] at this
  rw [forest_eq]
  simpa using this

private theorem titsOver_check_0 :
    titsSFlagArrs.size = 3 ∧ titsOverReps.length = 18 ∧
    orbitLabelOK 8775 titsSFlagArrs 18 titsOverForest.1 titsOverReps.toArray titsOverForest.2.1
      titsOverForest.2.2.1 titsOverForest.2.2.2 = true ∧
    (List.range 18).map (labelCount 8775 titsOverForest.1) =
      [1, 2, 4, 8, 8, 16, 32, 64, 64, 128, 256, 512, 512, 1024, 1024, 2048, 1024, 2048] ∧
    (titsOverForest.1[1]! = 1 ∧ titsOverForest.1[3]! = 1) ∧
    (titsOverForest.1[2]! = 2 ∧ titsOverForest.1[5]! = 2 ∧ titsOverForest.1[10]! = 2 ∧
      titsOverForest.1[20]! = 2) ∧
    (∀ c < 18, c ≠ 0 → ∃ i < 3, (titsSFlagArrs[i]!)[titsOverReps[c]!]! ≠ titsOverReps[c]!) ∧
    (∀ j < 15, (titsOverMerge j).length = (titsOverMergeVals.getD j []).length ∧
      mergeTargetsOK 8775 titsTFlagArrs 0 titsOverReps[j + 3]! (mergeVals (titsOverMerge j))
        [1, 2] = true) := by
  obtain ⟨hS, hW⟩ := Tits4139.sGens
  refine ⟨by rw [arrs_eq]; exact hS, rfl, ?_, ?_, ⟨lab_at (by norm_num) (by decide) Tits4139.lab1,
    lab_at (by norm_num) (by decide) Tits4139.lab1⟩, ⟨lab_at (by norm_num) (by decide) Tits4139.lab2,
    lab_at (by norm_num) (by decide) Tits4139.lab2, lab_at (by norm_num) (by decide) Tits4139.lab2,
    lab_at (by norm_num) (by decide) Tits4139.lab2⟩, ?_, ?_⟩
  · rw [arrs_eq, forest_eq, reps_eq]
    exact Tits4139.labS
  · rw [forest_eq]
    exact Tits4139.cntS
  · intro c hc hc0
    obtain ⟨i, hi, hiE⟩ := List.any_eq_true.1 (CFSG.KS.allN_spec Tits8076.moved (c - 1) (by omega))
    rw [List.mem_range] at hi
    refine ⟨i, hi, fun he => ?_⟩
    have hcr : titsOverReps[c - 1 + 1]! = titsOverReps[c]! := by rw [Nat.sub_add_cancel (by omega)]
    rw [hcr] at hiE
    have hlt : titsOverReps[c]! < 8775 := by
      interval_cases c <;> decide
    rw [arrs_eq, hW i hi, unpack_get hlt, ← Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec sl_eq i hi)] at he
    rw [he, Nat.beq_refl] at hiE
    exact absurd hiE Bool.false_ne_true
  · intro j hj
    refine ⟨by simp [titsOverMerge], ?_⟩
    have hm : Tits8076.mOK j = true := by
      interval_cases j
      exacts [Tits8076.m0, Tits8076.m1, Tits8076.m2, Tits8076.m3, Tits8076.m4, Tits8076.m5,
        Tits8076.m6, Tits8076.m7, Tits8076.m8, Tits8076.m9, Tits8076.m10, Tits8076.m11, Tits8076.m12,
        Tits8076.m13, Tits8076.m14]
    exact CFSG.KC.MergeT.mergeTargetsOK_of_mergeTK ⟨TitsStab.tF_size, fun i hi => by
      rw [TitsStab.tF_get hi, Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec fl_eq i hi)]⟩ hm

end CertificateChecks.Batch8076

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Tits in
theorem certificate8076 :
    CFSG.Quasithin.titsSFlagArrs.size = 3 ∧ titsOverReps.length = 18 ∧
    orbitLabelOK 8775 CFSG.Quasithin.titsSFlagArrs 18 titsOverForest.1 titsOverReps.toArray titsOverForest.2.1
      titsOverForest.2.2.1 titsOverForest.2.2.2 = true ∧
    (List.range 18).map (labelCount 8775 titsOverForest.1) =
      [1, 2, 4, 8, 8, 16, 32, 64, 64, 128, 256, 512, 512, 1024, 1024, 2048, 1024, 2048] ∧
    (titsOverForest.1[1]! = 1 ∧ titsOverForest.1[3]! = 1) ∧
    (titsOverForest.1[2]! = 2 ∧ titsOverForest.1[5]! = 2 ∧ titsOverForest.1[10]! = 2 ∧
      titsOverForest.1[20]! = 2) ∧
    (∀ c < 18, c ≠ 0 → ∃ i < 3, (CFSG.Quasithin.titsSFlagArrs[i]!)[titsOverReps[c]!]! ≠ titsOverReps[c]!) ∧
    (∀ j < 15, (titsOverMerge j).length = (titsOverMergeVals.getD j []).length ∧
      mergeTargetsOK 8775 titsTFlagArrs 0 titsOverReps[j + 3]! (mergeVals (titsOverMerge j))
        [1, 2] = true) := by
  exact CertificateChecks.Batch8076.titsOver_check_0

end Certificates

end

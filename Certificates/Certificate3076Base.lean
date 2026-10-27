
module

public import CFSG.Monster.B.TwoA.Sp8.GenActionOrbitInputs
public import CFSG.Certificates.Kernel.SortTreeSound
public import Certificates.Kernel.MonsterB.Sp8OrbData
public import Mathlib.Data.Nat.Bits
import CFSG.Certificates.Kernel.Common.Harness

@[expose] public section

open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.Code CFSG.KC.SortTree
  CFSG.KLie.CT

namespace CertificateChecks.Batch3076

set_option maxRecDepth 100000

theorem exists_bvec : ∀ (n : ℕ) (v : Fin n → ZMod 2), ∃ x < 2 ^ n, bvec n x = v
  | 0, v => ⟨0, by norm_num, funext fun i => i.elim0⟩
  | n + 1, v => by
    obtain ⟨x, hx, e⟩ := exists_bvec n (fun i => v i.succ)
    refine ⟨Nat.bit (decide (v 0 = 1)) x, ?_, funext fun i => ?_⟩
    · rw [Nat.bit_val, pow_succ]
      cases decide (v 0 = 1) <;> simp <;> omega
    · refine Fin.cases ?_ (fun j => ?_) i
      · simp only [bvec, Fin.val_zero, Nat.testBit_bit_zero]
        generalize v 0 = a
        revert a
        decide
      · simp only [bvec, Fin.val_succ, Nat.testBit_bit_succ]
        exact congrFun e j

theorem tV : treeOK vecAct 45 vecValid 1 (recT Sp8Orb.VR 6 28) 255 8 4 8 64 4 = true := by
  quickRfl

theorem eV : closeOK vecAct 45 (recT Sp8Orb.VR 6 28) (fun i k => fget (recT Sp8Orb.VE 6 360 i) k 8)
    255 8 64 4 = true := by quickRfl

theorem vV : allN 255 (fun i => Nat.beq (valF 8 (recT Sp8Orb.VR 6 28 i)) (Nat.succ i)) = true := by
  quickRfl

theorem tT : treeOK tupAct 23 tupValid tupRoot (recT Sp8Orb.TR 6 192) 128 176 3 7 64 2 = true := by
  quickRfl

theorem eT : closeOK tupAct 23 (recT Sp8Orb.TR 6 192) (fun i k => fget (recT Sp8Orb.TE 6 164 i) k 7)
    128 176 64 2 = true := by quickRfl

theorem vec_ok : natCertOK vecAct 45 vecValid 1 vecCert = true ∧ vecCert.pts.size = 255 ∧
    ∀ x < 256, x ≠ 0 → ∃ i < 255, vecCert.pts[i]! = x := by
  obtain ⟨h1, h2, h3⟩ := natBfs_tree (fuel := 300) (by norm_num) (by norm_num) tV eV
  refine ⟨h1, h2, fun x hx h0 => ?_⟩
  have hv := (allN_iff _ _).1 vV (x - 1) (by omega)
  rw [beq_iff] at hv
  obtain ⟨i, hi, e⟩ := Array.mem_iff_getElem.1 ((h3 x).2 ⟨x - 1, by omega, by rw [hv]; omega⟩)
  refine ⟨i, by rw [← h2]; exact hi, ?_⟩
  rw [getElem!_pos vecCert.pts i hi]
  exact e

theorem tup_ok : natCertOK tupAct 23 tupValid tupRoot tupCert = true ∧ tupCert.pts.size = 128 := by
  obtain ⟨h1, h2, -⟩ := natBfs_tree (fuel := 200) (by norm_num) (by norm_num) tT eT
  exact ⟨h1, h2⟩

end CertificateChecks.Batch3076

namespace Certificates

open CertificateChecks

end Certificates

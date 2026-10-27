module

public import Certificates.Kernel.Census.L34
public import CFSG.Certificates.Kernel.Census.E16Sound
public import CFSG.Certificates.Kernel.Census.E16Proof
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourE16Tests
import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourHypIIW
import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import Certificates.Data.Kernel.Census.Packed
import Certificates.Data.Kernel.Census.PackedF
import Certificates.Data.Kernel.Census.PackedE16
import CFSG.Certificates.Kernel.Enum.Defs
import Mathlib.Data.List.Sort
import Init.Data.Nat.Fold
import Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.L34K

open CFSG.KC.Census CFSG.KC.Enum CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoL3Four.HypII
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.Certificates.Native

set_option maxRecDepth 1000000

@[expose] noncomputable def invs : List Nat := l34CS.pts.toList.filter (pisInv 42 6)

@[expose] noncomputable def e16F (u : Nat) : Bool := pe16At 42 6 inP invs u

theorem kE0 : ((invs.drop 0).take 8).all e16F = true := by quickRfl
theorem kE1 : ((invs.drop 8).take 8).all e16F = true := by quickRfl
theorem kE2 : ((invs.drop 16).take 8).all e16F = true := by quickRfl
theorem kE3 : ((invs.drop 24).take 8).all e16F = true := by quickRfl
theorem kE4 : ((invs.drop 32).take 8).all e16F = true := by quickRfl
theorem kE5 : ((invs.drop 40).take 8).all e16F = true := by quickRfl
theorem kE6 : ((invs.drop 48).take 8).all e16F = true := by quickRfl
theorem kE7 : ((invs.drop 56).take 8).all e16F = true := by quickRfl
theorem kEend : (invs.drop 64).all e16F = true := by quickRfl

theorem kE : pe16OK 42 6 inP invs = true := by
  have h := all_drop_chunk (a := 0) (B := 8) kE0 (all_drop_chunk (a := 8) (B := 8) kE1
    (all_drop_chunk (a := 16) (B := 8) kE2 (all_drop_chunk (a := 24) (B := 8) kE3
      (all_drop_chunk (a := 32) (B := 8) kE4 (all_drop_chunk (a := 40) (B := 8) kE5
        (all_drop_chunk (a := 48) (B := 8) kE6 (all_drop_chunk (a := 56) (B := 8) kE7
          kEend)))))))
  rw [List.drop_zero] at h
  exact h

theorem canon_parts : l34SG.toList.all (canon1 42 6) = true ∧
    l34CS.pts.toList.all (canon1 42 6) = true := by
  have h := kCanon
  simp only [canonP, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.2⟩

theorem l34CheckWE16_eq_true : l34CheckWE16 ⟨l34Prog, l34SG, l34CS⟩ = true := by
  obtain ⟨hsg, hcs⟩ := canon_parts
  unfold l34CheckWE16
  rw [gens_eq]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨chain, (pslpOK_eq_proved (by norm_num) (by norm_num) kGc).symm.trans ?_⟩,
    penumOK_sound (by norm_num) (by norm_num) hsg hcs kS⟩, ?_⟩, ?_⟩, ?_⟩
  · unfold pslpOK
    simp only [Bool.and_eq_true]
    refine ⟨?_, kIdx⟩
    refine List.all_eq_true.2 fun k hk => ?_
    have hk' : k < l34GP.size := List.mem_range.1 hk
    rw [getElem!_pos l34GP k hk']
    exact List.all_eq_true.1 kGv _ (Array.getElem_mem_toList hk')
  · rw [allLt_iff]
    intro k hk
    rw [Array.size_map] at hk
    have h := List.all_eq_true.1 kG k (List.mem_range.2 hk)
    simp only [Bool.and_eq_true] at h
    rw [getElem!_map_lt _ _ hk, ← pinXL_slpRegs_proved (by norm_num) (by norm_num) kGc kGv h.1, regs_eq]
    exact h.2
  · simp only [ArrCertP.toMain, Array.size_map]
    decide +kernel
  · have h := pe16OK_eq (inSP := inP) (inS := l34InSW) hcs
      (List.all_eq_true.2 (pvalid_pts_of_penumOK kS)) fun P hP hv => inP_eq hP hv
    simp only [ArrCertP.toMain, Array.toList_map]
    rw [← h]
    exact kE

end CertificateChecks.KernelCensus.L34K

end

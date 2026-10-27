module

public import Certificates.Kernel.Census.J1.Bind
public import Certificates.Kernel.Census.J1.T
public import Certificates.Kernel.Census.J1.N0
public import Certificates.Kernel.Census.J1.N1
public import Certificates.Kernel.Census.J1.N2
public import Certificates.Kernel.Census.J1.N3
public import Certificates.Kernel.Census.J1.N4
public import Certificates.Kernel.Census.J1.N5
public import Certificates.Kernel.Census.J1.N6
public import Certificates.Kernel.Census.J1.P0
public import Certificates.Kernel.Census.J1.P1
public import Certificates.Kernel.Census.J1.P2
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ1W
public import CFSG.Certificates.Kernel.Census.FSound
public import CFSG.Certificates.Kernel.Census.FProof
public import CFSG.Certificates.Kernel.Census.Sound
public import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.Census.ToMainExc
public import CFSG.Certificates.Kernel.Spor.SiftEq
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicExcW
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.Monster.Code.Weights

public section

namespace CertificateChecks.KernelCensus.J1

open CFSG.KC.Census CFSG.KC.Enum CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoSporadic.J1
open CFSG.ComponentClassification.RankTwoSporadic.Cert

set_option maxRecDepth 1000000

#kc_forall_chunks steps_c (fun k => (List.range' (60 * k) 60).all stepF = true) 7
  CertificateChecks.KernelCensus.J1.kT 60

#kc_forall_chunks nodes_c (fun k => nodeF k = true) 7 CertificateChecks.KernelCensus.J1.kN 1

#kc_forall_chunks pairs_c (fun k => pairF k = true) 8 CertificateChecks.KernelCensus.J1.kP 1

theorem regs_eq : pslpRegs 3080 12 j1GP j1Prog = j1RegsP := by
  have hgs : j1GP.size = 2 := Nat.eq_of_beq_eq_true kGS
  have hpl : j1Prog.length = 459 := Nat.eq_of_beq_eq_true kPL
  have hs : ∀ t < 459, stepF t = true := by
    intro t ht
    rcases Nat.lt_or_ge t 420 with h | h
    · have hk : t / 60 < 7 := by omega
      exact List.all_eq_true.1 (steps_c (t / 60) hk) t (List.mem_range'_1.2 ⟨by omega, by omega⟩)
    · exact List.all_eq_true.1 kTt t (List.mem_range'_1.2 ⟨h, by omega⟩)
  have hsz : j1RegsP.size = 2 * j1GP.size + j1Prog.length := by
    rw [hgs, hpl]
    exact Nat.eq_of_beq_eq_true kRS
  have hg := kGs
  simp only [Bool.and_eq_true] at hg
  refine pslpRegs_eq_of_steps_proved hsz (fun k hk => ?_) (fun k hk => ?_) kIdx fun t ht => ?_
  · rw [hgs] at hk
    interval_cases k
    · exact Nat.eq_of_beq_eq_true hg.1
    · exact Nat.eq_of_beq_eq_true hg.2
  · rw [hgs] at hk ⊢
    interval_cases k
    · exact Nat.eq_of_beq_eq_true kI0
    · exact Nat.eq_of_beq_eq_true kI1
  · rw [hpl] at ht
    rw [hgs]
    exact Nat.eq_of_beq_eq_true (hs t ht)

theorem inXP_eq {P : Nat} (hP : canon1 3080 12 P = true) :
    inXP P = inRegsL 3080 (slpRegs 3080 (j1GP.map (unpackP 3080 12)) j1Prog)
      (unpackP 3080 12 P) := by
  rw [← pinXL_slpRegs_proved (by norm_num) (by norm_num) kGc kGv hP, regs_eq]
  rfl

theorem getElem!_map_lt {α β : Type} [Inhabited α] [Inhabited β] (a : Array α) (f : α → β)
    {k : Nat} (hk : k < a.size) : (a.map f)[k]! = f a[k]! := by
  rw [getElem!_pos (a.map f) k (by simpa using hk), Array.getElem_map, getElem!_pos a k hk]

theorem all_getElem! {a : Array Nat} {f : Nat → Bool} (h : a.toList.all f = true) {k : Nat}
    (hk : k < a.size) : f a[k]! = true := by
  rw [getElem!_pos a k hk]
  exact List.all_eq_true.1 h _ (Array.getElem_mem_toList hk)

theorem pairs_ok : j1CS.pts.toList.all (ppairsAt 3080 12 [0, 1, 2] j1Nodes j1CS) = true := by
  refine List.all_eq_true.2 fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hi' : i < j1CS.pts.size := by simpa using hi
  have h8 : i < 8 := Nat.eq_of_beq_eq_true kCs ▸ hi'
  have := pairs_c i h8
  unfold pairF at this
  rwa [getElem!_pos _ i hi', ← Array.getElem_toList] at this

theorem j1_ok : ∃ (prog : List (ℕ × ℕ)) (sG : Array ℕ) (nodes : Array FNodeP) (cS : ArrCertP),
    j1CheckW prog sG nodes cS = true := by
  have hin : ∀ P, canon1 3080 12 P = true → pvalid 3080 12 P = true →
      inXP P = inRegsL 3080 (slpRegs 3080 (j1GP.map (unpackP 3080 12)) j1Prog)
        (unpackP 3080 12 P) := fun P hP _ => inXP_eq hP
  have hN : ∀ k < j1Nodes.size, pfullOK 3080 12 inXP j1GP j1Nodes[k]! = true := by
    rw [Nat.eq_of_beq_eq_true kNs]
    intro k hk
    exact nodes_c k hk
  have hcensus := pfCensus_sound (by norm_num) (by norm_num) (by norm_num) kSc kGc kNc kCc hin
    kS kX hN pairs_ok
  refine ⟨j1Prog, j1SG, j1Nodes, j1CS, ?_⟩
  unfold j1CheckW
  rw [gens_eq]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨(pslpOK_eq_proved (by norm_num) (by norm_num) kGc).symm.trans kSlp, hcensus⟩, ?_⟩, ?_⟩
  · rw [allLt_iff]
    intro k hk
    rw [Array.size_map] at hk
    rw [getElem!_map_lt _ _ hk, ← inXP_eq (all_getElem! kSc hk)]
    exact List.all_eq_true.1 kG k (List.mem_range.2 hk)
  · simp only [ArrCertP.toMain, Array.size_map]
    exact Nat.eq_of_beq_eq_true kCs

end CertificateChecks.KernelCensus.J1

end

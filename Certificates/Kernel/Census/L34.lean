module

public import Certificates.Kernel.Census.L34Chain
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourHypIIPk
public import CFSG.Certificates.Kernel.Census.FProof
public import CFSG.Certificates.Kernel.Census.SiftSound
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourHypIIW
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourHypIITests
import all Certificates.Data.CFSGNative.MonsterB.Co2Chain
import all Certificates.Data.Kernel.Census.Packed
import all Certificates.Data.Kernel.Census.PackedF
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Census.ToMainExc
public import CFSG.Certificates.Kernel.Census.ToMainF
public import CFSG.Certificates.Kernel.Spor.SiftEq
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicExcW
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFullW
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.Monster.Code.Weights

public section

namespace CertificateChecks.KernelCensus.L34K

open CFSG.KC.Census CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoL3Four.HypII
open CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.Certificates.Native

set_option maxRecDepth 1000000

@[expose] noncomputable def inP (P : Nat) : Bool :=
  siftK 42 6 (mask 6) (42 * 6) (pidn 42 6) L34C.LR L34C.TRI L34C.BP 4 0 P

theorem binds : Binds 42 6 L34C.S 9 4 L34C.BP l34SW l34BaseW := by
  have h : l34SW.size = 9 ∧ (∀ j < 9, l34SW[j]! = unpack 42 6 (L34C.S j)) ∧
      l34BaseW.size = 4 ∧ ∀ t < 4, l34BaseW[t]! = pg 6 (mask 6) L34C.BP t := by
    decide +kernel
  exact ⟨by norm_num, by norm_num, by norm_num, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem hperm : allN 9 (fun j => permOK 42 6 (mask 6) (42 * 6) (L34C.S j) (L34C.SI j)) = true := by
  quickRfl

theorem inP_eq {P : Nat} (hP : canon1 42 6 P = true) (hv : pvalid 42 6 P = true) :
    inP P = l34InSW (unpackP 42 6 P) := by
  have hG : Nat.shiftRight P (42 * 6) = 0 := by
    simpa [canon1] using hP
  unfold inP l34InSW
  exact (siftK_eq binds hperm L34C.hl rfl hG (range_of_pvalid hv)).symm

theorem chain : rawChainOK 42 (l34SW.extract 0 3) l34SW l34BaseW
    (CFSG.EvenSmallLie.OmegaEight.wordsOf 3 l34DW) 4 = true := by
  have hw : CFSG.EvenSmallLie.OmegaEight.wordsOf 3 l34DW =
      CFSG.Sporadic.Schreier.Co3.Native.wordsArr 3 9 l34DW := by
    decide +kernel
  rw [hw]
  exact rawChainK_sound (NS := 1) (CH := 42) (chunks := 4) binds L34C.head L34C.hl
    (by norm_num) L34C.hs

@[expose] noncomputable def stepF (t : Nat) : Bool :=
  Nat.beq l34RegsP[12 + t]! (pc 42 6 l34RegsP[(l34Prog.getD t (0, 0)).1]!
    l34RegsP[(l34Prog.getD t (0, 0)).2]!)

theorem kPL : Nat.beq l34Prog.length 1067 = true := by quickRfl

theorem kT0 : (List.range' 0 270).all stepF = true := by quickRfl
theorem kT1 : (List.range' 270 270).all stepF = true := by quickRfl
theorem kT2 : (List.range' 540 270).all stepF = true := by quickRfl
theorem kT3 : (List.range' 810 257).all stepF = true := by quickRfl

theorem kT : ∀ t < l34Prog.length, stepF t = true := by
  rw [Nat.eq_of_beq_eq_true kPL]
  exact allRange_extend (a := 810) (len := 257) (allRange_extend (a := 540) (len := 270)
    (allRange_extend (a := 270) (len := 270) (allRange_extend (a := 0) (len := 270)
      (allRange_zero _) kT0) kT1) kT2) kT3

theorem kRS : Nat.beq l34RegsP.size (12 + l34Prog.length) = true := by quickRfl

theorem kGS : Nat.beq l34GP.size 6 = true := by quickRfl

theorem kGr : ((List.range 6).all fun k => Nat.beq l34RegsP[k]! l34GP[k]! &&
    Nat.beq l34RegsP[6 + k]! (pinv 42 6 l34GP[k]!)) = true := by quickRfl

theorem kIdx : pslpIdxOK (2 * l34GP.size) l34Prog = true := by quickRfl

theorem regs_eq : pslpRegs 42 6 l34GP l34Prog = l34RegsP := by
  have hgs : l34GP.size = 6 := Nat.eq_of_beq_eq_true kGS
  have hsz : l34RegsP.size = 2 * l34GP.size + l34Prog.length := by
    rw [hgs]
    exact Nat.eq_of_beq_eq_true kRS
  refine pslpRegs_eq_of_steps_proved hsz (fun k hk => ?_) (fun k hk => ?_) kIdx fun t ht => ?_
  · rw [hgs] at hk
    have h := List.all_eq_true.1 kGr k (List.mem_range.2 hk)
    simp only [Bool.and_eq_true] at h
    exact Nat.eq_of_beq_eq_true h.1
  · rw [hgs] at hk ⊢
    have h := List.all_eq_true.1 kGr k (List.mem_range.2 hk)
    simp only [Bool.and_eq_true] at h
    exact Nat.eq_of_beq_eq_true h.2
  · rw [hgs]
    exact Nat.eq_of_beq_eq_true (kT t ht)

theorem kGc : l34GP.toList.all (canon1 42 6) = true := by quickRfl

theorem kGv : l34GP.toList.all (pvalid 42 6) = true := by quickRfl

theorem gens_eq : l34GensR = l34GP.map (unpackP 42 6) := by decide +kernel

theorem kCanon : canonP 42 6 l34SG l34Nodes l34CS l34WCS = true := by quickRfl

theorem kS : penumOK 42 6 l34SG l34PS l34CS = true := by quickRfl

theorem kR : ((List.range l34CS.pts.size).all fun p =>
    prootOK 42 6 l34Nodes (pcN 42 6 l34Nodes) l34CS.pts[p]! l34Roots[p]!) = true := by quickRfl

@[expose] noncomputable def nodeF (i : Nat) : Bool :=
  pnodeOK 42 6 l34PS inP inP false true false l34CS l34Nodes (pcN 42 6 l34Nodes) l34WCS i

theorem kN0 : (List.range' 0 62).all nodeF = true := by quickRfl
theorem kN1 : (List.range' 62 62).all nodeF = true := by quickRfl
theorem kN2 : (List.range' 124 62).all nodeF = true := by quickRfl
theorem kN3 : (List.range' 186 62).all nodeF = true := by quickRfl

theorem kNS : Nat.beq l34Nodes.size 248 = true := by quickRfl

theorem kG : ((List.range l34SG.size).all fun k =>
    canon1 42 6 l34SG[k]! && pinXL l34RegsP l34SG[k]!) = true := by quickRfl

theorem getElem!_map_lt {α β : Type} [Inhabited α] [Inhabited β] (a : Array α) (f : α → β)
    {k : Nat} (hk : k < a.size) : (a.map f)[k]! = f a[k]! := by
  rw [getElem!_pos (a.map f) k (by simpa using hk), Array.getElem_map, getElem!_pos a k hk]

theorem l34CheckWII_eq_true : l34CheckWII l34Prog l34SG l34Roots l34Nodes l34CS l34WCS = true := by
  have hin : ∀ P, canon1 42 6 P = true → pvalid 42 6 P = true →
      inP P = l34InSW (unpackP 42 6 P) := fun P hP hv => inP_eq hP hv
  have hN : ∀ i < l34Nodes.size, nodeF i = true := by
    rw [Nat.eq_of_beq_eq_true kNS]
    exact allRange_extend (a := 186) (len := 62) (allRange_extend (a := 124) (len := 62)
      (allRange_extend (a := 62) (len := 62) (allRange_extend (a := 0) (len := 62)
        (allRange_zero _) kN0) kN1) kN2) kN3
  have hcensus := pcensus_sound_proved (by norm_num) (by norm_num) kCanon hin hin kS kR hN
  unfold l34CheckWII
  rw [gens_eq]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨chain, (pslpOK_eq_proved (by norm_num) (by norm_num) kGc).symm.trans ?_⟩, hcensus⟩, ?_⟩, ?_⟩
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

end CertificateChecks.KernelCensus.L34K

end

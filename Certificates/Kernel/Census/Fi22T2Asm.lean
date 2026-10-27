module

public import Certificates.Kernel.Census.Fi22T2M0
public import Certificates.Kernel.Census.Fi22T2M1
public import Certificates.Kernel.Census.Fi22T2M2
public import Certificates.Kernel.Census.Fi22T2M3
public import Certificates.Kernel.Census.Fi22T2M4
public import Certificates.Kernel.Census.Fi22T2H0
public import Certificates.Kernel.Census.Fi22T2H1
public import Certificates.Kernel.Census.Fi22T2H2
public import Certificates.Kernel.Census.Fi22T2H3
public import Certificates.Kernel.Census.Fi22T2H4
public import Certificates.Kernel.Census.Fi22T2H5
public import Certificates.Kernel.Census.Fi22T2H6
public import Certificates.Kernel.Census.Fi22T2H7
public import Certificates.Kernel.Census.Fi22T2H8
public import Certificates.Kernel.Census.Fi22T2V0
public import Certificates.Kernel.Census.Fi22T2V1
public import Certificates.Kernel.Census.Fi22T2V2
public import Certificates.Kernel.Census.Fi22T2V3
public import Certificates.Kernel.Census.Fi22T2EP
public import Certificates.Kernel.Census.Fi22T2OP
public import CFSG.Certificates.Kernel.Census.PackedRootPProof
public import CFSG.Certificates.Kernel.Census.RootConjJoin
public import CFSG.Certificates.Kernel.Census.ConjFSound
public import CFSG.Certificates.Kernel.Census.Sound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi22Tests
import Certificates.Kernel.Census.Fi22RDefs
import Certificates.Kernel.Census.Fi22RDefsT2
import Certificates.Kernel.Census.Fi22PkT2R
import Certificates.Kernel.Census.Fi22PkT2A
import Certificates.Kernel.Census.Fi22PkT2W
import Certificates.Data.Kernel.Census.PackedRootBit
import Certificates.Data.Kernel.Census.PackedRoot
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Census.ToMainConj
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Pair
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Roots
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.Monster.Code.Weights
public import CFSG.Sporadic.SmallOddCore.CheckSpec

public section

namespace CertificateChecks.KernelCensus.Fi22K.T2

set_option maxRecDepth 1000000

open CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Fi22
  CertificateChecks.KernelCensus.Fi22K

theorem kWtL : (fi22T2Wt.all fun b => Nat.beq b.length 4096) = true := by quickRfl

theorem kWtN : Nat.beq fi22T2Wt.length 32 = true := by quickRfl

theorem kImEnd : (fi22T2Im.filter fun m => Nat.ble 131072 m).isEmpty = true := by quickRfl

theorem kNum : Nat.beq (usize fi22T2Root.ukc) 3775 = true := by quickRfl

theorem walkT2 : pinvRest 3510 12 fi22T2Root.xs 0 fi22T2Root.im fi22T2Root.wt.flatten = some [] := by
  have hf : (fi22T2Im.filter fun m => Nat.ble 0 m) = fi22T2Im := List.filter_eq_self.2 fun m _ => by
    simp [Nat.ble_eq]
  have hl : ∀ b ∈ fi22T2Wt, b.length = 4096 := fun b hb =>
    Nat.eq_of_beq_eq_true (List.all_eq_true.1 kWtL b hb)
  have hn : fi22T2Wt.length = 32 := Nat.eq_of_beq_eq_true kWtN
  have h := pinvRest_blocks (n := 3510) (w := 12) (xs := fi22T2Xs) (L := 4096)
    (f := fun t => fi22T2Im.filter fun m => Nat.ble t m) fi22T2Wt 0 hl (fun c hc => by
      rw [hn] at hc
      simp only [Nat.zero_add]
      interval_cases c
      exacts [beq_iff_eq.1 kV0, beq_iff_eq.1 kV1, beq_iff_eq.1 kV2, beq_iff_eq.1 kV3,
        beq_iff_eq.1 kV4, beq_iff_eq.1 kV5, beq_iff_eq.1 kV6, beq_iff_eq.1 kV7, beq_iff_eq.1 kV8,
        beq_iff_eq.1 kV9, beq_iff_eq.1 kV10, beq_iff_eq.1 kV11, beq_iff_eq.1 kV12,
        beq_iff_eq.1 kV13, beq_iff_eq.1 kV14, beq_iff_eq.1 kV15, beq_iff_eq.1 kV16,
        beq_iff_eq.1 kV17, beq_iff_eq.1 kV18, beq_iff_eq.1 kV19, beq_iff_eq.1 kV20,
        beq_iff_eq.1 kV21, beq_iff_eq.1 kV22, beq_iff_eq.1 kV23, beq_iff_eq.1 kV24,
        beq_iff_eq.1 kV25, beq_iff_eq.1 kV26, beq_iff_eq.1 kV27, beq_iff_eq.1 kV28,
        beq_iff_eq.1 kV29, beq_iff_eq.1 kV30, beq_iff_eq.1 kV31])
  simp only [hf, hn] at h
  change pinvRest 3510 12 fi22T2Xs 0 fi22T2Im (fi22T2Wt.flatten) = some []
  rw [h, List.isEmpty_iff.1 kImEnd]

theorem headsT2 : ppcOK 3510 12 fi22T2Root.xs fi22T2Root.rs fi22T2Root.cjs fi22T2Root.bs = true :=
  ppcOK_of_heads _ _ _ _ fun j hj => by
    have hk : fi22T2Xs.length = 17 := by decide
    change j ≤ fi22T2Xs.length at hj
    rw [hk] at hj
    interval_cases j
    exacts [kH0, kH1, kH2, kH3, kH4, kH5, kH6, kH7, kH8, kH9, kH10, kH11, kH12, kH13, kH14, kH15,
      kH16, kH17]

theorem entsT2 : (List.range (usize fi22T2Root.ukc)).all entT2 = true := by
  have hs : usize fi22T2Root.ukc = 3775 := Nat.eq_of_beq_eq_true kNum
  have eP : ∀ {a len : Nat},
      pentBlkP 3510 12 3775 inXK [] #[] 10 fi22T2Root a len = true →
        (List.range' a len).all entT2 = true := fun h => by
    rw [pentBlkP_eq kFit hs] at h
    exact h
  rw [hs]
  have hb := allRange_blocks (a := 0) (L := 512) (C := 7) (f := entT2) (allRange_zero _)
    fun c hc => by
      simp only [Nat.zero_add]
      interval_cases c
      exacts [eP kEP0, eP kEP1, eP kEP2, eP kEP3, eP kEP4, eP kEP5, eP kEP6]
  have h := allRange_extend (a := 3584) (len := 191) hb (eP kEP7)
  exact List.all_eq_true.2 fun i hi => h i (List.mem_range.1 hi)

theorem orderT2 : pordOK 3510 12 fi22T2Root = true := by
  have hs : usize fi22T2Root.ukc = 3775 := Nat.eq_of_beq_eq_true kNum
  have oP : ∀ {a len : Nat}, pordBlkP 3510 12 fi22T2Root a len = true →
      (List.range' a len).all (fun i =>
        Nat.blt (pkeyU 3510 12 fi22T2Root i) (pkeyU 3510 12 fi22T2Root (i + 1))) = true :=
    fun h => by
      rw [pordBlkP_eq kFit] at h
      exact h
  unfold pordOK
  rw [hs]
  have hb := allRange_blocks (a := 0) (L := 512) (C := 7) (allRange_zero _) fun c hc => by
      simp only [Nat.zero_add]
      interval_cases c
      exacts [oP kOP0, oP kOP1, oP kOP2, oP kOP3, oP kOP4, oP kOP5, oP kOP6]
  have h := allRange_extend (a := 3584) (len := 190) hb (oP kOP7)
  exact List.all_eq_true.2 fun i hi => h i (List.mem_range.1 hi)

theorem rootII_ok : prootConjOKB 3510 12 fi22PS inXK inWK false 2 [] 10 fi22T2Root = true := by
  have h0a := kM0a
  have h0b := kM0b
  have h0g := kM0g
  have h0c := kM0c
  simp only [Bool.and_eq_true] at h0a h0b h0g h0c
  have h1 := kM1k
  simp only [Bool.and_eq_true] at h1
  have hw : (pinvRest 3510 12 fi22T2Root.xs 0 fi22T2Root.im fi22T2Root.wt.flatten == some []) = true := by
    rw [walkT2]
    rfl
  have hpf : fi22T2Root.perfs.toList.all (pperfOK 3510 12 fi22PS fi22T2Root.ga) = true := by simp [fi22T2Root]
  have he : (List.range (usize fi22T2Root.ukc)).all
      (pentryOKB 3510 12 inXK 2 [] (fi22T2Root.perfs.map (pperfGens 3510 12 fi22T2Root.ga)) 10 fi22T2Root) =
        true := by
    have hp : fi22T2Root.perfs.map (pperfGens 3510 12 fi22T2Root.ga) = #[] := by simp [fi22T2Root]
    rw [hp]
    exact List.all_eq_true.2 fun j hj =>
      ((CFSG.KS.bAnd_iff _ _).1 (List.all_eq_true.1 entsT2 j hj)).1
  unfold prootConjOKB
  simp only [h0a, h0b, h0g, h0c, h1, kM1, kM2, headsT2, hw, hpf, he, orderT2, Bool.and_true,
    Bool.true_or, Bool.or_true]

theorem root17_ok : prootConjOKB 3510 12 fi22PS inXK inWK true 1 [] 10 fi22T2Root = true := by
  have h0a := kM0a
  have h0b := kM0b
  have h0g := kM0g
  have h0c := kM0c
  simp only [Bool.and_eq_true] at h0a h0b h0g h0c
  have h1 := kM1k
  simp only [Bool.and_eq_true] at h1
  have hw : (pinvRest 3510 12 fi22T2Root.xs 0 fi22T2Root.im fi22T2Root.wt.flatten == some []) = true := by
    rw [walkT2]
    rfl
  have hpf : fi22T2Root.perfs.toList.all (pperfOK 3510 12 fi22PS fi22T2Root.ga) = true := by simp [fi22T2Root]
  have he : (List.range (usize fi22T2Root.ukc)).all
      (pentryOKB 3510 12 inXK 1 [] (fi22T2Root.perfs.map (pperfGens 3510 12 fi22T2Root.ga)) 10 fi22T2Root) =
        true := by
    have hp : fi22T2Root.perfs.map (pperfGens 3510 12 fi22T2Root.ga) = #[] := by simp [fi22T2Root]
    rw [hp]
    exact List.all_eq_true.2 fun j hj =>
      ((CFSG.KS.bAnd_iff _ _).1 (List.all_eq_true.1 entsT2 j hj)).2
  unfold prootConjOKB
  simp only [h0a, h0b, h0g, h0c, h1, kM1, kM2, headsT2, hw, hpf, he, orderT2, Bool.and_true,
    Bool.true_or, Bool.or_true]

end CertificateChecks.KernelCensus.Fi22K.T2

end

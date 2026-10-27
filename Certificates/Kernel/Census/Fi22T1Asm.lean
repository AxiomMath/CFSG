module

public import Certificates.Kernel.Census.Fi22T1M0
public import Certificates.Kernel.Census.Fi22T1M1
public import Certificates.Kernel.Census.Fi22T1M2
public import Certificates.Kernel.Census.Fi22T1M3
public import Certificates.Kernel.Census.Fi22T1M4
public import Certificates.Kernel.Census.Fi22T1H0
public import Certificates.Kernel.Census.Fi22T1H1
public import Certificates.Kernel.Census.Fi22T1H2
public import Certificates.Kernel.Census.Fi22T1H3
public import Certificates.Kernel.Census.Fi22T1H4
public import Certificates.Kernel.Census.Fi22T1H5
public import Certificates.Kernel.Census.Fi22T1H6
public import Certificates.Kernel.Census.Fi22T1H7
public import Certificates.Kernel.Census.Fi22T1H8
public import Certificates.Kernel.Census.Fi22T1H9
public import Certificates.Kernel.Census.Fi22T1V0
public import Certificates.Kernel.Census.Fi22T1V1
public import Certificates.Kernel.Census.Fi22T1V2
public import Certificates.Kernel.Census.Fi22T1V3
public import Certificates.Kernel.Census.Fi22T1V4
public import Certificates.Kernel.Census.Fi22T1V5
public import Certificates.Kernel.Census.Fi22T1V6
public import Certificates.Kernel.Census.Fi22T1V7
public import Certificates.Kernel.Census.Fi22T1EP
public import Certificates.Kernel.Census.Fi22T1OP
public import CFSG.Certificates.Kernel.Census.PackedRootPProof
public import CFSG.Certificates.Kernel.Census.RootConjJoin
public import CFSG.Certificates.Kernel.Census.ConjFSound
public import CFSG.Certificates.Kernel.Census.Sound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi22Tests
import Certificates.Kernel.Census.Fi22RDefs
import Certificates.Kernel.Census.Fi22RDefsT1
import Certificates.Kernel.Census.Fi22PkT1R
import Certificates.Kernel.Census.Fi22PkT1A
import Certificates.Kernel.Census.Fi22PkT1W
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

namespace CertificateChecks.KernelCensus.Fi22K.T1

set_option maxRecDepth 1000000

open CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Fi22
  CertificateChecks.KernelCensus.Fi22K

theorem kWtL : (fi22T1Wt.all fun b => Nat.beq b.length 4096) = true := by quickRfl

theorem kWtN : Nat.beq fi22T1Wt.length 64 = true := by quickRfl

theorem kImEnd : (fi22T1Im.filter fun m => Nat.ble 262144 m).isEmpty = true := by quickRfl

theorem kNum : Nat.beq (usize fi22T1Root.ukc) 6143 = true := by quickRfl

theorem walkT1 : pinvRest 3510 12 fi22T1Root.xs 0 fi22T1Root.im fi22T1Root.wt.flatten = some [] := by
  have hf : (fi22T1Im.filter fun m => Nat.ble 0 m) = fi22T1Im := List.filter_eq_self.2 fun m _ => by
    simp [Nat.ble_eq]
  have hl : ∀ b ∈ fi22T1Wt, b.length = 4096 := fun b hb =>
    Nat.eq_of_beq_eq_true (List.all_eq_true.1 kWtL b hb)
  have hn : fi22T1Wt.length = 64 := Nat.eq_of_beq_eq_true kWtN
  have h := pinvRest_blocks (n := 3510) (w := 12) (xs := fi22T1Xs) (L := 4096)
    (f := fun t => fi22T1Im.filter fun m => Nat.ble t m) fi22T1Wt 0 hl (fun c hc => by
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
        beq_iff_eq.1 kV29, beq_iff_eq.1 kV30, beq_iff_eq.1 kV31, beq_iff_eq.1 kV32,
        beq_iff_eq.1 kV33, beq_iff_eq.1 kV34, beq_iff_eq.1 kV35, beq_iff_eq.1 kV36,
        beq_iff_eq.1 kV37, beq_iff_eq.1 kV38, beq_iff_eq.1 kV39, beq_iff_eq.1 kV40,
        beq_iff_eq.1 kV41, beq_iff_eq.1 kV42, beq_iff_eq.1 kV43, beq_iff_eq.1 kV44,
        beq_iff_eq.1 kV45, beq_iff_eq.1 kV46, beq_iff_eq.1 kV47, beq_iff_eq.1 kV48,
        beq_iff_eq.1 kV49, beq_iff_eq.1 kV50, beq_iff_eq.1 kV51, beq_iff_eq.1 kV52,
        beq_iff_eq.1 kV53, beq_iff_eq.1 kV54, beq_iff_eq.1 kV55, beq_iff_eq.1 kV56,
        beq_iff_eq.1 kV57, beq_iff_eq.1 kV58, beq_iff_eq.1 kV59, beq_iff_eq.1 kV60,
        beq_iff_eq.1 kV61, beq_iff_eq.1 kV62, beq_iff_eq.1 kV63])
  simp only [hf, hn] at h
  change pinvRest 3510 12 fi22T1Xs 0 fi22T1Im (fi22T1Wt.flatten) = some []
  rw [h, List.isEmpty_iff.1 kImEnd]

theorem headsT1 : ppcOK 3510 12 fi22T1Root.xs fi22T1Root.rs fi22T1Root.cjs fi22T1Root.bs = true :=
  ppcOK_of_heads _ _ _ _ fun j hj => by
    have hk : fi22T1Xs.length = 18 := by decide
    change j ≤ fi22T1Xs.length at hj
    rw [hk] at hj
    interval_cases j
    exacts [kH0, kH1, kH2, kH3, kH4, kH5, kH6, kH7, kH8, kH9, kH10, kH11, kH12, kH13, kH14, kH15,
      kH16, kH17, kH18]

theorem entsT1 : (List.range (usize fi22T1Root.ukc)).all entT1 = true := by
  have hs : usize fi22T1Root.ukc = 6143 := Nat.eq_of_beq_eq_true kNum
  have eP : ∀ {a len : Nat},
      pentBlkP 3510 12 6143 inXK [694] #[] 16 fi22T1Root a len = true →
        (List.range' a len).all entT1 = true := fun h => by
    rw [pentBlkP_eq kFit hs] at h
    exact h
  rw [hs]
  have hb := allRange_blocks (a := 0) (L := 512) (C := 11) (f := entT1) (allRange_zero _)
    fun c hc => by
      simp only [Nat.zero_add]
      interval_cases c
      exacts [eP kEP0, eP kEP1, eP kEP2, eP kEP3, eP kEP4, eP kEP5, eP kEP6, eP kEP7, eP kEP8,
        eP kEP9, eP kEP10]
  have h := allRange_extend (a := 5632) (len := 511) hb (eP kEP11)
  exact List.all_eq_true.2 fun i hi => h i (List.mem_range.1 hi)

theorem orderT1 : pordOK 3510 12 fi22T1Root = true := by
  have hs : usize fi22T1Root.ukc = 6143 := Nat.eq_of_beq_eq_true kNum
  have oP : ∀ {a len : Nat}, pordBlkP 3510 12 fi22T1Root a len = true →
      (List.range' a len).all (fun i =>
        Nat.blt (pkeyU 3510 12 fi22T1Root i) (pkeyU 3510 12 fi22T1Root (i + 1))) = true :=
    fun h => by
      rw [pordBlkP_eq kFit] at h
      exact h
  unfold pordOK
  rw [hs]
  have hb := allRange_blocks (a := 0) (L := 512) (C := 11) (allRange_zero _) fun c hc => by
      simp only [Nat.zero_add]
      interval_cases c
      exacts [oP kOP0, oP kOP1, oP kOP2, oP kOP3, oP kOP4, oP kOP5, oP kOP6, oP kOP7, oP kOP8,
        oP kOP9, oP kOP10]
  have h := allRange_extend (a := 5632) (len := 510) hb (oP kOP11)
  exact List.all_eq_true.2 fun i hi => h i (List.mem_range.1 hi)

theorem rootII_ok : prootConjOKB 3510 12 fi22PS inXK inWK false 2 [694] 16 fi22T1Root = true := by
  have h0a := kM0a
  have h0b := kM0b
  have h0g := kM0g
  have h0c := kM0c
  simp only [Bool.and_eq_true] at h0a h0b h0g h0c
  have h1 := kM1k
  simp only [Bool.and_eq_true] at h1
  have hw : (pinvRest 3510 12 fi22T1Root.xs 0 fi22T1Root.im fi22T1Root.wt.flatten == some []) = true := by
    rw [walkT1]
    rfl
  have hpf : fi22T1Root.perfs.toList.all (pperfOK 3510 12 fi22PS fi22T1Root.ga) = true := by simp [fi22T1Root]
  have he : (List.range (usize fi22T1Root.ukc)).all
      (pentryOKB 3510 12 inXK 2 [694] (fi22T1Root.perfs.map (pperfGens 3510 12 fi22T1Root.ga)) 16 fi22T1Root) =
        true := by
    have hp : fi22T1Root.perfs.map (pperfGens 3510 12 fi22T1Root.ga) = #[] := by simp [fi22T1Root]
    rw [hp]
    exact List.all_eq_true.2 fun j hj =>
      ((CFSG.KS.bAnd_iff _ _).1 (List.all_eq_true.1 entsT1 j hj)).1
  unfold prootConjOKB
  simp only [h0a, h0b, h0g, h0c, h1, kM1, kM2, headsT1, hw, hpf, he, orderT1, Bool.and_true,
    Bool.true_or, Bool.or_true]

theorem root17_ok : prootConjOKB 3510 12 fi22PS inXK inWK true 1 [694] 16 fi22T1Root = true := by
  have h0a := kM0a
  have h0b := kM0b
  have h0g := kM0g
  have h0c := kM0c
  simp only [Bool.and_eq_true] at h0a h0b h0g h0c
  have h1 := kM1k
  simp only [Bool.and_eq_true] at h1
  have hw : (pinvRest 3510 12 fi22T1Root.xs 0 fi22T1Root.im fi22T1Root.wt.flatten == some []) = true := by
    rw [walkT1]
    rfl
  have hpf : fi22T1Root.perfs.toList.all (pperfOK 3510 12 fi22PS fi22T1Root.ga) = true := by simp [fi22T1Root]
  have he : (List.range (usize fi22T1Root.ukc)).all
      (pentryOKB 3510 12 inXK 1 [694] (fi22T1Root.perfs.map (pperfGens 3510 12 fi22T1Root.ga)) 16 fi22T1Root) =
        true := by
    have hp : fi22T1Root.perfs.map (pperfGens 3510 12 fi22T1Root.ga) = #[] := by simp [fi22T1Root]
    rw [hp]
    exact List.all_eq_true.2 fun j hj =>
      ((CFSG.KS.bAnd_iff _ _).1 (List.all_eq_true.1 entsT1 j hj)).2
  unfold prootConjOKB
  simp only [h0a, h0b, h0g, h0c, h1, kM1, kM2, headsT1, hw, hpf, he, orderT1, Bool.and_true,
    Bool.true_or, Bool.or_true]

end CertificateChecks.KernelCensus.Fi22K.T1

end

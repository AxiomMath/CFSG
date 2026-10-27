module

public import Certificates.Data.Co1FiveRank
public meta import Certificates.Data.Co1FiveRank
public import Certificates.Kernel.Co1B.Chk431007
public import Certificates.Kernel.Co1B.Lvl431007A
public import Certificates.Kernel.Co1B.Lvl431007B
public import Certificates.Kernel.Co1B.C17330
public import Certificates.Kernel.Co1B.C2041
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Monster.B.TwoA.Par3.Main

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound431007

open CFSG.KC.Co1BBoundP (lvlChunkP)
open CFSG.KC.Co1BBoundN CFSG.KC.Co1BBound CFSG.KC.Co1BSpin CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.M1F2
  CFSG.KLie.CT CFSG.KC.Enum CFSG.HardMathSupport.Dickson.I271.TabCo1
  CFSG.LocalAnalysis.GLTheoremA.H1017.Co1FiveNative CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1.TwoBNative
  CFSG.Sporadic.Co1.InvNative
open CertificateChecks.KernelCo1B.Bound17591 (XB)
open CertificateChecks.KernelCo1B.Bound17330 (boundOK_of_sel not_of_notB mul_unpackW')
open CFSG.KS.SporSch.M24 (unpackR_eq_unpack dagWK_sound gtBFS_of_K bfsTree gensArr gtPinK)

theorem DF_base : [aR, bR] = (List.range 2).map fun i => CFSG.KS.Raw.unpack 24 24 (DF.M i) := by
  have h := kDFB
  simp only [Bool.and_eq_true] at h
  have e0 : DF.M 0 = CertificateChecks.KernelCo1ThreeK.SM 0 := Nat.eq_of_beq_eq_true h.1
  have e1 : DF.M 1 = CertificateChecks.KernelCo1ThreeK.SM 1 := Nat.eq_of_beq_eq_true h.2
  rw [CertificateChecks.KernelCo1ThreeK.base_eq]
  refine List.map_congr_left fun i hi => ?_
  have hi2 : i < 2 := List.mem_range.1 hi
  interval_cases i
  · rw [e0]
  · rw [e1]

theorem kDag5_eq : kDag ext5 = ((List.range 95).map fun i => CFSG.KS.Raw.unpack 24 24 (DF.M i),
    (List.range 95).map fun i => CFSG.KS.Raw.unpack 24 24 (DF.MI i), true) := by
  rw [kDag, ← kDFW]
  exact dagWK_sound DF_base kDF

theorem hflag : (kDag ext5).2.2 = true := by
  rw [kDag5_eq]

theorem nd_eq {i : Nat} (h1 : 0 < i) (h2 : i ≤ 95) :
    nd (kDag ext5) i = unpackR 24 (DF.M (i - 1)) := by
  rw [nd, kDag5_eq,
    List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega),
    List.getElem_map, List.getElem_range, unpackR_eq_unpack]

theorem k_eq : nd (kDag ext5) 88 = unpackR 24 KK := nd_eq (by decide) (by decide)
theorem t_eq : nd (kDag ext5) 91 = unpackR 24 TK := nd_eq (by decide) (by decide)
theorem c_eq : nd (kDag ext5) 92 = unpackR 24 CK := nd_eq (by decide) (by decide)
theorem c2_eq : nd (kDag ext5) 93 = unpackR 24 C2K := nd_eq (by decide) (by decide)
theorem d_eq : nd (kDag ext5) 94 = unpackR 24 DK := nd_eq (by decide) (by decide)
theorem x2_eq : nd (kDag ext5) 95 = unpackR 24 X2K := nd_eq (by decide) (by decide)

theorem comm_unpack {A B : Nat} (h : eqK (mulWK A B) (mulWK B A) = true) :
    (mul (unpackR 24 A) (unpackR 24 B) == mul (unpackR 24 B) (unpackR 24 A)) = true := by
  rw [mul_unpackW', mul_unpackW', beq_unpack]
  exact h

theorem side_parts {t f₁ f₂ f₃ nfix : Nat} (h : sideK t f₁ f₂ f₃ nfix = true) :
    (mul (unpackR 24 t) (unpackR 24 t) == one ()) = true ∧ validRows (unpackR 24 t) = true ∧
    (unpackR 24 t != one ()) = true ∧
    (xFixCount certVecs (unpackR 24 t) == nfix) = true ∧
    (mul (unpackR 24 t) (unpackR 24 f₁) == mul (unpackR 24 f₁) (unpackR 24 t)) = true ∧
    (mul (unpackR 24 t) (unpackR 24 f₂) == mul (unpackR 24 f₂) (unpackR 24 t)) = true ∧
    (mul (unpackR 24 f₁) (unpackR 24 f₂) == mul (unpackR 24 f₂) (unpackR 24 f₁)) = true ∧
    (mul (unpackR 24 f₁) (unpackR 24 f₃) == mul (unpackR 24 f₃) (unpackR 24 f₁)) = true ∧
    (mul (unpackR 24 f₂) (unpackR 24 f₃) == mul (unpackR 24 f₃) (unpackR 24 f₂)) = true := by
  unfold sideK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨?_, validRows_unpackR _, ?_, ?_, comm_unpack h4, comm_unpack h5, comm_unpack h6,
    comm_unpack h7, comm_unpack h8⟩
  · rw [mul_unpackW', CFSG.KC.Co1B.one_eq, beq_unpack]
    exact h1
  · rw [CFSG.KC.Co1B.one_eq, bne, beq_unpack]
    exact not_of_notB h2
  · rw [CertificateChecks.KernelCo1B.xFix_eq rfl, beq_iff_eq]
    exact Nat.eq_of_beq_eq_true h3

theorem kFA' : gtPinK FAM 2 100 FAT.N FAT.P FAT.PAR FAT.LAB FAT.W FAT.S = true ∧ FAT.N = 25 := by
  have h := kFA
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact h

theorem kEA' : gtPinK EAM 3 400 EAT.N EAT.P EAT.PAR EAT.LAB EAT.W EAT.S = true ∧ EAT.N = 125 := by
  have h := kEA
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact h

theorem kFB' : gtPinK FBM 2 100 FBT.N FBT.P FBT.PAR FBT.LAB FBT.W FBT.S = true ∧ FBT.N = 25 := by
  have h := kFB
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact h

theorem kEB' : gtPinK EBM 3 400 EBT.N EBT.P EBT.PAR EBT.LAB EBT.W EBT.S = true ∧ EBT.N = 125 := by
  have h := kEB
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact h

theorem FAG_eq : [unpackR 24 KK, unpackR 24 DK].toArray = gensArr 2 FAM := by
  apply Array.ext (by simp [gensArr])
  intro i h1 h2
  have hi : i < 2 := by simpa using h1
  interval_cases i <;> simp [gensArr, FAM, getL_eq, unpackR_eq_unpack]

theorem EAG_eq : [unpackR 24 KK, unpackR 24 DK, unpackR 24 CK].toArray = gensArr 3 EAM := by
  apply Array.ext (by simp [gensArr])
  intro i h1 h2
  have hi : i < 3 := by simpa using h1
  interval_cases i <;> simp [gensArr, EAM, getL_eq, unpackR_eq_unpack]

theorem FBG_eq : [unpackR 24 KK, unpackR 24 CK].toArray = gensArr 2 FBM := by
  apply Array.ext (by simp [gensArr])
  intro i h1 h2
  have hi : i < 2 := by simpa using h1
  interval_cases i <;> simp [gensArr, FBM, getL_eq, unpackR_eq_unpack]

theorem EBG_eq : [unpackR 24 KK, unpackR 24 CK, unpackR 24 C2K].toArray = gensArr 3 EBM := by
  apply Array.ext (by simp [gensArr])
  intro i h1 h2
  have hi : i < 3 := by simpa using h1
  interval_cases i <;> simp [gensArr, EBM, getL_eq, unpackR_eq_unpack]

theorem kTA' : KF.TA.length = 25 ∧ ∀ i < 25, eqK (getL 0 KF.TA i) (trK 24 (betaK KK DK i)) = true := by
  have h := kTA
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1, allN_true' h.2⟩

theorem kTB' : KF.TB.length = 25 ∧ ∀ i < 25, eqK (getL 0 KF.TB i) (trK 24 (betaK KK CK i)) = true := by
  have h := kTB
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1, allN_true' h.2⟩

theorem cs_of {F₁ F₂ : Nat} {TL : List Nat} (hl : TL.length = 25)
    (hall : ∀ i < 25, eqK (getL 0 TL i) (trK 24 (betaK F₁ F₂ i)) = true) :
    colsOf (betas (unpackR 24 F₁) (unpackR 24 F₂)) = (TL.map (unpackR 24)).toArray := by
  rw [colsOf, betas, List.map_toArray, List.map_map]
  refine congrArg List.toArray ?_
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  have hi : i < 25 := by simpa using h1
  have e := beq_of_eqK (hall i hi)
  rw [CFSG.KC.Co1B.getL_eq, List.getElem?_eq_getElem (by rw [hl]; exact hi), Option.getD_some] at e
  rw [List.getElem_map, List.getElem_map, List.getElem_range, Function.comp_apply, pow_unpack',
    pow_unpack', mul_unpackW', CFSG.KC.F2W.transposeRows_unpackR, e]
  rfl

theorem kNFA {i : Nat} (hi : i < 3) : memK XB (baseA.getD i 0) = true ∧
    (KF.CNsA.getD i []).length = 9 ∧ (KF.CNsA.getD i []).sum ≤ cntsA.getD i 0 := by
  have h := kNsA
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  have h' := allN_true' h.2 i hi
  simp only [Bool.and_eq_true, Nat.beq_eq] at h'
  exact ⟨h'.1.1, h'.1.2, Nat.le_of_ble_eq_true h'.2⟩

theorem kNFB {i : Nat} (hi : i < 3) : memK XB (baseB.getD i 0) = true ∧
    (KF.CNsB.getD i []).length = 9 ∧ (KF.CNsB.getD i []).sum ≤ cntsB.getD i 0 := by
  have h := kNsB
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  have h' := allN_true' h.2 i hi
  simp only [Bool.and_eq_true, Nat.beq_eq] at h'
  exact ⟨h'.1.1, h'.1.2, Nat.le_of_ble_eq_true h'.2⟩

theorem chunksA : ∀ n < 27,
    lvlChunkP 25 XB KF.TA KF.CFsA KF.NPA CertificateChecks.KernelCo1B.CV.F KF.CNsA n = true := by
  intro n hn
  interval_cases n
  exacts [ch431007pA0, ch431007pA1, ch431007pA2, ch431007pA3, ch431007pA4, ch431007pA5,
    ch431007pA6, ch431007pA7, ch431007pA8, ch431007pA9, ch431007pA10, ch431007pA11,
    ch431007pA12, ch431007pA13, ch431007pA14, ch431007pA15, ch431007pA16, ch431007pA17,
    ch431007pA18, ch431007pA19, ch431007pA20, ch431007pA21, ch431007pA22, ch431007pA23,
    ch431007pA24, ch431007pA25, ch431007pA26]

theorem chunksB : ∀ n < 27,
    lvlChunkP 25 XB KF.TB KF.CFsB KF.NPB CertificateChecks.KernelCo1B.CV.F KF.CNsB n = true := by
  intro n hn
  interval_cases n
  exacts [ch431007pB0, ch431007pB1, ch431007pB2, ch431007pB3, ch431007pB4, ch431007pB5,
    ch431007pB6, ch431007pB7, ch431007pB8, ch431007pB9, ch431007pB10, ch431007pB11,
    ch431007pB12, ch431007pB13, ch431007pB14, ch431007pB15, ch431007pB16, ch431007pB17,
    ch431007pB18, ch431007pB19, ch431007pB20, ch431007pB21, ch431007pB22, ch431007pB23,
    ch431007pB24, ch431007pB25, ch431007pB26]

theorem sideA_ok : sideOK (nd (kDag ext5) 91) (nd (kDag ext5) 88) (nd (kDag ext5) 94)
    (nd (kDag ext5) 92) 2280 baseA condsA cntsA spanA combA = true := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := side_parts kSideA
  have gF := gtBFS_of_K kFA'.1
  have gE := gtBFS_of_K kEA'.1
  rw [t_eq, k_eq, d_eq, c_eq]
  unfold sideOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨s1, s2⟩, s3⟩, s4⟩, s5⟩, s6⟩, s7⟩, s8⟩, s9⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩,
    by decide⟩
  · rw [FAG_eq, gF.1]
    exact gF.2
  · rw [FAG_eq, gF.1]
    simp [bfsTree, kFA'.2]
  · rw [EAG_eq, gE.1]
    exact gE.2
  · rw [EAG_eq, gE.1]
    simp [bfsTree, kEA'.2]
  · rw [cs_of kTA'.1 kTA'.2]
    exact boundOK_of_sel (m := 3) kTA'.1 rfl rfl rfl (of_decide_eq_true kCFsA)
      (fun i hi => kNFA hi) chunksA kSpanA

theorem sideB_ok : sideOK (nd (kDag ext5) 95) (nd (kDag ext5) 88) (nd (kDag ext5) 92)
    (nd (kDag ext5) 93) 0 baseB condsB cntsB spanB combB = true := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := side_parts kSideB
  have gF := gtBFS_of_K kFB'.1
  have gE := gtBFS_of_K kEB'.1
  rw [x2_eq, k_eq, c_eq, c2_eq]
  unfold sideOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨s1, s2⟩, s3⟩, s4⟩, s5⟩, s6⟩, s7⟩, s8⟩, s9⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩,
    by decide⟩
  · rw [FBG_eq, gF.1]
    exact gF.2
  · rw [FBG_eq, gF.1]
    simp [bfsTree, kFB'.2]
  · rw [EBG_eq, gE.1]
    exact gE.2
  · rw [EBG_eq, gE.1]
    simp [bfsTree, kEB'.2]
  · rw [cs_of kTB'.1 kTB'.2]
    exact boundOK_of_sel (m := 3) kTB'.1 rfl rfl rfl (of_decide_eq_true kCFsB)
      (fun i hi => kNFB hi) chunksB kSpanB

open Certificates in
open CFSG.LocalAnalysis.GLTheoremA.H1017.Co1FiveNative in
theorem c431007 : co1FiveCheck () = true := by
  unfold co1FiveCheck
  simp only [hflag, sideA_ok, sideB_ok, Bool.and_self]

end CertificateChecks.KernelCo1B.Bound431007

end

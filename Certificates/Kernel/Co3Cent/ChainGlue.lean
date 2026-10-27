module

public import Certificates.Kernel.Co3Cent.Trees
public import CFSG.Certificates.Kernel.OrbRow.Tight
public import CFSG.Certificates.Kernel.OrbRow.ReachPerm
public import CFSG.Certificates.Kernel.OrbRow.LevelSound
public import CFSG.Certificates.Kernel.OrbRow.CentLGrp
public import CFSG.Certificates.Kernel.OrbRow.CentBSound
public import CFSG.Certificates.Kernel.OrbRow.PRepFacts
public import CFSG.Certificates.Kernel.Misc.PermWitSound
public import CFSG.Certificates.Kernel.BfsPinSetSound
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3Three
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Monster.AxisCount.HSIdentBaby
public import CFSG.Monster.AxisCount.HSIdentRec0
public import CFSG.Monster.AxisCount.HSIdentRec1
public import CFSG.Monster.AxisCount.HSIdentRec2
public import CFSG.Monster.AxisCount.HSIdentRec3
public import CFSG.Monster.AxisCount.HSIdentRec4
public import CFSG.Monster.AxisCount.HSIdentRec5
public import CFSG.Monster.AxisCount.HSIdentRec6
public import CFSG.Monster.AxisCount.HSIdentRec7
public import CFSG.Monster.AxisCount.HSIdentSmall
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.FischerOddCore.Basic
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.Schreier.RuLocal
public import CFSG.Sporadic.SchreierLemmas.FrattiniProfile
public import CFSG.Sporadic.SmallOddCore.CentSpec
public import CFSG.Sporadic.ThSchreier.ThSchreierCase
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate10027
public import Certificates.Certificate10107
public import Certificates.Certificate10108
public import Certificates.Certificate10110
public import Certificates.Certificate10111
public import Certificates.Certificate16018
public import Certificates.Certificate2323
public import Certificates.Certificate6006
public import Certificates.Certificate8026Base
public import Certificates.Certificate9124

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo3Cent

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KD.Co3Cent Subgroup
open CFSG.Monster.B.Co2 (permOfArr)
open CFSG.RankThree.Native (rep_of_validA)
open CFSG.KC.Misc.ArrEnum (permB)
open CFSG.KC.PermWit (siftR)
open CFSG.Sporadic.Schreier.Co3 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T

@[expose] noncomputable def pv (p : ℕ) : Equiv.Perm (Fin 276) := permOfArr 276 (unpack 276 9 p)

theorem prep_pv {p : ℕ} (h : permB 276 9 p = true) : PRep 276 9 p (pv p) :=
  prep_of_rep (rep_of_validA (CFSG.KC.BfsPin.validA_unpack h))

theorem pv_apply {p : ℕ} (h : permB 276 9 p = true) (y : ℕ) (hy : y < 276) :
    ((pv p) ⟨y, hy⟩ : ℕ) = pg 9 511 p y :=
  (prep_pv h ⟨y, hy⟩).symm

theorem inP3K_spec {S : List ℕ} {j : ℕ} (h : inP3K S j = true) :
    permB 276 9 (getS S j) = true ∧
      siftR 276 9 CertificateChecks.KernelSpor.Co3C.LR CertificateChecks.KernelSpor.Co3C.TRI
        CertificateChecks.KernelSpor.Co3C.BP 7 (getS S j) = true := by
  unfold inP3K at h
  rw [strictB_apply] at h
  exact (bAnd_iff _ _).1 h

theorem pv_mem {S : List ℕ} {j : ℕ}
    (h : inP3K S j = true) : pv (getS S j) ∈ co3P := by
  obtain ⟨hp, hs⟩ := inP3K_spec h
  exact mem_co3P_of_inP (rep_of_validA (CFSG.KC.BfsPin.validA_unpack hp))
    (CFSG.KC.PermWit.siftR_sound CertificateChecks.KernelSpor.Co3C.binds
      CertificateChecks.KernelSpor.Co3C.perm CertificateChecks.KernelSpor.Co3C.hl hs)

@[expose] noncomputable def sv (S : List ℕ) (j : ℕ) : Equiv.Perm (Fin 276) := pv (getS S j)

@[expose] noncomputable def bv (B : List ℕ) (hB : ∀ t, getS B t < 276) (t : ℕ) : Fin 276 :=
  ⟨getS B t, hB t⟩

@[expose] noncomputable def Gv (S M : List ℕ) (k i : ℕ) : Subgroup (Equiv.Perm (Fin 276)) :=
  closure (sv S '' {j | lvOk k (getS M i) j})

section Chain

variable {S B M : List ℕ} {k nl : ℕ} (hB : ∀ t, getS B t < 276)
  (hS : ∀ j < k, permB 276 9 (getS S j) = true)

include hS in
theorem sv_apply {i : ℕ} :∀ j, lvOk k (getS M i) j → ∀ y (hy : y < 276),
    ((sv S j) ⟨y, hy⟩ : ℕ) = pg 9 511 (getS S j) y :=
  fun j hj y hy => pv_apply (hS j (lvOk_iff.1 hj).1) y hy

theorem Gv_le
    (hP : ∀ j < k, inP3K S j = true) (i : ℕ) : Gv S M k i ≤ co3P := by
  rw [Gv, closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact pv_mem (hP j (lvOk_iff.1 hj).1)

theorem not_lvOk_zero (j : ℕ) : ¬ lvOk k 0 j := by
  rw [lvOk_iff, Nat.zero_testBit]
  simp

theorem Gv_zero {i : ℕ} (hM : getS M i = 0) : Gv S M k i = ⊥ := by
  rw [Gv, hM]
  have : sv S '' {j | lvOk k 0 j} = ∅ := by
    rw [Set.image_eq_empty]
    ext j
    exact ⟨fun h => not_lvOk_zero j h, fun h => h.elim⟩
  rw [this, Subgroup.closure_empty]

theorem closure_fixes {α : Type*} {X : Set (Equiv.Perm α)} {p : ℕ → α} {i : ℕ}
    (h : ∀ g ∈ X, ∀ t < i, g (p t) = p t) : ∀ g ∈ closure X, ∀ t < i, g (p t) = p t := by
  have hle : closure X ≤ stabB ⊤ p i := (closure_le _).2 fun g hg => ⟨mem_top g, h g hg⟩
  exact fun g hg => (hle hg).2

include hS in
theorem Gv_fix (hf : ∀ i < nl, fixLvK 9 511 S k (getS M i) B i = true) (hM : getS M nl = 0) :
    ∀ i ≤ nl, ∀ g ∈ Gv S M k i, ∀ t < i, g (bv B hB t) = bv B hB t := by
  intro i hi
  rcases Nat.lt_or_ge i nl with hi' | hi'
  · refine closure_fixes ?_
    rintro _ ⟨j, hj, rfl⟩ t ht
    exact fix_of_fixLvK (hf i hi') (sv S) (sv_apply hS) hj ht (hB t)
  · have : i = nl := by omega
    subst this
    rw [Gv_zero hM]
    intro g hg t _
    rw [(mem_bot).1 hg]
    rfl

theorem maskDec_sound {nl : ℕ} (h : maskDec3K M nl = true) {i : ℕ} (hi : i + 1 < nl)
    {j : ℕ} (hj : (getS M (i + 1)).testBit j = true) : (getS M i).testBit j = true := by
  have h1 := allN_spec h i (by change i < nl - 1; omega)
  change strictB (getS M (Nat.succ i)) (fun a => Nat.beq (Nat.land a (getS M i)) a) = true at h1
  rw [strictB_apply] at h1
  have h2 : getS M (i + 1) &&& getS M i = getS M (i + 1) := Nat.eq_of_beq_eq_true h1
  have h3 := congrArg (fun a => a.testBit j) h2
  simp only [Nat.testBit_land, hj, Bool.true_and] at h3
  exact h3

theorem Gv_dec (hd : maskDec3K M nl = true) (hM : getS M nl = 0) :
    ∀ i < nl, Gv S M k (i + 1) ≤ Gv S M k i := by
  intro i hi
  rcases Nat.lt_or_ge (i + 1) nl with hi' | hi'
  · refine closure_mono (Set.image_mono fun j hj => ?_)
    obtain ⟨hj1, hj2⟩ := lvOk_iff.1 hj
    exact lvOk_iff.2 ⟨hj1, maskDec_sound hd hi' hj2⟩
  · have : i + 1 = nl := by omega
    rw [this, Gv_zero hM]
    exact bot_le

@[expose] noncomputable def ptsD (D : ℕ) : Finset (Fin 276) :=
  Finset.univ.filter fun x => inD D x = true

include hS in
theorem orbD {K D : List ℕ} {R : List (List ℕ)}
    (ht : allN nl (levelK 276 9 511 S k B K M D R) = true) :
    ∀ i < nl, (ptsD (getS D i)).card = getS K i ∧
      ∀ x ∈ ptsD (getS D i), ∃ g ∈ Gv S M k i, g (bv B hB i) = x := by
  intro i hi
  have h : levelK 276 9 511 S k B K M D R i = true := allN_spec ht i hi
  rw [levelK_eq] at h
  obtain ⟨hc, hr⟩ := rowsK_dep h
  refine ⟨?_, fun x hx => ?_⟩
  · rw [← hc]
    refine Finset.card_bij (fun x _ => x.val) (fun x hx => ?_) (fun x _ y _ he => Fin.ext he)
      (fun y hy => ?_)
    · simp only [ptsD, Finset.mem_filter, Finset.mem_univ, true_and, inD_iff] at hx
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 x.2, hx⟩
    · obtain ⟨hy1, hy2⟩ := Finset.mem_filter.1 hy
      refine ⟨⟨y, Finset.mem_range.1 hy1⟩, ?_, rfl⟩
      simp only [ptsD, Finset.mem_filter, Finset.mem_univ, true_and, inD_iff]
      exact hy2
  · simp only [ptsD, Finset.mem_filter, Finset.mem_univ, true_and, inD_iff] at hx
    obtain ⟨_, g, hg, hgx⟩ := reach_perm (sv S) (sv_apply hS) (hB i) (hr x x.2 hx)
    exact ⟨g, hg, hgx.trans rfl⟩

include hS in
theorem orbS {K D : List ℕ} {R : List (List ℕ)}
    (ht : allN nl (levelK 276 9 511 S k B K M D R) = true) :
    ∀ i < nl, ∃ s : Finset (Fin 276), s.card = getS K i ∧
      ∀ x ∈ s, ∃ g ∈ Gv S M k i, g (bv B hB i) = x :=
  fun i hi => ⟨_, (orbD hB hS ht i hi).1, (orbD hB hS ht i hi).2⟩

end Chain

theorem allLt_of {L : List ℕ} {c : ℕ} (h : ∀ t < L.length, getS L t < c) (hc : 0 < c) :
    ∀ t, getS L t < c := by
  intro t
  rcases Nat.lt_or_ge t L.length with ht | ht
  · exact h t ht
  · rw [getS_eq, List.getD_eq_default _ _ ht]
    exact hc

theorem hBA : ∀ t, getS BA t < 276 := allLt_of (by decide +kernel) (by norm_num)

theorem hBB : ∀ t, getS BB t < 276 := allLt_of (by decide +kernel) (by norm_num)

theorem permS {S : List ℕ} {k : ℕ} (h : allN k (inP3K S) = true) :
    ∀ j < k, permB 276 9 (getS S j) = true := fun j hj => (inP3K_spec (allN_spec h j hj)).1

theorem sFacts : allN 17 (inP3K SA) = true ∧ allN 14 (inP3K SB) = true ∧
    allN 17 (inP3K SHA) = true ∧ allN 12 (inP3K SHB) = true := by
  have h := ch17370_s
  simp only [bAnd_iff] at h
  exact h

theorem fFacts : allN 11 (fun i => fixLvK 9 511 SA 17 (getS MA i) BA i) = true ∧
    allN 17 (fun i => fixLvK 9 511 SB 14 (getS MB i) BB i) = true ∧
    allN 11 (fun i => fixLvK 9 511 SHA 17 (getS MHA i) BHA i) = true ∧
    allN 17 (fun i => fixLvK 9 511 SHB 12 (getS MHB i) BHB i) = true ∧
    maskDec3K MA 11 = true ∧ maskDec3K MB 17 = true ∧ maskDec3K MHA 11 = true ∧
    maskDec3K MHB 17 = true := by
  have h := ch17370_f
  simp only [bAnd_iff] at h
  exact h

theorem kFacts : BHA = BA ∧ BHB = BB := by
  have h := ch17370_k
  simp only [bAnd_iff] at h
  exact ⟨eq_of_beq h.2.2.2.2.2.2.2.2.2.1, eq_of_beq h.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem MA11 : getS MA 11 = 0 := by decide +kernel
theorem MB17 : getS MB 17 = 0 := by decide +kernel
theorem MHA11 : getS MHA 11 = 0 := by decide +kernel
theorem MHB17 : getS MHB 17 = 0 := by decide +kernel

theorem prodKA : ∏ t ∈ Finset.range 11, getS KA t = 495766656000 := by decide +kernel
theorem prodKB : ∏ t ∈ Finset.range 17, getS KB t = 495766656000 := by decide +kernel
theorem prodKHA : ∏ t ∈ Finset.Ico 0 11, getS KHA t = 349920 := by decide +kernel
theorem prodKHB : ∏ t ∈ Finset.Ico 0 17, getS KHB t = 29160 := by decide +kernel

@[expose] noncomputable def bA (t : ℕ) : Fin 276 := bv BA hBA t

@[expose] noncomputable def bB (t : ℕ) : Fin 276 := bv BB hBB t

theorem chainA :
    ∀ i ≤ 11, Gv SA MA 17 i = stabB co3P bA i ∧
      Nat.card (Gv SA MA 17 i) = ∏ t ∈ Finset.Ico i 11, getS KA t :=
  tight_chain co3P bA 11 (Gv SA MA 17) (getS KA) (fun i _ => Gv_le (allN_spec sFacts.1) i)
    (Gv_fix hBA (permS sFacts.1) (allN_spec fFacts.1) MA11) (Gv_dec fFacts.2.2.2.2.1 MA11)
    (orbS hBA (permS sFacts.1) ch17370_tA) (by rw [card_co3P, prodKA])

theorem chainB :
    ∀ i ≤ 17, Gv SB MB 14 i = stabB co3P bB i ∧
      Nat.card (Gv SB MB 14 i) = ∏ t ∈ Finset.Ico i 17, getS KB t :=
  tight_chain co3P bB 17 (Gv SB MB 14) (getS KB) (fun i _ => Gv_le (allN_spec sFacts.2.1) i)
    (Gv_fix hBB (permS sFacts.2.1) (allN_spec fFacts.2.1) MB17) (Gv_dec fFacts.2.2.2.2.2.1 MB17)
    (orbS hBB (permS sFacts.2.1) ch17370_tB) (by rw [card_co3P, prodKB])

theorem hBHA : ∀ t, getS BHA t < 276 := by rw [kFacts.1]; exact hBA

theorem hBHB : ∀ t, getS BHB t < 276 := by rw [kFacts.2]; exact hBB

theorem card_HA : 349920 ≤ Nat.card (Gv SHA MHA 17 0) := by
  have h := CFSG.KC.OrbRow.CentLGrp.prod_le_card_chain (bv BHA hBHA) 11 (Gv SHA MHA 17)
    (getS KHA) (Gv_fix hBHA (permS sFacts.2.2.1) (allN_spec fFacts.2.2.1) MHA11)
    (Gv_dec fFacts.2.2.2.2.2.2.1 MHA11) (orbS hBHA (permS sFacts.2.2.1) ch17370_tHA) 0 (by norm_num)
  rwa [prodKHA] at h

theorem card_HB : 29160 ≤ Nat.card (Gv SHB MHB 12 0) := by
  have h := CFSG.KC.OrbRow.CentLGrp.prod_le_card_chain (bv BHB hBHB) 17 (Gv SHB MHB 12)
    (getS KHB) (Gv_fix hBHB (permS sFacts.2.2.2) (allN_spec fFacts.2.2.2.1) MHB17)
    (Gv_dec fFacts.2.2.2.2.2.2.2 MHB17) (orbS hBHB (permS sFacts.2.2.2) ch17370_tHB) 0 (by norm_num)
  rwa [prodKHB] at h

end CertificateChecks.KernelCo3Cent

end

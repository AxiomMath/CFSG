module

public import Certificates.Kernel.D4Q2K.Points
public import Certificates.Kernel.D4Q2K.Frames
public import Certificates.Kernel.D4Q2K.Masks
public import Certificates.Kernel.D4Q2K.Rows
public import Certificates.Kernel.D4Q2K.Clique
public import Certificates.Kernel.D4Q2K.Sols
public import Certificates.Kernel.D4Q2K.Tri
public import Certificates.Kernel.D4Q2K.TriC
public import Certificates.Kernel.D4Q2K.Apart
public import Certificates.Kernel.D4Q2K.Elim
public import CFSG.Certificates.Kernel.D4Q2K.PtSound
public import CFSG.Certificates.Kernel.D4Q2K.ElimSound
public import CFSG.ClassicalInvolution.Phan.PhanDn.D4Q2.Solids
import CFSG.Certificates.Kernel.Common.ForallFrom
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalInvolution.Phan.Defs
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwoCompressed
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

set_option maxRecDepth 400000
set_option exponentiation.threshold 5000

namespace CertificateChecks.KernelD4Q2K

open CFSG.KC.D4Q2K CFSG.KC.Enum CFSG.ClassicalInvolution.PhanDn.D4Q2

#kc_forall_from allMk (fun c => masksK D.pts D.frames.toList D.MF (280 * c) 280 = true) 16
  CertificateChecks.KernelD4Q2K.ch709441mk 0
#kc_forall_from allRw (fun c => rowsK D.pts D.RF (280 * c) 280 = true) 8
  CertificateChecks.KernelD4Q2K.ch709441rw 0
#kc_forall_from allCq (fun s => cqSl s = true) 112 CertificateChecks.KernelD4Q2K.cqSl 0
#kc_forall_from allSA (fun s => solASl s = true) 16 CertificateChecks.KernelD4Q2K.solASl 0
#kc_forall_from allSB (fun s => solBSl s = true) 8 CertificateChecks.KernelD4Q2K.solBSl 0
#kc_forall_from allTS (fun s => triSSl s = true) 16 CertificateChecks.KernelD4Q2K.triSSl 0
#kc_forall_from allTF (fun s => tfSl s = true) 16 CertificateChecks.KernelD4Q2K.tfSl 0
#kc_forall_from allTC (fun s => triCSl s = true) 112 CertificateChecks.KernelD4Q2K.triCSl 0
#kc_forall_from allCX (fun s => cxSl s = true) 16 CertificateChecks.KernelD4Q2K.cxSl 0
#kc_forall_from allAP (fun s => apSl s = true) 16 CertificateChecks.KernelD4Q2K.apSl 0
#kc_forall_from allRV (fun s => rowVSl s = true) 105 CertificateChecks.KernelD4Q2K.rowVSl 0
#kc_forall_from allEV (fun s => elimVSl s = true) 105 CertificateChecks.KernelD4Q2K.elimVSl 0

theorem bAnd_true {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem len_both : Nat.beq (lenL D.pts) 2240 = true ∧
    Nat.beq D.frames.toList.length 4480 = true :=
  bAnd_true (a := Nat.beq (lenL D.pts) 2240) (b := Nat.beq D.frames.toList.length 4480)
    ch709441len

theorem pts_len : D.pts.length = 2240 := by
  have h := len_both.1
  rw [lenL_eq] at h
  exact Nat.eq_of_beq_eq_true h

theorem frames_size : D.frames.size = 4480 := by
  have h := Nat.eq_of_beq_eq_true len_both.2
  rw [Array.length_toList] at h
  exact h

theorem hSA : ∀ c < 16, solAK D.MF DS.SF DS.sp (280 * c) 280 = true := allSA
theorem hSB : ∀ c < 8, solBK D.MF DS.SF DS.si (280 * c) 280 = true := allSB
theorem hCq : ∀ s < 112, cliqueK D.RF D.MF DC.cl (20 * s) 20 = true := allCq
theorem hTS : ∀ c < 16, triSK D.RF D.MF DT.TW (280 * c) 280 = true := allTS
theorem hTF : ∀ c < 16, tfK DT.TW DT.TF (280 * c) 280 = true := allTF
theorem hTC : ∀ s < 112, triCK DS.SF DT.TF DC.cl (20 * s) 20 = true := allTC
theorem hAP : ∀ c < 16,
    apK D.pts D.MF DS.SF DT.TF DA.XC DA.CX DA.AP 4989 (280 * c) 280 = true := allAP

theorem all_of_slices {f : Nat → Bool} {w n N : Nat} (hN : N ≤ w * n)
    (h : ∀ s < n, allBlk (Nat.mul w s) (fun x => bIf(Nat.blt x N, f x, true)) w = true) :
    ∀ x < N, f x = true := by
  intro x hx
  have hw : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h0 | h0
    · rw [h0, Nat.zero_mul] at hN
      omega
    · exact h0
  have hs : x / w < n := by
    rw [Nat.div_lt_iff_lt_mul hw, Nat.mul_comm]
    omega
  have e : Nat.mul w (x / w) + x % w = x := Nat.div_add_mod x w
  have h1 := allBlk_get (h (x / w) hs) (x % w) (Nat.mod_lt x hw)
  rw [e] at h1
  have hb : Nat.blt x N = true := by
    rw [Nat.blt_eq]
    exact hx
  rw [hb] at h1
  exact h1

theorem hCX : ∀ t < 4989, cxK DA.FP DA.XC DA.CX t 1 = true :=
  all_of_slices (w := 312) (n := 16) (by norm_num) allCX

theorem hRV : ∀ x < 6720, rowV D.RF DS.SF D.MF DT.TF DE.NL x = true :=
  all_of_slices (w := 64) (n := 105) (by norm_num) allRV

theorem hEV : ∀ x < 6720, elimV DE.NL DE.RC DE.tr x = true :=
  all_of_slices (w := 64) (n := 105) (by norm_num) allEV

theorem hA : ∀ i < 2240, D.RF i < 2 ^ 2240 ∧
    ∀ i' < 2240, Nat.testBit (D.RF i) i' = ptAdjC (ptCodes ())[i]! (ptCodes ())[i']! :=
  fun _ hi => rowsK_sound ch709441pt pts_len allRw hi

theorem hM : ∀ j < 4480, D.MF j < 2 ^ 2240 ∧
    ∀ i < 2240, Nat.testBit (D.MF j) i = ((mkTabs (ptCodes ()) D.frames).inc[j]!)[i]! :=
  fun _ hj => masksK_sound ch709441pt pts_len allMk hj

theorem hS : ∀ i < 2240, DS.SF i < 2 ^ 4480 ∧
    ∀ j < 4480, Nat.testBit (DS.SF i) j = ((mkTabs (ptCodes ()) D.frames).inc[j]!)[i]! :=
  fun _ hi => solK_sound ch709441pt pts_len allMk hSA hSB hi

theorem hT : ∀ j < 4480, DT.TF j < 2 ^ 4480 ∧ ∀ j' < 4480, Nat.testBit (DT.TF j) j' =
    (j != j' && triTest (mkTabs (ptCodes ()) D.frames) j j') :=
  fun _ hj => triK_sound ch709441pt pts_len frames_size allMk allRw hSA hSB hCq hTS hTF hTC hj

theorem checks : Checks D.frames :=
  ⟨sizeCheck_of ch709441pt pts_len frames_size, frameK_sound ch709441pt ch709441fr,
    distinctK_sound ch709441pt pts_len frames_size allMk ch709441inc,
    cliqueK_sound ch709441pt pts_len frames_size allMk allRw hCq,
    apartK_sound ch709441pt pts_len frames_size allMk hS hT ch709441fp hCX hAP⟩

theorem elim : CFSG.KC.RankElim.ok 6720 (nbOf (mkTabs (ptCodes ()) D.frames))
    (fun x => parOf (trAt DE.tr x)) (fun x => depOf (trAt DE.tr x))
    (fun x k => rkOf (rcAt (DE.RC x) k)) (fun x k => apOf (rcAt (DE.RC x) k))
    (fun x k => bpOf (rcAt (DE.RC x) k)) (fun _ _ _ => true) = true :=
  elimK_sound hA hS hM hT hRV hEV

end CertificateChecks.KernelD4Q2K

end

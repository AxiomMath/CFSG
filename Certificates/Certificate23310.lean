module

public import Certificates.Data.Sol76PclsSuzE8
import Certificates.Kernel.Sporadic.Suz.E8K23310
import Certificates.Kernel.Sporadic.OddCore.Suz2302
import Certificates.Kernel.Sporadic.OddCore.CentGlue
import CFSG.Certificates.Kernel.BfsPinAlg

namespace CertificateChecks.Batch23310

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.PkPow CFSG.KC.BfsPin CFSG.KS.MulH
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier.Native CFSG.EvenSporadicStandard.HypOne CFSG.EvenSporadicStandard.HypOne.Suz
open CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.Sol76T13.R12.Pcls.SuzE8
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Suz23310

abbrev Cn (p : Nat) : Prop := canonK 1782 11 (mask 11) (1782 * 11) p = true

theorem base : szOK 1782 11 = true ∧ cn (pidn 1782 11) = true ∧ cn (SuzHypT.F 6) = true ∧
    cn (SuzHypT.F 7) = true ∧ cn (SuzHypT.F 8) = true ∧ cn (SuzHypT.F 9) = true := by
  simpa only [bAnd_iff] using base23310

theorem hyp_eq {k : Nat} (hk : k < 10) : hypTbl k = tabT (unpack 1782 11 (SuzHypT.F k)) := by
  have h : natArr (hypTbl k) = unpack 1782 11 (SuzHypT.F k) := by
    have h := CFSG.KC.Misc.HexFlat.hexT_sound SuzHypT.all (by norm_num) k hk
    rw [← SuzHypT.eq] at h
    exact h
  rw [← tabT_natArr (hypTbl k), h]

theorem idA_eq' : idA 1782 = unpack 1782 11 (pidn 1782 11) := idA_eq base.1

theorem idT_eq : idT 1782 = tabT (unpack 1782 11 (pidn 1782 11)) := by
  rw [idT_tabT, idA_eq']

theorem strictN_id (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem pows (P : Nat) : Pows 1782 11 P (ppw 1782 11 P) :=
  ⟨rfl, fun e => strictN_id (ppw 1782 11 P e) (fun q => pcomp 1782 11 (mask 11) P q)⟩

theorem not_of_bIf {b : Bool} (h : bIf(b, false, true) = true) : b = false := by
  cases b
  · rfl
  · exact absurd h Bool.false_ne_true

theorem divParts_two : divParts 2 = [1] := by decide

theorem elt_ok {P : Nat} (h : invK P = true) : Cn P ∧
    CFSG.Sporadic.SmallOddCore.permOK 1782 (tabT (unpack 1782 11 P)) = true ∧
    ordTest 1782 2 (tabT (unpack 1782 11 P)) = true ∧
    (CFSG.Sporadic.SuzOddCore.fixedCount (natArr (tabT (unpack 1782 11 P))) == 54) = true := by
  obtain ⟨hc, hi, h2, h1, hf⟩ := (by simpa only [invK, bAnd_iff] using h :
    cn P = true ∧ invEqK 1782 11 (mask 11) (1782 * 11) P P = true ∧
    Nat.beq (ppw 1782 11 P 2) (pidn 1782 11) = true ∧
    bIf(Nat.beq (ppw 1782 11 P 1) (pidn 1782 11), false, true) = true ∧ Nat.beq (fixK P) 54 = true)
  refine ⟨hc, permOK_unpack hc hi, ?_, ?_⟩
  · simp only [ordTest_unpack (pows P) idA_eq' base.2.1 hc, divParts_two, h2, not_of_bIf h1,
      List.all_cons, List.all_nil, Bool.not_false, Bool.and_true]
  · have e : CertificateChecks.KernelSpor.OddCore.fixCntK 1782 11 (mask 11) P = 54 :=
      Nat.eq_of_beq_eq_true hf
    simp only [natArr_tabT hc, CertificateChecks.KernelSpor.OddCore.fixedCount_unpack, e,
      beq_self_eq_true]

theorem sift_ok {P : Nat} (hc : Cn P) (h : Suz2306.sift P = true) :
    siftM (tabT (unpack 1782 11 P)) = true := by
  unfold siftM
  rw [natArr_tabT hc, CertificateChecks.KernelSpor.OddCore.inM_eq rfl hc]
  exact h

theorem comm_ok {P Q : Nat} (hp : Cn P) (hq : Cn Q)
    (h : Nat.beq (pcomp 1782 11 (mask 11) P Q) (pcomp 1782 11 (mask 11) Q P) = true) :
    commT 1782 (tabT (unpack 1782 11 P)) (tabT (unpack 1782 11 Q)) = true := by
  unfold commT
  rw [compT_unpack hp hq, compT_unpack hq hp, tblEq_unpack (canonK_pcomp hp hq) (canonK_pcomp hq hp)]
  exact h

theorem holds : suzE8Check = true := by
  obtain ⟨sx, sy, sz, cxy, cxz, cyz, ix, iy, iz, ixy, ixz, iyz, ixyz⟩ :=
    (by simpa only [e8K, bAnd_iff] using k23310 :
      Suz2306.sift X = true ∧ Suz2306.sift Y = true ∧ Suz2306.sift Z = true ∧
      Nat.beq (c X Y) (c Y X) = true ∧ Nat.beq (c X Z) (c Z X) = true ∧
      Nat.beq (c Y Z) (c Z Y) = true ∧ invK X = true ∧ invK Y = true ∧ invK Z = true ∧
      invK (c X Y) = true ∧ invK (c X Z) = true ∧ invK (c Y Z) = true ∧
      invK (c (c X Y) Z) = true)
  obtain ⟨-, -, b6, b7, b8, b9⟩ := base
  have cX := (elt_ok ix).1
  have cY := (elt_ok iy).1
  have cZ := (elt_ok iz).1
  have cXY : Cn (pcomp 1782 11 (mask 11) X Y) := canonK_pcomp cX cY
  have x_eq : xTab = tabT (unpack 1782 11 X) := by
    unfold xTab
    rw [hyp_eq (by norm_num), powT_unpack (pows _) idT_eq base.2.1 b7 4]
    rfl
  have w_eq : wTab = tabT (unpack 1782 11 W) := by
    unfold wTab
    rw [hyp_eq (k := 7) (by norm_num), hyp_eq (k := 9) (by norm_num), hyp_eq (k := 6) (by norm_num),
      compT_unpack b9 b6, compT_unpack b7 (canonK_pcomp b9 b6)]
    rfl
  have cW : Cn W := canonK_pcomp b7 (canonK_pcomp b9 b6)
  have y_eq : yTab = tabT (unpack 1782 11 Y) := by
    unfold yTab
    rw [w_eq, compT_unpack cW cW]
    rfl
  have z_eq : zTab = tabT (unpack 1782 11 Z) := by
    unfold zTab
    rw [x_eq, hyp_eq (k := 8) (by norm_num), compT_unpack cX b8, compT_unpack b8 (canonK_pcomp cX b8)]
    rfl
  unfold suzE8Check e8Check e8Prods
  rw [x_eq, y_eq, z_eq, compT_unpack cX cY, compT_unpack cX cZ, compT_unpack cY cZ,
    compT_unpack cXY cZ]
  have ex := elt_ok ix
  have ey := elt_ok iy
  have ez := elt_ok iz
  have exy := elt_ok (P := pcomp 1782 11 (mask 11) X Y) ixy
  have exz := elt_ok (P := pcomp 1782 11 (mask 11) X Z) ixz
  have eyz := elt_ok (P := pcomp 1782 11 (mask 11) Y Z) iyz
  have exyz := elt_ok (P := pcomp 1782 11 (mask 11) (pcomp 1782 11 (mask 11) X Y) Z) ixyz
  simp only [ex.2.1, ey.2.1, ez.2.1, sift_ok cX sx, sift_ok cY sy, sift_ok cZ sz,
    comm_ok cX cY cxy, comm_ok cX cZ cxz, comm_ok cY cZ cyz, ex.2.2.1, ey.2.2.1, ez.2.2.1,
    exy.2.2.1, exz.2.2.1, eyz.2.2.1, exyz.2.2.1, List.all_cons, List.all_nil, ex.2.2.2, ey.2.2.2,
    ez.2.2.2, exy.2.2.2, exz.2.2.2, eyz.2.2.2, exyz.2.2.2, Bool.and_self]

end CertificateChecks.Batch23310

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.Sol76T13.R12.Pcls.SuzE8 in
theorem certificate23310 : suzE8Check = true :=
  CertificateChecks.Batch23310.holds

end Certificates

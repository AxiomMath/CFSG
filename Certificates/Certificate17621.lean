module

public import Certificates.Data.TabCo1ThreeASuzInv
public meta import Certificates.Data.TabCo1ThreeASuzInv
public import Certificates.Data.Kernel.SuzInvK
import Certificates.Kernel.SuzPump.PairFacts
import CFSG.Certificates.Kernel.Misc.ArrEnumSound
import CFSG.Certificates.Kernel.Misc.ArrEnumOps
import CFSG.Certificates.Kernel.B3S3KSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Misc.ArrBind

set_option maxRecDepth 400000

open CFSG.KS hiding levels
open CFSG.KC.Enum CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CFSG.KC.BfsPin
open CertificateChecks.KernelSpor CertificateChecks.KernelSuzPump CFSG.KC.SuzInvK
open CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeASuzInv CFSG.HardMathSupport.Dickson.I271.TabSuzFuse
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu

namespace CertificateChecks.Batch17621

open CFSG.KS hiding levels
open CFSG.KC.Enum CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CFSG.KC.BfsPin
open CertificateChecks.KernelSpor CertificateChecks.KernelSuzPump CFSG.KC.SuzInvK
open CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeASuzInv CFSG.HardMathSupport.Dickson.I271.TabSuzFuse
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu

theorem inP_of {G : Nat} (h : Nat.beq (Nat.shiftRight G (1782 * 11)) 0 = true ∧
    allN 1782 (fun t => Nat.blt (pg 11 (mask 11) G t) 1782) = true ∧
    siftK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) SuzC.LR SuzC.TRI SuzC.BP 6 0 G = true) :
    inP (levels ()) (unpack 1782 11 G) = true := by
  unfold inP CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.levels
  exact siftA_of Suz2306.binds Suz2306.perm SuzC.hl h

theorem invAt_of {C S T U : Nat} {tp : Array (Array Nat)}
    (eS : rebuild (levels ()) tp[0]! = unpack 1782 11 S)
    (eT : rebuild (levels ()) tp[1]! = unpack 1782 11 T)
    (eU : rebuild (levels ()) tp[2]! = unpack 1782 11 U)
    (pC : permB 1782 11 C = true) (pS : permB 1782 11 S = true) (pT : permB 1782 11 T = true)
    (pU : permB 1782 11 U = true) (iS : inP (levels ()) (unpack 1782 11 S) = true)
    (iT : inP (levels ()) (unpack 1782 11 T) = true)
    (iU : inP (levels ()) (unpack 1782 11 U) = true) (h : invK C S T U = true) :
    invAtOK (levels ()) (unpack 1782 11 C) tp = true := by
  have pSC := permB_pcomp hw pS pC
  have pTU := permB_pcomp hw pT pU
  unfold invAtOK
  dsimp only
  rw [eS, eT, eU, validA_of pS, validA_of pT, validA_of pU, iS, iT, iU, idA_eq hw,
    comp_unpack hw pS pS, comp_unpack hw pS pC, comp_unpack hw pSC pSC, comp_unpack hw pT pT,
    comp_unpack hw pU pU, comp_unpack hw pT pC, comp_unpack hw pC pT, comp_unpack hw pU pC,
    comp_unpack hw pC pU, comp_unpack hw pT pU, pow_unpack hw pTU 3,
    eqA_unpack hw (permB_pcomp hw pS pS) (permB_id hw),
    eqA_unpack hw (permB_pcomp hw pSC pSC) (permB_id hw),
    eqA_unpack hw (permB_pcomp hw pT pT) (permB_id hw),
    eqA_unpack hw (permB_pcomp hw pU pU) (permB_id hw),
    eqA_unpack hw (permB_pcomp hw pT pC) (permB_pcomp hw pC pT),
    eqA_unpack hw (permB_pcomp hw pU pC) (permB_pcomp hw pC pU),
    eqA_unpack hw (permB_ppow hw pTU 3) (permB_id hw), eqA_unpack hw pTU (permB_id hw)]
  unfold invK at h
  simpa using h

theorem invAt_reb {c : Array Nat} {tp : Array (Array Nat)} (hc : (reb c).2.2 = true)
    (h0 : (reb tp[0]!).2.2 = true) (h1 : (reb tp[1]!).2.2 = true) (h2 : (reb tp[2]!).2.2 = true)
    (pC : permB 1782 11 (reb c).1 = true) (p0 : permB 1782 11 (reb tp[0]!).1 = true)
    (p1 : permB 1782 11 (reb tp[1]!).1 = true) (p2 : permB 1782 11 (reb tp[2]!).1 = true)
    (s0 : Nat.beq (Nat.shiftRight (reb tp[0]!).1 (1782 * 11)) 0 = true ∧
      allN 1782 (fun t => Nat.blt (pg 11 (mask 11) (reb tp[0]!).1 t) 1782) = true ∧
      siftK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) SuzC.LR SuzC.TRI SuzC.BP 6 0
        (reb tp[0]!).1 = true)
    (s1 : Nat.beq (Nat.shiftRight (reb tp[1]!).1 (1782 * 11)) 0 = true ∧
      allN 1782 (fun t => Nat.blt (pg 11 (mask 11) (reb tp[1]!).1 t) 1782) = true ∧
      siftK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) SuzC.LR SuzC.TRI SuzC.BP 6 0
        (reb tp[1]!).1 = true)
    (s2 : Nat.beq (Nat.shiftRight (reb tp[2]!).1 (1782 * 11)) 0 = true ∧
      allN 1782 (fun t => Nat.blt (pg 11 (mask 11) (reb tp[2]!).1 t) 1782) = true ∧
      siftK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) SuzC.LR SuzC.TRI SuzC.BP 6 0
        (reb tp[2]!).1 = true)
    (h : invK (reb c).1 (reb tp[0]!).1 (reb tp[1]!).1 (reb tp[2]!).1 = true) :
    invAtOK (levels ()) (rebuild (levels ()) c) tp = true := by
  rw [rebuild_eq hc]
  exact invAt_of (rebuild_eq h0) (rebuild_eq h1) (rebuild_eq h2) pC p0 p1 p2 (inP_of s0)
    (inP_of s1) (inP_of s2) h

theorem atA : invAtOK (levels ()) (xAArr (levels ())) tupA = true :=
  invAt_reb (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    (by quickRfl) (by quickRfl) ⟨by quickRfl, by quickRfl, by quickRfl⟩
    ⟨by quickRfl, by quickRfl, by quickRfl⟩ ⟨by quickRfl, by quickRfl, by quickRfl⟩ (by quickRfl)

theorem atB : invAtOK (levels ()) (xBArr (levels ())) tupB = true :=
  invAt_reb (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    (by quickRfl) (by quickRfl) ⟨by quickRfl, by quickRfl, by quickRfl⟩
    ⟨by quickRfl, by quickRfl, by quickRfl⟩ ⟨by quickRfl, by quickRfl, by quickRfl⟩ (by quickRfl)

theorem atY : invAtOK (levels ()) (yArr (levels ())) tupY = true :=
  invAt_reb (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    (by quickRfl) (by quickRfl) ⟨by quickRfl, by quickRfl, by quickRfl⟩
    ⟨by quickRfl, by quickRfl, by quickRfl⟩ ⟨by quickRfl, by quickRfl, by quickRfl⟩ (by quickRfl)

end CertificateChecks.Batch17621

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeASuzInv in
theorem certificate17621 : suzInvCheck () = true := by
  unfold suzInvCheck
  dsimp only
  rw [CertificateChecks.Batch17621.atA, CertificateChecks.Batch17621.atB, CertificateChecks.Batch17621.atY]
  rfl

end Certificates

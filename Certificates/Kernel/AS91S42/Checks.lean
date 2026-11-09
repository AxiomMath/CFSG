module

public import Certificates.Data.Kernel.AS91S42
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.RangeSplit

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelAS91S42

open Certificates.Kernel.AS91S42 CFSG.KC.RangeSplit CFSG.KC.Mat12P CFSG.KC.Mat8P Certificates.Kernel.HJ12K

theorem s1A : (pairsOK g1Q && pairsOK p1Q && pairsOK w1Q &&
    g1Q.all (fun p => Nat.beq (mvNR (unpackQ p.1) 3) 3) &&
    memP (ofListP (enumQ (g1Q.map Prod.fst))) oneQ && closedS (g1Q.map Prod.fst) (enumQ (g1Q.map Prod.fst)) (ofListP (enumQ (g1Q.map Prod.fst))) && nodupP (enumQ (g1Q.map Prod.fst)) &&
    Nat.beq (enumQ (g1Q.map Prod.fst)).length 3840 &&
    memP (ofListP (enumQ (p1Q.map Prod.fst))) oneQ && closedS (p1Q.map Prod.fst) (enumQ (p1Q.map Prod.fst)) (ofListP (enumQ (p1Q.map Prod.fst))) && nodupP (enumQ (p1Q.map Prod.fst)) &&
    Nat.beq (enumQ (p1Q.map Prod.fst)).length 32 &&
    p1Q.all (fun p => memP (ofListP (enumQ (g1Q.map Prod.fst))) p.1) &&
    g1Q.all (fun t => p1Q.all fun p => memP (ofListP (enumQ (p1Q.map Prod.fst))) (mulQ t.1 (mulQ p.1 t.2))) &&
    w1Q.all (fun w => memP (ofListP (enumQ (g1Q.map Prod.fst))) w.1)) = true := by
  quickRfl

theorem s1T0 : ((enumQ (g1Q.map Prod.fst)).take 960).all (twoTest w1Q (ofListP (enumQ (p1Q.map Prod.fst)))) = true := by quickRfl

theorem s1T1 : (((enumQ (g1Q.map Prod.fst)).drop 960).take 960).all (twoTest w1Q (ofListP (enumQ (p1Q.map Prod.fst)))) = true := by quickRfl

theorem s1T2 : ((((enumQ (g1Q.map Prod.fst)).drop 960).drop 960).take 960).all (twoTest w1Q (ofListP (enumQ (p1Q.map Prod.fst)))) = true := by quickRfl

theorem s1T3 : ((((enumQ (g1Q.map Prod.fst)).drop 960).drop 960).drop 960).all (twoTest w1Q (ofListP (enumQ (p1Q.map Prod.fst)))) = true := by quickRfl

theorem ch89402_s1 : stabQ 3 g1Q p1Q w1Q 3840 32 = true := by
  unfold stabQ stabAt stabCore
  exact andT s1A (all_cut (enumQ (g1Q.map Prod.fst)) 960 s1T0 (all_cut ((enumQ (g1Q.map Prod.fst)).drop 960) 960 s1T1 (all_cut (((enumQ (g1Q.map Prod.fst)).drop 960).drop 960) 960 s1T2 (s1T3))))

theorem ch89402_s2 : stabQ 5 g2Q p2Q w2Q 1920 16 = true := by quickRfl

end CertificateChecks.KernelAS91S42

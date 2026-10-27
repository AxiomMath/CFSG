module

public import Certificates.Kernel.D4.ChainAL0
public import Certificates.Kernel.D4.ChainAL1
public import Certificates.Kernel.D4.ChainAL2
public import Certificates.Kernel.D4.ChainAO0
public import Certificates.Kernel.D4.ChainAO1
public import Certificates.Kernel.D4.ChainAO2
public import Certificates.Kernel.D4.ChainAO3
public import Certificates.Kernel.D4.ChainAS10
public import Certificates.Kernel.D4.ChainAS11
public import Certificates.Kernel.D4.ChainAS12
public import Certificates.Kernel.D4.ChainAS13
public import Certificates.Kernel.D4.ChainAS2
public import CFSG.Certificates.Kernel.Spor.RawSch7OSound
public import CFSG.Certificates.Kernel.Spor.RawSch6WSound
public import CFSG.Certificates.Kernel.Common.ForallFrom
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4.CA

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

#kc_forall_from ls0all (fun s => lvSlK 2457 12 (mask 12) (2457 * 12) S SI TR TRI 8
  (stepsAt 2457 12 S 8 BP 0) (LR 0) (s * 256) 256 = true) 10 CertificateChecks.KernelD4.CA.ls0_ 0
#kc_forall_from ls1all (fun s => lvSlK 2457 12 (mask 12) (2457 * 12) S SI TR TRI 8
  (stepsAt 2457 12 S 8 BP 1) (LR 1) (s * 256) 256 = true) 10 CertificateChecks.KernelD4.CA.ls1_ 0
#kc_forall_from ls2all (fun s => lvSlK 2457 12 (mask 12) (2457 * 12) S SI TR TRI 8
  (stepsAt 2457 12 S 8 BP 2) (LR 2) (s * 256) 256 = true) 10 CertificateChecks.KernelD4.CA.ls2_ 0
#kc_forall_from ls3all (fun s => lvSlK 2457 12 (mask 12) (2457 * 12) S SI TR TRI 8
  (stepsAt 2457 12 S 8 BP 3) (LR 3) (s * 256) 256 = true) 10 CertificateChecks.KernelD4.CA.ls3_ 0
#kc_forall_from ls4all (fun s => lvSlK 2457 12 (mask 12) (2457 * 12) S SI TR TRI 8
  (stepsAt 2457 12 S 8 BP 4) (LR 4) (s * 256) 256 = true) 10 CertificateChecks.KernelD4.CA.ls4_ 0
#kc_forall_from ls5all (fun s => lvSlK 2457 12 (mask 12) (2457 * 12) S SI TR TRI 8
  (stepsAt 2457 12 S 8 BP 5) (LR 5) (s * 256) 256 = true) 10 CertificateChecks.KernelD4.CA.ls5_ 0
#kc_forall_from ls6all (fun s => lvSlK 2457 12 (mask 12) (2457 * 12) S SI TR TRI 8
  (stepsAt 2457 12 S 8 BP 6) (LR 6) (s * 256) 256 = true) 10 CertificateChecks.KernelD4.CA.ls6_ 0

theorem hN : 2457 ≤ 10 * 256 := Nat.le_of_ble_eq_true (by quickRfl)

theorem lv0 : levelK 2457 12 (mask 12) (2457 * 12) (mask (2457 * 12)) (pidn 2457 12) S SI TR TRI 8
    (pg 12 (mask 12) BP 0) (stepsAt 2457 12 S 8 BP 0) (LR 0) = true := levelK_of_sl lh0 ls0all hN

theorem lv1 : levelK 2457 12 (mask 12) (2457 * 12) (mask (2457 * 12)) (pidn 2457 12) S SI TR TRI 8
    (pg 12 (mask 12) BP 1) (stepsAt 2457 12 S 8 BP 1) (LR 1) = true := levelK_of_sl lh1 ls1all hN

theorem lv2 : levelK 2457 12 (mask 12) (2457 * 12) (mask (2457 * 12)) (pidn 2457 12) S SI TR TRI 8
    (pg 12 (mask 12) BP 2) (stepsAt 2457 12 S 8 BP 2) (LR 2) = true := levelK_of_sl lh2 ls2all hN

theorem lv3 : levelK 2457 12 (mask 12) (2457 * 12) (mask (2457 * 12)) (pidn 2457 12) S SI TR TRI 8
    (pg 12 (mask 12) BP 3) (stepsAt 2457 12 S 8 BP 3) (LR 3) = true := levelK_of_sl lh3 ls3all hN

theorem lv4 : levelK 2457 12 (mask 12) (2457 * 12) (mask (2457 * 12)) (pidn 2457 12) S SI TR TRI 8
    (pg 12 (mask 12) BP 4) (stepsAt 2457 12 S 8 BP 4) (LR 4) = true := levelK_of_sl lh4 ls4all hN

theorem lv5 : levelK 2457 12 (mask 12) (2457 * 12) (mask (2457 * 12)) (pidn 2457 12) S SI TR TRI 8
    (pg 12 (mask 12) BP 5) (stepsAt 2457 12 S 8 BP 5) (LR 5) = true := levelK_of_sl lh5 ls5all hN

theorem lv6 : levelK 2457 12 (mask 12) (2457 * 12) (mask (2457 * 12)) (pidn 2457 12) S SI TR TRI 8
    (pg 12 (mask 12) BP 6) (stepsAt 2457 12 S 8 BP 6) (LR 6) = true := levelK_of_sl lh6 ls6all hN

theorem hl : LevelsOK 2457 12 S SI LR TR TRI 8 7 BP := by
  intro i hi
  interval_cases i
  exacts [lv0, lv1, lv2, lv3, lv4, lv5, lv6]

#kc_forall_from so_all (fun s => schK 2457 12 (mask 12) (2457 * 12) (pidn 2457 12) S SI LR TR TRI 8
  BP 7 0 pTS (s * 16) 16 = true) 154 CertificateChecks.KernelD4.CA.so_ 0
#kc_forall_from s1all (fun s => s1f s = true) 128 CertificateChecks.KernelD4.CA.s1f 0
#kc_forall_from sch2all (fun s => schK 2457 12 (mask 12) (2457 * 12) (pidn 2457 12) S SI LR TR TRI
  8 BP 7 2 (stepsAt 2457 12 S 8 BP 2) (s * 16) 16 = true) 1 CertificateChecks.KernelD4.CA.sch2_ 0
#kc_forall_from sch3all (fun s => schK 2457 12 (mask 12) (2457 * 12) (pidn 2457 12) S SI LR TR TRI
  8 BP 7 3 (stepsAt 2457 12 S 8 BP 3) (s * 16) 16 = true) 1 CertificateChecks.KernelD4.CA.sch3_ 0
#kc_forall_from sch4all (fun s => schK 2457 12 (mask 12) (2457 * 12) (pidn 2457 12) S SI LR TR TRI
  8 BP 7 4 (stepsAt 2457 12 S 8 BP 4) (s * 16) 16 = true) 1 CertificateChecks.KernelD4.CA.sch4_ 0
#kc_forall_from sch5all (fun s => schK 2457 12 (mask 12) (2457 * 12) (pidn 2457 12) S SI LR TR TRI
  8 BP 7 5 (stepsAt 2457 12 S 8 BP 5) (s * 16) 16 = true) 1 CertificateChecks.KernelD4.CA.sch5_ 0
#kc_forall_from sch6all (fun s => schK 2457 12 (mask 12) (2457 * 12) (pidn 2457 12) S SI LR TR TRI
  8 BP 7 6 (stepsAt 2457 12 S 8 BP 6) (s * 16) 16 = true) 1 CertificateChecks.KernelD4.CA.sch6_ 0

theorem hc0 : rcnt (LR 0) ≤ 154 * 16 := Nat.le_of_ble_eq_true (by quickRfl)
theorem hc1 : rcnt (LR 1) ≤ 128 * 16 := Nat.le_of_ble_eq_true (by quickRfl)
theorem hc2 : rcnt (LR 2) ≤ 1 * 16 := Nat.le_of_ble_eq_true (by quickRfl)
theorem hc3 : rcnt (LR 3) ≤ 1 * 16 := Nat.le_of_ble_eq_true (by quickRfl)
theorem hc4 : rcnt (LR 4) ≤ 1 * 16 := Nat.le_of_ble_eq_true (by quickRfl)
theorem hc5 : rcnt (LR 5) ≤ 1 * 16 := Nat.le_of_ble_eq_true (by quickRfl)
theorem hc6 : rcnt (LR 6) ≤ 1 * 16 := Nat.le_of_ble_eq_true (by quickRfl)

theorem h1 (h₀ cnt : Nat) : schK 2457 12 (mask 12) (2457 * 12) (pidn 2457 12) S SI LR TR TRI 8 BP 7
    1 (stepsAt 2457 12 S 8 BP 1) h₀ cnt = true :=
  Orb.schK_of_sch6WL (i := 1) head hl inv1 g23 g34 g45 g56 tsb1 tj1 wds1 lo1 hc1 s1all
    hc2 sch2all hc3 sch3all hc4 sch4all hc5 sch5all hc6 sch6all h₀ cnt

theorem h0 (h₀ cnt : Nat) : schK 2457 12 (mask 12) (2457 * 12) (pidn 2457 12) S SI LR TR TRI 8 BP 7
    0 (stepsAt 2457 12 S 8 BP 0) h₀ cnt = true :=
  Orb.schK_of_sch7OL (i := 0) head hl inv g12 g23 g34 g45 g56 tsb tso hc0 so_all hc1
    (fun _ _ => h1 _ _) hc2 sch2all hc3 sch3all hc4 sch4all hc5 sch5all hc6 sch6all h₀ cnt

theorem hs : ∀ i < 7, ∀ s < 154, schK 2457 12 (mask 12) (2457 * 12) (pidn 2457 12) S SI LR TR TRI
    8 BP 7 i (stepsAt 2457 12 S 8 BP i) (s * 16) 16 = true := by
  intro i hi
  interval_cases i
  · exact fun s _ => h0 _ _
  · exact fun s _ => h1 _ _
  · exact schK_slices hc2 sch2all
  · exact schK_slices hc3 sch3all
  · exact schK_slices hc4 sch4all
  · exact schK_slices hc5 sch5all
  · exact schK_slices hc6 sch6all

end CertificateChecks.KernelD4.CA

end

module

public import Certificates.Kernel.Co2Smith.ChainG0O
public import Certificates.Kernel.Co2Smith.ChainG0L
public import Certificates.Kernel.Co2Smith.ChainG0S10
public import Certificates.Kernel.Co2Smith.ChainG0S11
public import CFSG.Certificates.Kernel.Spor.RawSchWSound
public import CFSG.Certificates.Kernel.Spor.RawSlSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb

theorem chG0Ls0 : ∀ s < 9, lvSlK 2300 12 (mask 12) (2300 * 12) CG0.S CG0.SI CG0.TR CG0.TRI 19
    (stepsAt 2300 12 CG0.S 19 CG0.BP 0) (CG0.LR 0) (s * 256) 256 = true := by
  intro s hs
  interval_cases s
  exacts [CG0.ls0_0, CG0.ls0_1, CG0.ls0_2, CG0.ls0_3, CG0.ls0_4, CG0.ls0_5, CG0.ls0_6, CG0.ls0_7,
      CG0.ls0_8]

theorem chG0Lv0 : levelK 2300 12 (mask 12) (2300 * 12) (mask (2300 * 12)) (pidn 2300 12) CG0.S
    CG0.SI CG0.TR CG0.TRI 19 (pg 12 (mask 12) CG0.BP 0) (stepsAt 2300 12 CG0.S 19 CG0.BP 0) (CG0.LR
    0) = true :=
  levelK_of_sl (NS := 9) (CH := 256) CG0.lh0 chG0Ls0 (Nat.le_of_ble_eq_true (by quickRfl))

theorem chG0Ls1 : ∀ s < 9, lvSlK 2300 12 (mask 12) (2300 * 12) CG0.S CG0.SI CG0.TR CG0.TRI 19
    (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (CG0.LR 1) (s * 256) 256 = true := by
  intro s hs
  interval_cases s
  exacts [CG0.ls1_0, CG0.ls1_1, CG0.ls1_2, CG0.ls1_3, CG0.ls1_4, CG0.ls1_5, CG0.ls1_6, CG0.ls1_7,
      CG0.ls1_8]

theorem chG0Lv1 : levelK 2300 12 (mask 12) (2300 * 12) (mask (2300 * 12)) (pidn 2300 12) CG0.S
    CG0.SI CG0.TR CG0.TRI 19 (pg 12 (mask 12) CG0.BP 1) (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (CG0.LR
    1) = true :=
  levelK_of_sl (NS := 9) (CH := 256) CG0.lh1 chG0Ls1 (Nat.le_of_ble_eq_true (by quickRfl))

theorem chG0Ls2 : ∀ s < 9, lvSlK 2300 12 (mask 12) (2300 * 12) CG0.S CG0.SI CG0.TR CG0.TRI 19
    (stepsAt 2300 12 CG0.S 19 CG0.BP 2) (CG0.LR 2) (s * 256) 256 = true := by
  intro s hs
  interval_cases s
  exacts [CG0.ls2_0, CG0.ls2_1, CG0.ls2_2, CG0.ls2_3, CG0.ls2_4, CG0.ls2_5, CG0.ls2_6, CG0.ls2_7,
      CG0.ls2_8]

theorem chG0Lv2 : levelK 2300 12 (mask 12) (2300 * 12) (mask (2300 * 12)) (pidn 2300 12) CG0.S
    CG0.SI CG0.TR CG0.TRI 19 (pg 12 (mask 12) CG0.BP 2) (stepsAt 2300 12 CG0.S 19 CG0.BP 2) (CG0.LR
    2) = true :=
  levelK_of_sl (NS := 9) (CH := 256) CG0.lh2 chG0Ls2 (Nat.le_of_ble_eq_true (by quickRfl))

theorem chG0Ls3 : ∀ s < 9, lvSlK 2300 12 (mask 12) (2300 * 12) CG0.S CG0.SI CG0.TR CG0.TRI 19
    (stepsAt 2300 12 CG0.S 19 CG0.BP 3) (CG0.LR 3) (s * 256) 256 = true := by
  intro s hs
  interval_cases s
  exacts [CG0.ls3_0, CG0.ls3_1, CG0.ls3_2, CG0.ls3_3, CG0.ls3_4, CG0.ls3_5, CG0.ls3_6, CG0.ls3_7,
      CG0.ls3_8]

theorem chG0Lv3 : levelK 2300 12 (mask 12) (2300 * 12) (mask (2300 * 12)) (pidn 2300 12) CG0.S
    CG0.SI CG0.TR CG0.TRI 19 (pg 12 (mask 12) CG0.BP 3) (stepsAt 2300 12 CG0.S 19 CG0.BP 3) (CG0.LR
    3) = true :=
  levelK_of_sl (NS := 9) (CH := 256) CG0.lh3 chG0Ls3 (Nat.le_of_ble_eq_true (by quickRfl))

theorem chG0Ls4 : ∀ s < 9, lvSlK 2300 12 (mask 12) (2300 * 12) CG0.S CG0.SI CG0.TR CG0.TRI 19
    (stepsAt 2300 12 CG0.S 19 CG0.BP 4) (CG0.LR 4) (s * 256) 256 = true := by
  intro s hs
  interval_cases s
  exacts [CG0.ls4_0, CG0.ls4_1, CG0.ls4_2, CG0.ls4_3, CG0.ls4_4, CG0.ls4_5, CG0.ls4_6, CG0.ls4_7,
      CG0.ls4_8]

theorem chG0Lv4 : levelK 2300 12 (mask 12) (2300 * 12) (mask (2300 * 12)) (pidn 2300 12) CG0.S
    CG0.SI CG0.TR CG0.TRI 19 (pg 12 (mask 12) CG0.BP 4) (stepsAt 2300 12 CG0.S 19 CG0.BP 4) (CG0.LR
    4) = true :=
  levelK_of_sl (NS := 9) (CH := 256) CG0.lh4 chG0Ls4 (Nat.le_of_ble_eq_true (by quickRfl))

theorem chG0LOK : LevelsOK 2300 12 CG0.S CG0.SI CG0.LR CG0.TR CG0.TRI 19 5 CG0.BP := by
  intro i hi
  interval_cases i
  exacts [chG0Lv0, chG0Lv1, chG0Lv2, chG0Lv3, chG0Lv4]

theorem chG0C1 : rcnt (CG0.LR 1) ≤ 71 * 8 :=
  Nat.le_of_ble_eq_true (by quickRfl)

theorem chG0C2 : rcnt (CG0.LR 2) ≤ 24 * 8 :=
  Nat.le_of_ble_eq_true (by quickRfl)

theorem chG0C3 : rcnt (CG0.LR 3) ≤ 2 * 8 :=
  Nat.le_of_ble_eq_true (by quickRfl)

theorem chG0C4 : rcnt (CG0.LR 4) ≤ 1 * 8 :=
  Nat.le_of_ble_eq_true (by quickRfl)

theorem chG0L2 : ∀ s < 24, schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR
    CG0.TR CG0.TRI 19 CG0.BP 5 2 (stepsAt 2300 12 CG0.S 19 CG0.BP 2) (s * 8) 8 = true := by
  intro s hs
  interval_cases s
  exacts [CG0.sch2_0, CG0.sch2_1, CG0.sch2_2, CG0.sch2_3, CG0.sch2_4, CG0.sch2_5, CG0.sch2_6,
      CG0.sch2_7, CG0.sch2_8, CG0.sch2_9, CG0.sch2_10, CG0.sch2_11, CG0.sch2_12, CG0.sch2_13,
      CG0.sch2_14, CG0.sch2_15, CG0.sch2_16, CG0.sch2_17, CG0.sch2_18, CG0.sch2_19, CG0.sch2_20,
      CG0.sch2_21, CG0.sch2_22, CG0.sch2_23]

theorem chG0L3 : ∀ s < 2, schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR
    CG0.TR CG0.TRI 19 CG0.BP 5 3 (stepsAt 2300 12 CG0.S 19 CG0.BP 3) (s * 8) 8 = true := by
  intro s hs
  interval_cases s
  exacts [CG0.sch3_0, CG0.sch3_1]

theorem chG0L4 : ∀ s < 1, schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR
    CG0.TR CG0.TRI 19 CG0.BP 5 4 (stepsAt 2300 12 CG0.S 19 CG0.BP 4) (s * 8) 8 = true := by
  intro s hs
  interval_cases s
  exacts [CG0.sch4_0]

theorem chG0O1 : ∀ s < 71, schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR
    CG0.TR CG0.TRI 19 CG0.BP 5 1 chG0T1 (s * 8) 8 = true := by
  intro s hs
  interval_cases s
  exacts [chG0S1_0, chG0S1_1, chG0S1_2, chG0S1_3, chG0S1_4, chG0S1_5, chG0S1_6, chG0S1_7, chG0S1_8,
      chG0S1_9, chG0S1_10, chG0S1_11, chG0S1_12, chG0S1_13, chG0S1_14, chG0S1_15, chG0S1_16,
      chG0S1_17, chG0S1_18, chG0S1_19, chG0S1_20, chG0S1_21, chG0S1_22, chG0S1_23, chG0S1_24,
      chG0S1_25, chG0S1_26, chG0S1_27, chG0S1_28, chG0S1_29, chG0S1_30, chG0S1_31, chG0S1_32,
      chG0S1_33, chG0S1_34, chG0S1_35, chG0S1_36, chG0S1_37, chG0S1_38, chG0S1_39, chG0S1_40,
      chG0S1_41, chG0S1_42, chG0S1_43, chG0S1_44, chG0S1_45, chG0S1_46, chG0S1_47, chG0S1_48,
      chG0S1_49, chG0S1_50, chG0S1_51, chG0S1_52, chG0S1_53, chG0S1_54, chG0S1_55, chG0S1_56,
      chG0S1_57, chG0S1_58, chG0S1_59, chG0S1_60, chG0S1_61, chG0S1_62, chG0S1_63, chG0S1_64,
      chG0S1_65, chG0S1_66, chG0S1_67, chG0S1_68, chG0S1_69, chG0S1_70]

theorem chG0H1 (h₀ cnt : Nat) : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI
    CG0.LR CG0.TR CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) h₀ cnt = true :=
  schK_of_schOL_stw (kO := 13) (E := 5) (i := 1) (TS := chG0T1) (TJ := chG0J1) (NSi := 71) (CH :=
      8) (W := chG0D)
    (WS := chG0W1) CG0.head chG0LOK (by omega) (lv12K_facts CG0.g12).1
    (fun k hk => by
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      exacts [CG0.g23, CG0.g34])
    chG0B1_k chG0W1_k chG0I1_k chG0C1 chG0O1
    (fun k hk => by
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
      exacts [⟨24, chG0C2, chG0L2⟩, ⟨2, chG0C3, chG0L3⟩, ⟨1, chG0C4, chG0L4⟩])
    h₀ cnt

theorem CG0.sch1_0 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (0 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_1 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (1 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_2 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (2 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_3 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (3 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_4 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (4 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_5 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (5 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_6 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (6 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_7 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (7 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_8 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (8 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_9 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (9 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_10 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (10 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_11 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (11 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_12 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (12 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_13 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (13 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_14 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (14 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_15 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (15 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_16 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (16 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_17 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (17 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_18 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (18 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_19 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (19 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_20 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (20 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_21 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (21 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_22 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (22 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_23 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (23 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_24 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (24 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_25 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (25 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_26 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (26 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_27 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (27 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_28 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (28 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_29 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (29 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_30 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (30 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_31 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (31 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_32 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (32 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_33 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (33 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_34 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (34 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_35 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (35 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_36 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (36 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_37 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (37 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_38 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (38 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_39 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (39 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_40 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (40 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_41 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (41 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_42 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (42 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_43 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (43 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_44 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (44 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_45 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (45 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_46 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (46 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_47 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (47 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_48 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (48 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_49 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (49 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_50 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (50 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_51 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (51 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_52 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (52 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_53 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (53 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_54 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (54 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_55 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (55 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_56 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (56 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_57 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (57 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_58 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (58 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_59 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (59 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_60 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (60 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_61 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (61 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_62 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (62 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_63 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (63 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_64 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (64 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_65 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (65 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_66 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (66 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_67 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (67 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_68 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (68 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_69 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (69 * 8) 8 = true :=
  chG0H1 _ _

theorem CG0.sch1_70 : schK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.S CG0.SI CG0.LR CG0.TR
    CG0.TRI 19 CG0.BP 5 1 (stepsAt 2300 12 CG0.S 19 CG0.BP 1) (70 * 8) 8 = true :=
  chG0H1 _ _

end CertificateChecks.KernelCo2Smith

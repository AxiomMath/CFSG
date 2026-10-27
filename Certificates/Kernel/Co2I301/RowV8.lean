module

public import Certificates.Kernel.Co2I301.Mats
public import Certificates.Kernel.SporSch.Co2M.QMod
public import Certificates.Data.Kernel.SporSch.SpanK3
public import Certificates.Data.Co2RowChk
public meta import Certificates.Data.Co2RowChk
meta import Certificates.Kernel.SporSch.HN.GenNTree
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic

public section

set_option maxRecDepth 400000
set_option exponentiation.threshold 600

namespace CertificateChecks.KernelCo2I301

open CFSG.Sporadic.SmallF2.Native CFSG.LocalAnalysis.GLTheoremA.H301B.Co2RowNative

meta def rowTabs : List Nat := [co2K1Cols, co2K2Cols, co2DCols].map fun T =>
  (List.range 256).foldl (fun acc a => acc ||| (vecMulN 8 T a <<< (8 * a))) 0

end CertificateChecks.KernelCo2I301

#kss_ntree CertificateChecks.KernelCo2I301.RT CertificateChecks.KernelCo2I301.rowTabs

namespace CertificateChecks.KernelCo2I301

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2M CFSG.KS.MatRep CFSG.KS.SpanK
open CFSG.RankThree.Native.F2
open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.Sporadic.SmallF2.Native
open CFSG.LocalAnalysis.GLTheoremA.H301B.Co2RowNative
open CertificateChecks.KernelSporSch.Co2M (cmpP invP powP prodOrZK qT)

@[expose] noncomputable def rowP (k : ℕ) : ℕ × ℕ := (M k, MI k)

theorem pow5_ok : Nat.beq (powP (cmpP (rowP 5) (rowP 6)) 5).1 I22 = true := by
  decide +kernel

@[expose] noncomputable def colsK (p : ℕ × ℕ) (cols : Array ℕ) : Bool :=
  allLt 8 fun l => decide (cols[l]! < 256) &&
    prodOrZK (cmpP (cmpP p (qT.getD l (0, 0))) (invP p)).1 cols[l]!

theorem cols8_ok : (colsK (rowP 5) co2K1Cols && colsK (rowP 6) co2K2Cols &&
    colsK (rowP 1) co2DCols) = true := by
  decide +kernel

theorem tab8_ok : allN 256 (fun a => Nat.beq (tabK (RT 0) a) (vecMulN 8 co2K1Cols a) &&
    Nat.beq (tabK (RT 1) a) (vecMulN 8 co2K2Cols a) &&
    Nat.beq (tabK (RT 2) a) (vecMulN 8 co2DCols a)) = true := by
  decide +kernel

@[expose] noncomputable def spanR (v : ℕ) : Bool :=
  bif Nat.blt v 255 then Nat.beq (iterK3 (tabK (RT 0)) (tabK (RT 1)) (tabK (RT 2)) 5
    (insK 1 (Nat.succ v))) (Nat.sub (Nat.shiftLeft 1 256) 1) else true

theorem spanR0 : allN 16 (fun t => spanR (Nat.add 0 t)) = true := by quickRfl
theorem spanR1 : allN 16 (fun t => spanR (Nat.add 16 t)) = true := by quickRfl
theorem spanR2 : allN 16 (fun t => spanR (Nat.add 32 t)) = true := by quickRfl
theorem spanR3 : allN 16 (fun t => spanR (Nat.add 48 t)) = true := by quickRfl
theorem spanR4 : allN 16 (fun t => spanR (Nat.add 64 t)) = true := by quickRfl
theorem spanR5 : allN 16 (fun t => spanR (Nat.add 80 t)) = true := by quickRfl
theorem spanR6 : allN 16 (fun t => spanR (Nat.add 96 t)) = true := by quickRfl
theorem spanR7 : allN 16 (fun t => spanR (Nat.add 112 t)) = true := by quickRfl
theorem spanR8 : allN 16 (fun t => spanR (Nat.add 128 t)) = true := by quickRfl
theorem spanR9 : allN 16 (fun t => spanR (Nat.add 144 t)) = true := by quickRfl
theorem spanR10 : allN 16 (fun t => spanR (Nat.add 160 t)) = true := by quickRfl
theorem spanR11 : allN 16 (fun t => spanR (Nat.add 176 t)) = true := by quickRfl
theorem spanR12 : allN 16 (fun t => spanR (Nat.add 192 t)) = true := by quickRfl
theorem spanR13 : allN 16 (fun t => spanR (Nat.add 208 t)) = true := by quickRfl
theorem spanR14 : allN 16 (fun t => spanR (Nat.add 224 t)) = true := by quickRfl
theorem spanR15 : allN 16 (fun t => spanR (Nat.add 240 t)) = true := by quickRfl

end CertificateChecks.KernelCo2I301

end

module

public import Certificates.Kernel.Asch54.Fi22Data
public import Certificates.Kernel.Asch54.Fi22Chain
public import Certificates.Kernel.Sporadic.Fi22.X2069Final
public import Certificates.Kernel.Sporadic.Fi22.G3147
public import Certificates.Kernel.Sporadic.Fi22.E2065T
public import Certificates.Kernel.Sporadic.Fi22.E2067T
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.A54F22

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Mathieu CertificateChecks.KernelSpor
open CFSG.LocalAnalysis.WeakClosure81.Asch54Fi22

abbrev BL : Array Nat := #[0, 1, 2, 3, 6, 4]

@[expose] noncomputable def M : Nat := A54F22M.F 0

@[expose] noncomputable def T1 : Nat := Fi22ExtT.L 22

@[expose] def W (k : Nat) : List Int :=
  [[19, 20, 4, 19, 13, 20, 15], [11, 6, 2, 13, 14, 8, 13, -19, 16]].getD k []

@[expose] noncomputable def wA (wd : List Int) : Nat :=
  wordK 3510 12 (mask 12) (pidn 3510 12) A54F22C.S A54F22C.SI wd

@[expose] noncomputable def wR (wd : List Int) : Nat :=
  wordK 3510 12 (mask 12) (pidn 3510 12) R RI wd

@[expose] def GD : List (List Int) := (genWords ()).toList.drop 11

theorem bindT : allN 9 (fun j => Nat.beq (A54F22C.S j) (Fi22X.TS j)) = true := by quickRfl
theorem bindX : allN 2 (fun k => Nat.beq (A54F22C.S (Nat.add 9 k)) (A54F22X.F k)) = true := by
  quickRfl
theorem baseC : allN 6 (fun t => Nat.beq BL[t]! (pg 12 (mask 12) A54F22C.BP t)) = true := by
  quickRfl
theorem inP : allN 20 (fun j => bAnd(Fi22X.cn (A54F22C.S j), Fi22X.siftP (A54F22C.S j))) = true := by
  quickRfl
theorem orb : (List.range 6).map (fun i => rcnt (A54F22C.LR i)) = [1536, 360, 32, 1, 1, 1] := by
  decide +kernel

theorem tComm : bAnd(Fi22X.cn T1, allN 9 (fun i =>
    Nat.beq (Fi22X.c (Fi22X.TS i) T1) (Fi22X.c T1 (Fi22X.TS i)))) = true := by quickRfl

theorem mInv : bAnd(Fi22X.cn M, permOK 3510 12 (mask 12) (3510 * 12) M M) = true := by quickRfl
theorem mU : Fi22X.siftP (Fi22X.c Fi22X.GO M) = true := by quickRfl
theorem mT : allN 9 (fun i => Fi22X.siftT (Fi22X.c M (Fi22X.c (Fi22X.TS i) M))) = true := by
  quickRfl
theorem mA : allN 2 (fun k => bAnd(lettersK 20 (W k),
    Nat.beq (Fi22X.c M (Fi22X.c (A54F22X.F k) M)) (wA (W k)))) = true := by quickRfl
theorem mt1 : Nat.beq (Fi22X.c M T1) (Fi22X.c T1 M) = true := by quickRfl

theorem slpPerm : allN 26 (fun j => bAnd(Fi22X.cn (R j),
    permOK 3510 12 (mask 12) (3510 * 12) (R j) (RI j))) = true := by quickRfl
theorem slpBind : bAnd(allN 2 (fun k => Nat.beq (R k) (A54F22X.F k)),
    allN 9 (fun k => Nat.beq (R (Nat.add 2 k)) (Fi22CentT.L (Nat.add 19 k)))) = true := by quickRfl
theorem slpDeriv : bAnd(Nat.beq (Nat.add (lenW GD) 11) 26, allN 26 (fun j => bIf(Nat.blt j 11, true,
    bAnd(lettersK j (dword GD 11 j), Nat.beq (R j) (wR (dword GD 11 j)))))) = true := by quickRfl
theorem slpGen : bAnd(bAnd(lettersK 26 (genA0Word ()), lettersK 26 (genA1Word ())),
    bAnd(Nat.beq (Fi22CGT.F 0) (wR (genA0Word ())), Nat.beq (Fi22CGT.F 1) (wR (genA1Word ())))) =
    true := by quickRfl

end CertificateChecks.KernelSpor.A54F22

end

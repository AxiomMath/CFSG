module

public import Certificates.Kernel.Co2Smith.ChainG0Data
public import Certificates.Data.Kernel.Spor.RawSchW
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb

@[expose] def chG0T1 : Nat := 303040771

@[expose] def chG0J1 : Nat := 5084180724582662

@[expose] def chG0W1 : List (List Nat) :=
  [[1, 0, 2, 0, 2, 1, 0, 1, 0, 2, 0, 2, 1, 0],
   [0],
   [1, 0, 0, 1, 0, 1],
   [0, 1, 2, 0, 0, 2, 1, 0, 1, 2, 0, 2, 0, 1, 0],
   [2, 1, 0, 1, 0, 2, 1, 0, 1, 2, 1, 0, 1, 0, 2, 0],
   [1, 0, 1, 0, 2, 0, 2, 1, 0, 1, 0, 2, 0, 2],
   [1],
   [2, 0, 1, 2, 1, 0, 1, 0, 0, 1, 2, 0, 1, 2, 0, 1, 0, 1, 2],
   [2]]

theorem chG0B1_k : allN (stCnt chG0T1) (fun a => Nat.blt (stAt chG0T1 a) 19) = true := by
  quickRfl

theorem chG0I1_k : incK chG0J1 chG0T1 = true := by
  quickRfl

theorem chG0W1_k : stwK 2300 12 (mask 12) (pidn 2300 12) CG0.S CG0.SI 19 (stepsAt 2300 12 CG0.S 19
    CG0.BP 1) chG0J1 chG0W1 0 =
    true := by
  quickRfl

end CertificateChecks.KernelCo2Smith

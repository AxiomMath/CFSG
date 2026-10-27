module

public import Certificates.Kernel.CF23L34.HeGSL
public import Certificates.Kernel.SporSch.HeT.W2117K
public import Certificates.Kernel.LocalComp.HeFix2329.Enum
public import Certificates.Data.GrSLitHeZStar
public import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeZS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Mathieu CFSG.KS.PEnum CFSG.KC.PermTool
open CFSG.ComponentClassification.GrSLit.HeGS Certificates.GrSLitHeZStar
open CertificateChecks.KernelLC.HeFix CertificateChecks.KernelLC.HeGS36
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch

@[expose] noncomputable def O : Nat := pc (HeW17.C 0) (HeW17.C 0)

@[expose] noncomputable def D1 : Nat := pc (HeW17.D 0) (HeW17.D 0)

@[expose] noncomputable def DY : Nat := pc (pc D1 (HeW17.D 2)) (HeW17.D 2)

@[expose] noncomputable def D2 : Nat := pc DY (pc DY DY)

@[expose] noncomputable def p32 (p q : Nat) : Nat := pcomp 32 6 (mask 6) p q

@[expose] noncomputable def cmK (t j : Nat) : Bool :=
  Nat.beq (p32 t (Q j)) (p32 (Q j) t) || Nat.beq (p32 t (Q j)) (p32 (Q 0) (p32 (Q j) t))

@[expose] noncomputable def sylK (i : Nat) : Bool :=
  !(allN 5 (cmK (HeT32.T i))) || Nat.beq (p32 (HeT32.T i) (HeT32.T i)) (pidn 32 6)

@[expose] noncomputable def ZU (x : Nat) : Nat :=
  CFSG.KS.PEnum.wordTabK 105 7 (mask 7) (pidn 105 7) HDE.G (lget2 heZWords x)

@[expose] noncomputable def g7 (p i : Nat) : Nat := pg 7 (mask 7) p i

theorem ch22704_c : (cn (HeW17.C 0) && Nat.beq (pc O O) (pidn 8330 14) &&
    !Nat.beq O (pidn 8330 14) && Nat.beq (CFSG.KC.HeFixK.fixK 8330 14 O) 346) = true := by
  quickRfl

theorem ch22704_d : (cn (HeW17.D 0) && cn (HeW17.D 2) && Nat.beq (pc D1 D1) (pidn 8330 14) &&
    Nat.beq (pc D2 D2) (pidn 8330 14) && !Nat.beq D1 (pidn 8330 14) &&
    !Nat.beq D2 (pidn 8330 14) && !Nat.beq D1 D2 && Nat.beq (pc D1 D2) (pc D2 D1)) = true := by
  quickRfl

theorem ch22704_syl : allN HeT32.N sylK = true := by quickRfl

theorem ch22704_id32 : (CFSG.KS.Prim.idK 32 6 (mask 6) &&
    canonK 32 6 (mask 6) (32 * 6) (pidn 32 6) && Nat.beq HeT32.N 1024) = true := by
  quickRfl

theorem ch22704_trans : allN 105 (fun x => Nat.beq (g7 (ZU x) 0) x) = true := by quickRfl

theorem ch22704_fix : (Nat.beq (g7 (HDE.G 2) 79) 63 && Nat.beq (g7 (HDE.G 2) 94) 86 &&
    allN 105 (fun x => Nat.beq x 0 ||
      !(Nat.beq (g7 (HDE.G 2) (g7 (ZU 79) x)) (g7 (ZU 63) x) &&
        Nat.beq (g7 (HDE.G 2) (g7 (ZU 94) x)) (g7 (ZU 86) x)))) = true := by
  quickRfl

theorem ch22704_u : strictB (K (heGSComm2 heGSUComm)) (fun u =>
    Nat.beq (CFSG.KC.HeFixK.fixK 8330 14 u) 346 &&
      strictB (pc (HG.F 0) u) (fun v => Nat.beq (CFSG.KC.HeFixK.fixK 8330 14 v) 346 &&
        Nat.beq (pc v v) (pidn 8330 14) && !Nat.beq v (pidn 8330 14))) = true := by
  quickRfl

end CertificateChecks.KernelLC.HeZS

end

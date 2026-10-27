module

public import Certificates.Kernel.Asch54.McLData
public import Certificates.Kernel.Sporadic.McLC.SylK
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporMcLInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLAsch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CertificateChecks.KernelSpor.McLC

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp (nat_lit 275) (nat_lit 9) (mask 9) p q

@[expose] noncomputable def sT (i : Nat) : Nat := McLCS.T i

@[expose] noncomputable def aT : Nat := sT (r32 McLAV (nat_lit 0))

@[expose] noncomputable def uT : Nat := sT (r32 McLAV (nat_lit 1))

@[expose] noncomputable def auT : Nat := sT (r32 McLAV (nat_lit 2))

@[expose] noncomputable def vL : List Nat := [pidn (nat_lit 275) (nat_lit 9), aT, uT, auT]

@[expose] noncomputable def commK (x s : Nat) : Bool := Nat.beq (pc x s) (pc s x)

@[expose] noncomputable def z2K (a x s : Nat) : Bool :=
  strictB (pc x s) fun xs => strictB (pc s x) fun sx =>
    bIf(Nat.beq xs sx, true, Nat.beq xs (pc a sx))

@[expose] noncomputable def cenK (x : Nat) : Bool :=
  bIf(Nat.beq x (pidn (nat_lit 275) (nat_lit 9)), true, bIf(Nat.beq x aT, true,
    List.any (List.range (nat_lit 4)) fun j => bIf(commK x (McLCS.GI j), false, true)))

@[expose] noncomputable def z2outK (x : Nat) : Bool :=
  bIf(List.any vL (Nat.beq x), true,
    List.any (List.range (nat_lit 4)) fun j => bIf(z2K aT x (McLCS.GI j), false, true))

@[expose] noncomputable def z2inK (v : Nat) : Bool :=
  allN (nat_lit 128) fun i => z2K aT v (sT i)

@[expose] noncomputable def normK (g : Nat) : Bool :=
  List.all vL fun v => bAnd(List.any vL fun w => Nat.beq (pc g v) (pc w g),
    List.any vL fun w => Nat.beq (pc v g) (pc g w))

@[expose] noncomputable def GKH (l y : Nat) : Nat :=
  nIf(Nat.beq l (nat_lit 1), LJ (nat_lit 0) y, nIf(Nat.beq l (nat_lit 2), LJ (nat_lit 2) y,
    pk (McLAHG (Nat.sub l (nat_lit 3))) y))

theorem vBase_ok : bAnd(Nat.blt (r32 McLAV (nat_lit 0)) (nat_lit 128),
    bAnd(Nat.blt (r32 McLAV (nat_lit 1)) (nat_lit 128),
    bAnd(Nat.blt (r32 McLAV (nat_lit 2)) (nat_lit 128),
    bAnd(allN (nat_lit 275) (fun x => Nat.beq (pk aT x) (r32 McLK.AL x)),
    bAnd(Nat.beq auT (pc aT uT),
    bAnd(bIf(Nat.beq uT (pidn (nat_lit 275) (nat_lit 9)), false, true),
      bIf(Nat.beq uT aT, false, true))))))) = true := by
  quickRfl

theorem cen_ok : allN (nat_lit 128) (fun i => cenK (sT i)) = true := by quickRfl

theorem z2out_ok : allN (nat_lit 128) (fun i => z2outK (sT i)) = true := by quickRfl

theorem z2in_ok : List.all vL z2inK = true := by quickRfl

theorem hGen_ok : allN (nat_lit 3) (fun j => bAnd(cKS (McLAHG j), allN (nat_lit 275) fun x =>
    Nat.beq (pk (McLAHG j) x)
      (List.foldr GA x (List.getD CFSG.LocalAnalysis.WeakClosure81.SporMcL.hWords j [])))) =
      true := by
  quickRfl

theorem eBase_ok : bAnd(allN (nat_lit 2) (fun j => bAnd(Nat.beq (McLAE.GI j) (McLAHG j),
      bAnd(Nat.beq (McLAE.G j) (pidn (nat_lit 275) (nat_lit 9)), bAnd(cKS (McLAEI j),
        invEqK (nat_lit 275) (nat_lit 9) (mask 9) (275 * 9) (McLAE.GI j) (McLAEI j))))),
    bAnd(Nat.beq McLAE.cnt (nat_lit 9),
      penumHdK (pidn (nat_lit 275) (nat_lit 9)) McLAE.cnt (nat_lit 50000) McLAE.T McLAE.PL)) =
      true := by
  quickRfl

theorem eE_ok : penumSlK (nat_lit 275) (nat_lit 9) (mask 9) (275 * 9) true McLAE.G McLAE.GI
    (nat_lit 2) McLAE.cnt McLAE.T McLAE.PL McLAE.POS McLAE.SRT McLAE.SRI (nat_lit 0) McLAE.cnt =
      true := by
  quickRfl

theorem eH_ok : slK McLAE.cnt (hsortPtK (nat_lit 275) (nat_lit 9) (mask 9) McLAE.cnt McLAE.T
    McLAE.HS McLAE.HSI) (nat_lit 0) McLAE.cnt = true := by quickRfl

theorem eCl_ok : slK (Nat.mul McLAE.cnt 4)
    (findPtK McLAE.cnt McLAE.T (prodQK 275 9 (mask 9) 4 McLAE.T (bothK 2 McLAE.GI McLAEI))
      McLAECl) 0 (Nat.mul McLAE.cnt 4) = true := by quickRfl

theorem uBase_ok : bAnd(allN (nat_lit 2) (fun j => bAnd(cKS (McLAU.G j), bAnd(cKS (McLAU.GI j),
      invEqK (nat_lit 275) (nat_lit 9) (mask 9) (275 * 9) (McLAU.G j) (McLAU.GI j)))),
    bAnd(allN (nat_lit 275) (fun x => bAnd(Nat.beq (pk (McLAU.G (nat_lit 0)) x) (LJ (nat_lit 0) x),
      Nat.beq (pk (McLAU.G (nat_lit 1)) x) (LJ (nat_lit 2) x))),
    bAnd(Nat.beq McLAU.cnt (nat_lit 210), bAnd(Nat.beq McLAU.R uT,
      penumHdK McLAU.R McLAU.cnt (nat_lit 50000) McLAU.T McLAU.PL)))) = true := by
  quickRfl

theorem uE_ok : penumSlK (nat_lit 275) (nat_lit 9) (mask 9) (275 * 9) true McLAU.G McLAU.GI
    (nat_lit 2) McLAU.cnt McLAU.T McLAU.PL McLAU.POS McLAU.SRT McLAU.SRI (nat_lit 0) McLAU.cnt =
      true := by
  quickRfl

theorem norm_ok : bAnd(allN (nat_lit 3) (fun j => normK (McLAHG j)),
    allN (nat_lit 4) (fun j => normK (McLCS.GI j))) = true := by
  quickRfl

theorem word_ok : allN (nat_lit 275) (fun x => bAnd(
    Nat.beq (List.foldr GKH x CFSG.LocalAnalysis.WeakClosure81.SporMcL.khWordA) (r32 McLK.AL x),
    Nat.beq (List.foldr GKH x CFSG.LocalAnalysis.WeakClosure81.SporMcL.khWordB)
      (r32 McLK.BE x))) = true := by
  quickRfl

end CertificateChecks.KernelSpor.McLAsch

end

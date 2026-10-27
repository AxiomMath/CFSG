module

public import Certificates.Kernel.A312He.D
public import Certificates.Kernel.A312He.Data
public import Certificates.Kernel.He7149.D
public import Certificates.Kernel.LocalQT.Base.C4141D
public import Certificates.Data.Kernel.A312HeK
public import Certificates.Data.Kernel.LocalQT.PermW
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HeInputs
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.A312He

open CFSG.KC.E64F CFSG.KC.A312HeK CFSG.Quasithin.A312He CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.He CFSG.QuasithinUnique.K1.SporadicPerm

@[expose] noncomputable def LF3 (l p : Nat) : Nat := CFSG.KC.LQT.PW.imgW 14 (Y3.TF l) p

@[expose] noncomputable def LF4 (l p : Nat) : Nat := CFSG.KC.LQT.PW.imgW 14 (Y4.TF l) p

@[expose] noncomputable def LF7 (l p : Nat) : Nat :=
  CFSG.KC.LQT.PW.imgW 14 (bif Nat.blt l 5 then CFSG.KD.He7149.TF l else Y7.TF (l - 5)) p

@[expose] noncomputable def LAB (l p : Nat) : Nat :=
  CFSG.KC.LQT.PW.imgW 14 (CFSG.KD.LQT.C4141.TF l) p

@[expose] def qg (x : QuotGen) : List Nat × Nat × Nat := (x.w, x.k, x.m)

@[expose] def mw (j : Nat) : List Nat := (heMwLit[j]!).headD []

theorem lt3_ok : (Nat.beq (Y3.TF 0) (CFSG.KD.LQT.C4141.TF 197) &&
    Nat.beq (Y3.TF 1) (CFSG.KD.LQT.C4141.TF 207) && Nat.beq (Y3.TF 2) (CFSG.KD.LQT.C4141.TF 226) &&
    Nat.beq (Y3.TF 3) (CFSG.KD.LQT.C4141.TF 247)) = true := by
  quickRfl

theorem lt4_ok : (Nat.beq (Y4.TF 0) (CFSG.KD.LQT.C4141.TF 197) &&
    Nat.beq (Y4.TF 1) (CFSG.KD.LQT.C4141.TF 207) && Nat.beq (Y4.TF 2) (CFSG.KD.LQT.C4141.TF 226) &&
    Nat.beq (Y4.TF 3) (CFSG.KD.LQT.C4141.TF 247)) = true := by
  quickRfl

end CFSG.KD.A312He

open CFSG.KC.E64F CFSG.KC.A312HeK CFSG.Quasithin.A312He CFSG.KD.A312He
open CFSG.QuasithinUnique.K1.SporadicPerm

#kc_each CFSG.KD.A312He ch4167w3_
  (fun c => chunkAll 8330 (fun p => Nat.beq (LF3 4 p) (wordF LAB (mw 3) p)) c) 0 9

#kc_each CFSG.KD.A312He ch4167w4_
  (fun c => chunkAll 8330 (fun p => Nat.beq (LF4 4 p) (wordF LAB (mw 4) p)) c) 0 9

#kc_each CFSG.KD.A312He ch4167i3_ (fun i => invChk LF3 8330 5 (i / 9) (i % 9)) 0 45

#kc_each CFSG.KD.A312He ch4167i4_ (fun i => invChk LF4 8330 5 (i / 9) (i % 9)) 0 45

#kc_each CFSG.KD.A312He ch4167i7_ (fun i => invChk LF7 8330 5 (i / 9) (i % 9)) 0 45

#kc_each CFSG.KD.A312He ch4167h3_ (fun k => hatPart LF3 8330 heB 5 (heHat3Xs.map qg) (qg heHat3T)
  heHat3Ws heHat3Pts heHat3W1 heHat3W2 heHat3V h3wit h3ex k) 0 11

#kc_each CFSG.KD.A312He ch4167h4_ (fun k => hatPart LF4 8330 heB 5 (heHat4Xs.map qg) (qg heHat4T)
  heHat4Ws heHat4Pts heHat4W1 heHat4W2 heHat4V h4wit h4ex k) 0 7

#kc_each CFSG.KD.A312He ch4167e7_ (fun k => extPart LF7 heB 5 (heExt7Xs.map qg) (qg heExt7T)
  heExt7Ws heExt7W heExt7Z e7sq e7C e7idx e7ex k) 0 8

end

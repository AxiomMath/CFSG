module

public import Certificates.Data.Kernel.Census.PackedRootR
public import Certificates.Data.Kernel.Census.PackedTree
public import Certificates.Kernel.Sporadic.Co2.ChainA
public import Certificates.Kernel.SporSch.Co2M.Words
import CFSG.Certificates.Kernel.Common.JsonGzC
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 1000000

open CFSG.KC.Census in
#kc_repo #kc_jsonc_gz CertificateChecks.KernelCensus.Co2R.Z
  "Certificates/Kernel/Census/Co2R/data/co2z.json.gz" 1057360 11961572167060610199 (r : RootR)

open CFSG.KC.Census in
#kc_repo #kc_jsonc_gz CertificateChecks.KernelCensus.Co2R.T
  "Certificates/Kernel/Census/Co2R/data/co2t.json.gz" 715865 2968051800055976139 (r : RootR)

open CFSG.KC.Census in
#kc_repo #kc_jsonc_gz CertificateChecks.KernelCensus.Co2R.U
  "Certificates/Kernel/Census/Co2R/data/co2u.json.gz" 218562 3886129654498415708 (r : RootR)

#kc_repo #kc_jsonc_gz CertificateChecks.KernelCensus.Co2R
  "Certificates/Kernel/Census/Co2R/data/co2li.json.gz" 91416 4520772252056854651 (li : Array Nat)

public section

namespace CertificateChecks.KernelCensus.Co2R

open CFSG.KC.Census CertificateChecks.KernelSporSch

@[expose] noncomputable def L (k : Nat) : Nat :=
  bif Nat.blt k 11 then CertificateChecks.KernelSpor.Co2A.S k else li[Nat.sub k 11]!

@[expose] def base : List Nat := [0, 1, 2, 3, 5, 4]

@[expose] noncomputable def pxs : List Nat :=
  [Co2M.WE 0, Co2M.WE 1, pc 2300 12 (Co2LS.S 8) (Co2LS.S 0)]

@[expose] noncomputable def inWP (m : Nat) (P : Nat) : Bool := Nat.beq P (pid m 5)

@[expose] noncomputable def cN (m : Nat) (r : RootR) : Array ArrCertP := pcN m 5 r.d.nodes

@[expose] noncomputable def nodeF (m : Nat) (r : RootR) (i : Nat) : Bool :=
  pnodeOKT m 5 r.ps (inWP m) r.d (cN m r) #[] i

@[expose] noncomputable def clsF (m : Nat) (r : RootR) : Bool :=
  Nat.beq r.mb.length r.d.nodes.size && Nat.beq r.mxb.length r.d.nodes.size &&
    (List.range r.d.nodes.size).all fun j =>
      Nat.beq r.d.nodes[j]!.basis.size 1 &&
      Nat.beq r.d.nodes[j]!.basis[0]! (ppcA m 5 r.d.xs (r.mb.getD j 0)) &&
      base.any (fun b => !(Nat.beq (pcwPt 12 L r.xw (r.mb.getD j 0) b) b)) &&
      base.all (fun b => Nat.beq (pcwPt 12 L r.xw (r.mxb.getD j 0) b)
        (pcwPt 12 L r.xw r.mx (pcwPt 12 L r.xw (r.mb.getD j 0) b)))

@[expose] def imFrom (r : RootR) (S c : Nat) : List Nat := r.d.im.filter fun x => Nat.ble (c * S) x

@[expose] noncomputable def invChunk (m : Nat) (r : RootR) (S c : Nat) : Bool :=
  pinvRest m 5 r.d.xs (c * S) (imFrom r S c) ((r.d.wt.drop (c * S)).take S) ==
    some (imFrom r S (c + 1))

@[expose] noncomputable def invHead (m : Nat) (r : RootR) : Bool :=
  Nat.beq r.d.im.length r.d.us.size &&
    (r.d.us.toList.zip r.d.im).all (fun ua => Nat.beq (ppcA m 5 r.d.xs ua.2) ua.1) &&
    Nat.beq r.d.wt.length (2 ^ r.d.xs.length) &&
    r.d.im.all (fun x => Nat.blt x (2 ^ r.d.xs.length))

@[expose] noncomputable def rootChunk (m : Nat) (r : RootR) (S c : Nat) : Bool :=
  (((r.d.us.toList.zip r.d.roots).drop (c * S)).take S).all fun ur =>
    prootOKC m 5 (r.d.nodes.map NodeP.basis) (cN m r) r.d.cs r.d.ci ur.1 ur.2

end CertificateChecks.KernelCensus.Co2R

end

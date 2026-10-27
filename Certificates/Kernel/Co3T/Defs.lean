module

public import Certificates.Kernel.Co3T.Data
public import Certificates.Kernel.Co3T.Text
public import Certificates.Kernel.Co3T.EnumC
public import Certificates.Kernel.Sporadic.Co3.C
public import Certificates.Data.Kernel.Co3TK
public import Certificates.Data.Kernel.Misc.ChainTail

public section

namespace CertificateChecks.KernelCo3T

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail CFSG.KC.B3S3K
open CFSG.KC.Co3TK CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T
open CertificateChecks.KernelSpor

@[expose] noncomputable def sAll (G : Nat) : Bool :=
  Nat.beq (Nat.shiftRight G (276 * 9)) 0 && allN 276 (fun t => Nat.blt (pg 9 (mask 9) G t) 276) &&
    siftK 276 9 (mask 9) (276 * 9) (pidn 276 9) Co3C.LR Co3C.TRI Co3C.BP 7 0 G

@[expose] noncomputable def hypK (j : Nat) : Bool :=
  (rebK 276 9 Co3C.LR Co3C.TR Co3C.TRI (fun l => (hypTuples[j]!)[l]!) 7).2.2 &&
    Nat.beq (rebK 276 9 Co3C.LR Co3C.TR Co3C.TRI (fun l => (hypTuples[j]!)[l]!) 7).1 (GJ j) &&
    permB 276 9 (GJ j) && sAll (GJ j) && allN 7 (fun l => coordK DE (GJ j) l (CK (7 * j + l)))

@[expose] noncomputable def trK (j : Nat) : Bool :=
  permB 276 9 (TT.L (24 + j)) && permB 276 9 (TT.L (12 + j)) && sAll (TT.L (24 + j)) &&
    (if transToD.getD j false then
      Nat.blt (TD j) 243 && Nat.beq (cj 276 9 (TT.L (24 + j)) (TT.L (12 + j))) (DE (TD j))
     else Nat.beq (cj 276 9 (TT.L (24 + j)) (TT.L (12 + j))) (TT.L 9) ||
       Nat.beq (cj 276 9 (TT.L (24 + j)) (TT.L (12 + j))) (cm 276 9 (TT.L 9) (TT.L 9)))

@[expose] noncomputable def EC.SK : List Nat := (List.range 4536).map EC.SKT

@[expose] noncomputable def tailP (k : Nat) : Bool :=
  ptailBranchK 276 9 Co3C.LR Co3C.TR Co3C.BP (TT.L 9) (pw 276 9 (TT.L 9)) yRels EC.N EC.T 7 k

@[expose] noncomputable def classB (lo : Nat) : Bool := allBlk lo (classK 4536 EC.T CW C2 C7) 504

end CertificateChecks.KernelCo3T

end

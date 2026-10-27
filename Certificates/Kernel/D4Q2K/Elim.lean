module

public import Certificates.Data.Kernel.D4Q2K.ElimDefs
public import Certificates.Kernel.D4Q2K.Data
public import Certificates.Kernel.D4Q2K.DataS
public import Certificates.Kernel.D4Q2K.DataT
public import Certificates.Kernel.D4Q2K.DataE
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4Q2K

open CFSG.KC.D4Q2K CFSG.KC.Enum

@[expose] noncomputable def rowVSl (s : Nat) : Bool :=
  allBlk (Nat.mul 64 s) (fun x => bIf(Nat.blt x 6720, rowV D.RF DS.SF D.MF DT.TF DE.NL x, true)) 64

@[expose] noncomputable def elimVSl (s : Nat) : Bool :=
  allBlk (Nat.mul 64 s) (fun x => bIf(Nat.blt x 6720, elimV DE.NL DE.RC DE.tr x, true)) 64

#kc_each CertificateChecks.KernelD4Q2K.rowVSl 0 105
#kc_each CertificateChecks.KernelD4Q2K.elimVSl 0 105

theorem elim_negRk : (!elimV DE.NL (fun x => Nat.shiftLeft (DE.RC x) 32) DE.tr 2240) = true := by
  quickRfl

theorem elim_negTr : (!elimV DE.NL DE.RC (Nat.shiftLeft DE.tr 32) 1) = true := by
  quickRfl

theorem row_negNb : (!rowV D.RF DS.SF D.MF DT.TF (fun x => Nat.xor (DE.NL x) 65536) 0) = true := by
  quickRfl

theorem row_negRow : (!rowV (fun i => D.RF (Nat.succ i)) DS.SF D.MF DT.TF DE.NL 0) = true := by
  quickRfl

end CertificateChecks.KernelD4Q2K

end

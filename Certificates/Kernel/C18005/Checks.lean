module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.C18005
public import CFSG.LocalAnalysis.SteinbergCCDempwolffModelCertificate18005Inputs
public meta import CFSG.LocalAnalysis.SteinbergCCDempwolffModelCertificate18005Inputs
public import CFSG.Certificates.Kernel.Common.EachTrue
public import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public meta import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public meta import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelC18005

open CFSG.LocalAnalysis.DempwolffFive

meta def baseArrs : Array (Array Nat) := rootPermArr.push negArr

meta def blkArrs : Array (Array Nat) :=
  Array.ofFn (n := 620) fun q => Array.ofFn (n := 240) fun i =>
    (blockPerm (q.1 / 31) ⟨q.1 % 31, Nat.mod_lt _ (by decide)⟩ i).1

meta def blkInvArrs : Array (Array Nat) :=
  Array.ofFn (n := 620) fun q => Array.ofFn (n := 240) fun i =>
    ((blockPerm (q.1 / 31) ⟨q.1 % 31, Nat.mod_lt _ (by decide)⟩).symm i).1

end CertificateChecks.KernelC18005

#kmisc_packarrs CertificateChecks.KernelC18005.GP CertificateChecks.KernelC18005.baseArrs 8

#kmisc_packarrs CertificateChecks.KernelC18005.B CertificateChecks.KernelC18005.blkArrs 8

#kmisc_packarrs CertificateChecks.KernelC18005.BI CertificateChecks.KernelC18005.blkInvArrs 8

#kc_each CertificateChecks.KernelC18005.ch18005b base
  (fun k => CFSG.KC.C18005.baseOK CertificateChecks.KernelC18005.GP
    (Bool.rec (motive := fun _ => Array Nat) CFSG.LocalAnalysis.DempwolffFive.negArr
      (CFSG.LocalAnalysis.DempwolffFive.rootPermArr.getD k #[]) (Nat.blt k 12)) k) 0 13

#kc_each CertificateChecks.KernelC18005.ch18005k blk
  (fun q => CFSG.KC.C18005.blkOK CertificateChecks.KernelC18005.GP CertificateChecks.KernelC18005.B
    CFSG.LocalAnalysis.DempwolffFive.blockWords q) 0 620

#kc_each CertificateChecks.KernelC18005.ch18005i inv
  (fun q => CFSG.KC.C18005.invOK CertificateChecks.KernelC18005.B CertificateChecks.KernelC18005.BI
    q) 0 620

#kc_each CertificateChecks.KernelC18005.ch18005w b
  (fun a => CFSG.KC.C18005.strictB (CertificateChecks.KernelC18005.GP 12) fun neg =>
    CFSG.KC.C18005.wordChk CertificateChecks.KernelC18005.B CertificateChecks.KernelC18005.BI
      neg (CFSG.KC.C18005.lettersB a)) 0 20

#kc_each CertificateChecks.KernelC18005.ch18005w c
  (fun q => CFSG.KC.C18005.strictB (CertificateChecks.KernelC18005.GP 12) fun neg =>
    CFSG.KC.C18005.chkC CertificateChecks.KernelC18005.B CertificateChecks.KernelC18005.BI neg q)
  0 400

#kc_each CertificateChecks.KernelC18005.ch18005w e
  (fun _ => CFSG.KC.C18005.strictB (CertificateChecks.KernelC18005.GP 12) fun neg =>
    CFSG.KC.C18005.wordOK CertificateChecks.KernelC18005.B CertificateChecks.KernelC18005.BI
      neg (CFSG.KC.C18005.lettersC 0 10) 16) 0 1

namespace CertificateChecks.KernelC18005

open CFSG.KC.C18005

#kc_forall_tree ch18005_base
  (fun k => baseOK GP (Bool.rec (motive := fun _ => Array Nat) CFSG.LocalAnalysis.DempwolffFive.negArr
    (CFSG.LocalAnalysis.DempwolffFive.rootPermArr.getD k #[]) (Nat.blt k 12)) k = true)
  13 CertificateChecks.KernelC18005.ch18005b.base

#kc_forall_tree ch18005_blk
  (fun q => blkOK GP B CFSG.LocalAnalysis.DempwolffFive.blockWords q = true)
  620 CertificateChecks.KernelC18005.ch18005k.blk

#kc_forall_tree ch18005_inv (fun q => invOK B BI q = true) 620
  CertificateChecks.KernelC18005.ch18005i.inv

#kc_forall_tree ch18005_wB
  (fun a => strictB (GP 12) (fun neg => wordChk B BI neg (lettersB a)) = true) 20
  CertificateChecks.KernelC18005.ch18005w.b

#kc_forall_tree ch18005_wC (fun q => strictB (GP 12) (fun neg => chkC B BI neg q) = true) 400
  CertificateChecks.KernelC18005.ch18005w.c

theorem ch18005_wE : strictB (GP 12) (fun neg => wordOK B BI neg (lettersC 0 10) 16) = true :=
  CertificateChecks.KernelC18005.ch18005w.e0

end CertificateChecks.KernelC18005

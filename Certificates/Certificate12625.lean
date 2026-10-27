module

public import CFSG.Sporadic.SmallOddCore.J3DataInputs
public meta import Certificates.Data.CFSGNative.SmallOddCore.Check
public meta import CFSG.Sporadic.SmallOddCore.CentData
public meta import Certificates.Data.CFSGNative.SporadicSchreier.Classes
import Certificates.Kernel.Sporadic.OddCore.J3Ord12625
import Certificates.Data.Kernel.Spor.Prim
import Certificates.Kernel.Sporadic.OddCore.CentGlue
import CFSG.Certificates.Kernel.BfsPinAlg

public section

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Schreier.Native

namespace Certificates

open CertificateChecks

@[expose] def j3OuterH (_ : Unit := ()) : Table := compT 6156 (j3CentTbl 22) (j3CentTbl 24)

end Certificates

end

namespace CertificateChecks.Batch12625

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.PkPow CFSG.KC.BfsPin CFSG.KS.MulH
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Schreier.Native CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore

theorem canons : canonK 6156 13 (mask 13) (6156 * 13) (J3CentP 22) = true ∧
    canonK 6156 13 (mask 13) (6156 * 13) (J3CentP 24) = true ∧
    canonK 6156 13 (mask 13) (6156 * 13) (pidn 6156 13) = true := by
  simpa only [bAnd_iff] using canon12625

theorem tbl_eq {k : Nat} (hk : k < 31) : j3CentTbl k = tabT (unpack 6156 13 (J3CentP k)) := by
  rw [← j3CentTbl_eq hk, tabT_natArr]

theorem h_eq : Certificates.j3OuterH () = tabT (unpack 6156 13 H12625) := by
  rw [Certificates.j3OuterH, tbl_eq (by norm_num), tbl_eq (by norm_num),
    compT_unpack canons.1 canons.2.1]
  rfl

theorem strictN_id (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem pows : Pows 6156 13 H12625 (ppw 6156 13 H12625) :=
  ⟨rfl, fun e => strictN_id (ppw 6156 13 H12625 e) (fun q => pcomp 6156 13 (mask 13) H12625 q)⟩

theorem id_eq : idT 6156 = tabT (unpack 6156 13 (pidn 6156 13)) := by
  rw [idT_tabT, idA_eq sz12625]

theorem hc : canonK 6156 13 (mask 13) (6156 * 13) H12625 = true :=
  canonK_pcomp canons.1 canons.2.1

theorem tblEq_pow (e : Nat) :
    tblEq 6156 (powT 6156 e (Certificates.j3OuterH ())) (idT 6156) =
      Nat.beq (ppw 6156 13 H12625 e) (pidn 6156 13) := by
  rw [h_eq, powT_unpack pows id_eq canons.2.2 hc, id_eq,
    tblEq_unpack (pows_canon pows canons.2.2 hc e) canons.2.2]

theorem not_of_bIf {c : Bool} (h : bIf(c, false, true) = true) : c = false := by
  cases c
  · rfl
  · exact absurd h Bool.false_ne_true

end CertificateChecks.Batch12625

public section

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Schreier.Native
open CertificateChecks

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Schreier.Native in
theorem certificate12625 :
    tblEq 6156 (powT 6156 9 (j3OuterH ())) (idT 6156) = true ∧
      tblEq 6156 (powT 6156 3 (j3OuterH ())) (idT 6156) = false := by
  refine ⟨?_, ?_⟩
  · rw [CertificateChecks.Batch12625.tblEq_pow]
    exact KernelSpor.OddCore.pow9_12625
  · rw [CertificateChecks.Batch12625.tblEq_pow]
    exact CertificateChecks.Batch12625.not_of_bIf KernelSpor.OddCore.pow3_12625

end Certificates

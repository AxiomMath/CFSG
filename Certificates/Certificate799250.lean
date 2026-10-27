module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KJ3CycInputs
public meta import CFSG.RankThree.PartTwo.Sec21.Hering214KJ3CycInputs
import Certificates.Kernel.Sporadic.OddCore.C799250
import Certificates.Kernel.Sporadic.OddCore.J3PGGlue

namespace CertificateChecks.Batch799250

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.PkPow CFSG.KC.BfsPin CFSG.KS.MulH
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore
open CertificateChecks.KernelSpor.OddCore.J3W CFSG.RankThree.PartTwo.Sec21.Hering214

theorem letters : ∀ l ∈ j3NineWord, l < 2 := by decide

theorem c_eq : j3NineTbl () = tabT (unpack 6156 13 C799250) ∧
    canonK 6156 13 (mask 13) (6156 * 13) C799250 = true := by
  rw [j3NineTbl, idT_eq]
  refine foldl_pg j3NineWord _ cn.2.2.2.2 fun l hl => ⟨pg_eq (letters l hl), ?_⟩
  have hl2 := letters l hl
  rcases l with _ | _ | l
  · exact cn.2.2.1
  · exact cn.2.2.2.1
  · omega

theorem divParts9 : CFSG.Sporadic.Schreier.Native.divParts 9 = [3, 1] := by decide

theorem holds : j3NineOK = true := by
  have h := k799250
  simp only [bAnd_iff] at h
  obtain ⟨hinv, hcomm, h9, h3, h1⟩ := h
  have h3' : Nat.beq (ppw 6156 13 C799250 3) (pidn 6156 13) = false := not_of_bIf h3
  have h1' : Nat.beq (ppw 6156 13 C799250 1) (pidn 6156 13) = false := not_of_bIf h1
  have hidA : CFSG.Monster.B.Co2.Native.idA 6156 = unpack 6156 13 (pidn 6156 13) := idA_eq cn.1
  simp only [j3NineOK]
  rw [perm_t, c_eq.1, permOK_unpack c_eq.2 hinv, t_eq, commTT_unpack c_eq.2 cn.2.1, hcomm,
    ordTest_unpack (pows _) hidA cn.2.2.2.2 c_eq.2, divParts9, h9]
  simp only [List.all_cons, List.all_nil, h3', h1']
  rfl

end CertificateChecks.Batch799250

public section

namespace Certificates

open CertificateChecks

theorem certificate799250 : CFSG.RankThree.PartTwo.Sec21.Hering214.j3NineOK = true := CertificateChecks.Batch799250.holds

end Certificates

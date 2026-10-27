module

public import Certificates.Data.J3RealB
import Certificates.Kernel.J3RealB.Checks
import Certificates.Kernel.SporSch.J3K426.Glue
import Certificates.Kernel.SporSch.PairJ3.Check2237
import CFSG.Certificates.Kernel.HeGlueKGlue

set_option maxRecDepth 100000

namespace CertificateChecks.KernelJ3RealB

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Sporadic.Schreier
open CertificateChecks.KernelSporSch

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem ppS {j : Nat} (hj : j < 5) : PP 6156 13 (PJ3.S j) :=
  CFSG.KC.HeGlueK.PP_of_permOK2 J3KT.szOK' (CFSG.KS.Raw.Orb.allN_iff.1 PJ3Check.perm j hj)

theorem word_eq : ∀ wd : List Nat, (∀ j ∈ wd, j < 5) →
    j3WordArr wd = unpack 6156 13 (rbW wd) ∧ PP 6156 13 (rbW wd)
  | [], _ => ⟨idA_eq J3KT.szOK', PP.id J3KT.szOK'⟩
  | j :: rest, h => by
    obtain ⟨ih1, ih2⟩ := word_eq rest (fun j' hj' => h j' (List.mem_cons_of_mem j hj'))
    have hj := h j List.mem_cons_self
    have e1 : rbW (j :: rest) = pcomp 6156 13 (mask 13) (PJ3.S j) (rbW rest) := strictN_eq _ _
    have e2 : j3WordArr (j :: rest) = compA 6156 j3StrongArrs[j]! (j3WordArr rest) := rfl
    rw [e1, e2, ih1, PJ3Check.arr_eq j hj, compA_PP (ppS hj) ih2]
    exact ⟨rfl, (ppS hj).mul ih2⟩

end CertificateChecks.KernelJ3RealB

public section

namespace Certificates

open CFSG.KC.BfsPin CFSG.RankThree.PartTwo.KFacts.K426 CertificateChecks.KernelSporSch
  CertificateChecks.KernelJ3RealB

open CFSG.RankThree.PartTwo.KFacts.K426 in
theorem certificate10131 : j3RealBOK () = true := by
  have hl : ∀ j ∈ j3RealBWord, j < 5 := by decide
  obtain ⟨hw, hp⟩ := word_eq j3RealBWord hl
  have h2 : (j3RealBWord.all fun l => decide (l < 2)) = true := by decide
  have hc := rb_ok
  rw [rbChk, strictB_eq, rbTest] at hc
  have px := J3KT.ppX1
  simp only [j3RealBOK, h2, Bool.true_and]
  rw [hw, J3KT.hX1, compA_PP hp px, compA_PP px px, compA_PP (px.mul px) hp,
    eqA_PP (hp.mul px) ((px.mul px).mul hp)]
  exact hc

end Certificates

module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.ExtendData
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.WordTreeFact
import Certificates.Kernel.PresLetters.F134002
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import CFSG.Foundations.Basic
public import Certificates.Data.Kernel.Bounds.TableFact
public import Mathlib

public section

open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation CFSG.KC.MiscCoset CFSG.Certificates
  CFSG.CosetTable

namespace CertificateChecks.PresLetters134002

#kc_forall_chunks leaf (fun i => KB.TableFact 4
  ((((extendTree.collapses extendRels).getD i []).map FreeGroup.toWord).map encW)
  (([0, 1, 2] : List (Fin 4)).map fun x => [(x.val, true)]) 1) 41 CFSG.KBFact.F134002t 1

theorem length_collapses : (extendTree.collapses extendRels).length = 41 := by decide +kernel

theorem succOk : extendTree.succOk 3 extendRels = true := by decide +kernel

theorem succs : ∀ t ∈ extendTree.succs, t ∈ extendSucc := by
  simp [extendTree, Tree.succs, extendSucc]

end CertificateChecks.PresLetters134002

namespace Certificates

open CertificateChecks.PresLetters134002 in
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation in
theorem certificate134002 :
    extendTree.okF [0, 1, 2] 3 extendRels
    ∧ (∀ t ∈ extendTree.succs, t ∈ extendSucc) :=
  ⟨Tree.okF_of [0, 1, 2] 3 extendTree extendRels succOk fun rs hrs => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrs
      have h := TableFact.genSub_index _ (by norm_num) [0, 1, 2]
        (leaf i (hi.trans_eq length_collapses))
      rw [List.getD_eq_getElem _ _ hi] at h
      exact h, succs⟩

end Certificates

module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StarData
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.WordTreeFact
import Certificates.Kernel.PresLetters.F134001
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import CFSG.Foundations.Basic
public import Certificates.Data.Kernel.Bounds.TableFact
public import Mathlib

public section

open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation CFSG.KC.MiscCoset CFSG.Certificates
  CFSG.CosetTable

namespace CertificateChecks.PresLetters134001

#kc_forall_chunks leaf (fun i => KB.TableFact 4
  ((((starTree.collapses starRels).getD i []).map FreeGroup.toWord).map encW)
  (([0, 1, 2] : List (Fin 4)).map fun x => [(x.val, true)]) 1) 55 CFSG.KBFact.F134001t 1

theorem length_collapses : (starTree.collapses starRels).length = 55 := by decide +kernel

theorem succOk : starTree.succOk 3 starRels = true := by decide +kernel

theorem succs : ∀ t ∈ starTree.succs, t = ⟨(2, true), 1⟩ := by
  simp [starTree, Tree.succs]

end CertificateChecks.PresLetters134001

namespace Certificates

open CertificateChecks.PresLetters134001 in
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation in
theorem certificate134001 :
    starTree.okF [0, 1, 2] 3 starRels
    ∧ (∀ t ∈ starTree.succs, t = ⟨(2, true), 1⟩) :=
  ⟨Tree.okF_of [0, 1, 2] 3 starTree starRels succOk fun rs hrs => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrs
      have h := TableFact.genSub_index _ (by norm_num) [0, 1, 2]
        (leaf i (hi.trans_eq length_collapses))
      rw [List.getD_eq_getElem _ _ hi] at h
      exact h, succs⟩

end Certificates

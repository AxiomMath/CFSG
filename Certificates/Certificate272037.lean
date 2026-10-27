module

public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.Model
public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.W4Presentation
import Certificates.Kernel.PresLetters.F272037A
import Certificates.Kernel.W4Model.Fact
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import CFSG.Sporadic.J3
public import Certificates.Data.Kernel.Bounds.TableFact
import CFSG.Certificates.CosetTableShort
import CFSG.Certificates.NativeSchreierCard
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.Open.Defs

public section

open CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition CFSG.CosetTable
  CFSG.KC.MiscCoset CFSG.Certificates

namespace CertificateChecks.PresLetters272037

#kc_forall_chunks coll (fun k => KB.TableFact 7
  ((j3WordsRest ++ [collapseRels.getD k []]).map encW)
  ((subsetOf 7 [0, 1, 2, 3, 4, 5]).map fun x => [(x.val, true)]) 1) 13 CFSG.KBFact.PL272037c 1

theorem collapse : ∀ r ∈ collapseRels,
    genSub {s : FreeGroup (Fin 7) | s ∈ (j3WordsRest ++ [r]).map FreeGroup.mk}
      (subsetOf 7 [0, 1, 2, 3, 4, 5]) = ⊤ := by
  intro r hr
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hr
  have hl : collapseRels.length = 13 := by decide
  have h := coll k (lt_of_lt_of_eq hk hl)
  rw [List.getD_eq_getElem _ _ hk] at h
  obtain ⟨hfi, hidx⟩ := TableFact.genSub_index _ (by norm_num) _ h
  exact Subgroup.index_eq_one.1 (le_antisymm hidx (Nat.one_le_iff_ne_zero.2 hfi.index_ne_zero))

end CertificateChecks.PresLetters272037

namespace Certificates

open CertificateChecks

open CFSG.CosetTable CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition in
theorem certificate272037 :
    (Finite (PG 7 j3WordsW) ∧ Nat.card (PG 7 j3WordsW) ≤ 78489 * 1920) ∧
    (∀ r ∈ collapseRels, genSub {s : FreeGroup (Fin 7) | s ∈ (j3WordsRest ++ [r]).map FreeGroup.mk}
      (subsetOf 7 [0, 1, 2, 3, 4, 5]) = ⊤) ∧
    (Finite (PG 7 j2Words) ∧ Nat.card (PG 7 j2Words) ≤ 315 * 1920) ∧
    FreeGroup.lift uJ (FreeGroup.mk (wRel 4 1)) = 1 :=
  ⟨TableFact.card_restrict j3WordsW (by norm_num) (subsetOf 7 [0, 1, 2, 3, 4, 5]) (by decide)
      CFSG.KBFact.PL272037a CFSG.KBFact.PL272037b,
    PresLetters272037.collapse,
    TableFact.card_restrict j2Words (by norm_num) (subsetOf 7 [0, 1, 2, 3, 4, 5]) (by decide)
      CFSG.KBFact.PL272037d CFSG.KBFact.PL272037e,
    KernelW4Model.w4_eq_one⟩

end Certificates

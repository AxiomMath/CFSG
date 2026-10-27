module

public import Certificates.Data.G23RecogTriInputs
import Certificates.Kernel.PresLetters.F320013A
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import Certificates.Data.Kernel.Bounds.TableFact

public section

open CFSG.GH74.QTGen4.Recog.G23.P7 CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Certificates

namespace CertificateChecks.PresLetters320013

def nonModel : List (Fin 6 × Fin 6) :=
  ((List.finRange 6).flatMap fun a => (List.finRange 6).map fun b => (a, b)).filter
    fun p => !(modelPairs.contains p)

def pairAt (i : ℕ) : Fin 6 × Fin 6 := nonModel.getD i (0, 0)

#kc_forall_chunks idx (fun i => KB.TableFact 6 ((cfgWords (pairAt i).1 (pairAt i).2).map encW)
  ((subsetOf 6 [0, 1, 2, 3]).map fun x => [(x.val, true)]) 1) 32 CFSG.KBFact.F320013c 1

#kc_forall_chunks res (fun i => KB.TableFact (subsetOf 6 [0, 1, 2, 3]).length
  ((restrictWords (subsetOf 6 [0, 1, 2, 3]) (cfgWords (pairAt i).1 (pairAt i).2)).map encW) [] 288)
  32 CFSG.KBFact.F320013d 1

theorem nonModel_length : nonModel.length = 32 := by decide

theorem mem_nonModel (k₁ k₂ : Fin 6) (h : (k₁, k₂) ∉ modelPairs) : (k₁, k₂) ∈ nonModel := by
  revert k₁ k₂; decide

end CertificateChecks.PresLetters320013

namespace Certificates

open CertificateChecks.PresLetters320013 in
open CFSG.GH74.QTGen4.Recog.G23.P7 CFSG.CosetTable in
theorem certificate320013 : ((genSub {r : FreeGroup (Fin 6) | r ∈ triWords.map FreeGroup.mk}
        (subsetOf 6 [0, 1, 2, 3])).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 6) | r ∈ triWords.map FreeGroup.mk}
        (subsetOf 6 [0, 1, 2, 3])).index ≤ 14742)
    ∧ (Finite (PG (subsetOf 6 [0, 1, 2, 3]).length (restrictWords (subsetOf 6 [0, 1, 2, 3]) triWords)) ∧
      Nat.card (PG (subsetOf 6 [0, 1, 2, 3]).length
        (restrictWords (subsetOf 6 [0, 1, 2, 3]) triWords)) ≤ 288)
    ∧ (∀ k₁ k₂ : Fin 6, (k₁, k₂) ∈ modelPairs ∨
      (Finite (PG 6 (cfgWords k₁ k₂)) ∧ Nat.card (PG 6 (cfgWords k₁ k₂)) ≤ 288)) := by
  refine ⟨TableFact.genSub_index triWords (by norm_num) (subsetOf 6 [0, 1, 2, 3])
      CFSG.KBFact.F320013a,
    TableFact.card (restrictWords (subsetOf 6 [0, 1, 2, 3]) triWords) (by decide)
      CFSG.KBFact.F320013b, ?_⟩
  · intro k₁ k₂
    by_cases hm : (k₁, k₂) ∈ modelPairs
    · exact Or.inl hm
    · right
      obtain ⟨i, hi, he⟩ := List.getElem_of_mem (mem_nonModel k₁ k₂ hm)
      have hp : pairAt i = (k₁, k₂) := by rw [pairAt, List.getD_eq_getElem _ _ hi, he]
      have hi' : i < 32 := hi.trans_eq nonModel_length
      have h := TableFact.card_restrict (cfgWords (pairAt i).1 (pairAt i).2) (by norm_num)
        (subsetOf 6 [0, 1, 2, 3]) (by decide) (idx i hi') (res i hi')
      rw [hp] at h
      exact ⟨h.1, h.2.trans (by norm_num)⟩

end Certificates

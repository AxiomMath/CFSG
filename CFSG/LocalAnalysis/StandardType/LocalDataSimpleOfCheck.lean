module

public import CFSG.LocalAnalysis.StandardType.LocalDataOfCheck
public import CFSG.LocalAnalysis.StandardType.LocalDataSimple

public section

namespace CFSG.StandardType.LocalDataSimpleOfCheck

open CFSG.AGLEmbedding.MaxD2 (Gsub Rsub)
open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native
open Certificates.MaxD2Perm (Data check)

theorem isSimpleGroup_of_check_conj {D : Data} {S : List (Equiv.Perm (Fin D.n))}
    (hp : D.p.Prime) (hm : 1 < D.tm) (hlam : D.tlam = 2)
    (hS : ∀ j, TabRep (D.gT.getD j (idTab D.n)) (S.getD j 1)) (hlen : S.length = D.gT.size)
    (hcard : Nat.card (Gsub S) = D.gOrder)
    (hsolv : ∃ a b : ℕ, D.nOrder = D.p ^ 2 * (2 ^ a * 3 ^ b)) (h : check D = true)
    (hconj : ∀ s ∈ S, ∃ g ∈ Gsub S, ∃ r ∈ Rsub D S, s = g * r * g⁻¹) :
    IsSimpleGroup ↥(Gsub S) ∧ commutator ↥(Gsub S) = ⊤ := by
  obtain ⟨hloc, hnn⟩ := CFSG.StandardType.LocalDataOfCheck.localData_rsub_of_check hp hS hlen hcard
    hsolv h
  rw [hlam] at hloc
  refine CFSG.StandardType.LocalDataSimple.isSimpleGroup_of_localData hp hm hloc hnn ?_
  refine (Subgroup.closure_le _).2 ?_
  intro s hs
  obtain ⟨g, hg, r, hr, rfl⟩ := hconj s hs
  exact Subgroup.subset_closure ⟨g, hg, r, hr, rfl⟩

end CFSG.StandardType.LocalDataSimpleOfCheck

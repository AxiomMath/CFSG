module

public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Bridge.TwoGen
public import CFSG.Sporadic.Presentation.M23
public import Certificates.Data.CFSGNative.Bridge.SurjA
public meta import Certificates.Data.CFSGNative.Bridge.SurjA
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Certificate9121
public import CFSG.Sporadic.Bridge.M23SurjInputs
public import Certificates.Certificate9214
public import Certificates.Certificate2197
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Sporadic.M23.M23Group

public section

namespace CFSG.Sporadic.Bridge.M23

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Bridge.TwoGen.Native TauCeti
open CFSG.Sporadic.Schreier (m23GenA m23GenB m23_eq_closure m23_card)
open CFSG.Sporadic.Mathieu (closure_pair_eq_top)

private theorem presentation_eq : SporadicName.M23.presentation = Sporadic.m23Presentation := rfl

theorem generatorCount_eq : Sporadic.m23Presentation.generatorCount = 2 := by
  simp [GroupPresentation.generatorCount]

theorem rep_a : CFSG.Sporadic.Th.Rep 23 tabA m23GenA := by
  unfold CFSG.Sporadic.Th.Rep
  decide

theorem rep_a_inv : CFSG.Sporadic.Th.Rep 23 tabA (m23GenA⁻¹) := by
  unfold CFSG.Sporadic.Th.Rep
  decide

theorem rep_b : CFSG.Sporadic.Th.Rep 23 tabB m23GenB := by
  unfold CFSG.Sporadic.Th.Rep
  decide

theorem rep_b_inv : CFSG.Sporadic.Th.Rep 23 tabBi (m23GenB⁻¹) := by
  unfold CFSG.Sporadic.Th.Rep
  decide

theorem rel_check :
    relCheck 23 tabA tabA tabBi tabB Sporadic.m23Presentation.relatorLetters =
    true := by
  exact Certificates.certificate9214

theorem relators_eval :
    ∀ v ∈ Sporadic.m23Presentation.relatorLetters,
    wordProd (img2 m23GenA m23GenB⁻¹) v = 1 :=
  wordProd_eq_one_of_relCheck (n := 23) (by norm_num) rep_a rep_a_inv rep_b_inv
    (by rw [inv_inv]; exact rep_b) rel_check

theorem closure_gen :
    Subgroup.closure ({m23GenA, m23GenB⁻¹} : Set Blueprint.NativeSporadic.M23) = ⊤ := by
  have h : Subgroup.closure ({m23GenA, m23GenB} : Set Blueprint.NativeSporadic.M23) = ⊤ :=
    closure_pair_eq_top m23_eq_closure _ _
  rw [eq_top_iff, ← h, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · have hb : m23GenB⁻¹ ∈
        Subgroup.closure ({m23GenA, m23GenB⁻¹} : Set Blueprint.NativeSporadic.M23) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    simpa using Subgroup.inv_mem _ hb

theorem nonempty_mulEquiv_of_card_le
    (hfin : Finite SporadicName.M23.Group)
    (hcard : Nat.card SporadicName.M23.Group ≤ 10200960) :
    Nonempty (Blueprint.NativeSporadic.M23 ≃* SporadicName.M23.Group) := by
  revert hfin hcard
  show Finite SporadicName.M23.presentation.Group →
    Nat.card SporadicName.M23.presentation.Group ≤ 10200960 →
    Nonempty (Blueprint.NativeSporadic.M23 ≃* SporadicName.M23.presentation.Group)
  rw [presentation_eq]
  intro hfin hcard
  exact nonempty_mulEquiv_of_closure Sporadic.m23Presentation generatorCount_eq closure_gen
    relators_eval hcard (le_of_eq m23_card.symm)

theorem nonempty_mulEquiv :
    Nonempty (Blueprint.NativeSporadic.M23 ≃* SporadicName.M23.Group) :=
  nonempty_mulEquiv_of_card_le Presentation.M23.finite_card_le.1
    Presentation.M23.finite_card_le.2

end CFSG.Sporadic.Bridge.M23

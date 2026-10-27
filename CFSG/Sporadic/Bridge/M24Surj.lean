module

public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Presentation.M24Exact
public import CFSG.Sporadic.Bridge.TwoGen
public import Certificates.Data.CFSGNative.Bridge.SurjA
public meta import Certificates.Data.CFSGNative.Bridge.SurjA
public meta import Certificates.Data.CFSGNative.Mathieu.M24
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Certificate9123
public import CFSG.Sporadic.Bridge.M24SurjInputs
public import Certificates.Certificate9215
public import Certificates.Certificate3017
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Sporadic.Presentation.Common

public section

namespace CFSG.Sporadic.Bridge.M24

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Bridge.TwoGen.Native TauCeti
open CFSG.Sporadic.Mathieu (m24a m24b rep_m24a rep_m24b m24_eq card_M24 closure_pair_eq_top)
open CFSG.Sporadic.Mathieu.Native (m24Data)

private theorem presentation_eq : SporadicName.M24.presentation = Sporadic.m24Presentation := rfl

theorem generatorCount_eq : Sporadic.m24Presentation.generatorCount = 2 := by
  simp [GroupPresentation.generatorCount]

theorem rep_a_inv : CFSG.Sporadic.Th.Rep 24 m24Data.tA (m24a⁻¹) := by
  unfold CFSG.Sporadic.Th.Rep
  decide

theorem rep_b_inv : CFSG.Sporadic.Th.Rep 24 tabBi (m24b⁻¹) := by
  unfold CFSG.Sporadic.Th.Rep
  decide

theorem rel_check :
    relCheck 24 m24Data.tA m24Data.tA tabBi m24Data.tB
    Sporadic.m24Presentation.relatorLetters = true := by
  exact Certificates.certificate9215

theorem relators_eval :
    ∀ v ∈ Sporadic.m24Presentation.relatorLetters,
    wordProd (img2 m24a m24b⁻¹) v = 1 :=
  wordProd_eq_one_of_relCheck (n := 24) (by norm_num) rep_m24a rep_a_inv rep_b_inv
    (by rw [inv_inv]; exact rep_m24b) rel_check

theorem closure_gen : Subgroup.closure ({m24a, m24b⁻¹} : Set Blueprint.NativeSporadic.M24) = ⊤ := by
  have h : Subgroup.closure ({m24a, m24b} : Set Blueprint.NativeSporadic.M24) = ⊤ :=
    closure_pair_eq_top m24_eq _ _
  rw [eq_top_iff, ← h, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · have hb : m24b⁻¹ ∈ Subgroup.closure ({m24a, m24b⁻¹} : Set Blueprint.NativeSporadic.M24) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    simpa using Subgroup.inv_mem _ hb

theorem nonempty_mulEquiv_of_card_le
    (hfin : Finite SporadicName.M24.Group)
    (hcard : Nat.card SporadicName.M24.Group ≤ 244823040) :
    Nonempty (Blueprint.NativeSporadic.M24 ≃* SporadicName.M24.Group) := by
  revert hfin hcard
  show Finite SporadicName.M24.presentation.Group →
    Nat.card SporadicName.M24.presentation.Group ≤ 244823040 →
    Nonempty (Blueprint.NativeSporadic.M24 ≃* SporadicName.M24.presentation.Group)
  rw [presentation_eq]
  intro hfin hcard
  exact nonempty_mulEquiv_of_closure Sporadic.m24Presentation generatorCount_eq closure_gen
    relators_eval hcard (le_of_eq card_M24.symm)

theorem nonempty_mulEquiv :
    Nonempty (Blueprint.NativeSporadic.M24 ≃* SporadicName.M24.Group) :=
  nonempty_mulEquiv_of_card_le Presentation.M24.finite_card_le.1
    Presentation.M24.finite_card_le.2

end CFSG.Sporadic.Bridge.M24

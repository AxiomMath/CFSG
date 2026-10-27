module

public import CFSG.RankThree.PartTwo.Census.Exceptional.E6E7
public import CFSG.RankThree.PartTwo.Census.Exceptional.TwistedE6
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6
  CFSG.TauCetiBridge.Minuscule CFSG.RankThree.CentralCover TauCeti
  CFSG.RankThree.PartTwo.Census.Exceptional
open scoped MatrixGroups

theorem exists_four_commuting_SL2_e6Index
    (d : TypeE6LieIndex) :
    ∃ φ : Fin 4 → SL(2, d.1.fixedField) →* FixedPointCandidate d.steinberg,
      (∀ i, Function.Injective (φ i)) ∧
        ∀ i j, i ≠ j → ∀ A B, φ i A * φ j B = φ j B * φ i A := by
  have hC : commutator ↥(e6Data_valid.minGroup d.1.fixedField) = ⊤ :=
    (CFSG.LieType.CurtisTits.isQuasisimple_e6 d.1.fixedField).1.commutator_eq_top
  have : Fintype d.1.fixedField := Fintype.ofFinite _
  obtain ⟨ρ, hinj, hcomm, hcen⟩ := exists_commuting_minuscule_SL2 e6Data_valid d.1.fixedField
    neighbour_cartan_E6 ![![1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1],
      ![1, 2, 2, 3, 2, 1]] (by decide +kernel)
  refine ⟨fun i => (toQuot (e6Embed d) hC).comp (ρ i),
    fun i => toQuot_comp_injective (e6Embed_injective d) hC (ρ i) (hcen i), fun i j hij A B => ?_⟩
  simp only [MonoidHom.comp_apply, ← map_mul, hcomm i j hij A B]

theorem exists_four_commuting_SL2_E6
    (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q.card ∧
      ∃ φ : Fin 4 → SL(2, K) →* (CFSGIndex.lie ⟨.E6 q, hv⟩).Group,
        (∀ i, Function.Injective (φ i)) ∧
          ∀ i j, i ≠ j → ∀ A B, φ i A * φ j B = φ j B * φ i A := by
  obtain ⟨φ, hφ1, hφ2⟩ := exists_four_commuting_SL2_e6Index
    (⟨⟨.E6 q, hv⟩, (LieTypeIndex.isTypeE6_iff _).2 trivial⟩ : TypeE6LieIndex)
  have hfin : ∀ d : ValidLieTypeIndex, Finite d.fixedField := fun d => inferInstance
  refine ⟨ValidLieTypeIndex.fixedField (⟨.E6 q, hv⟩ : ValidLieTypeIndex), inferInstance,
    hfin _, ?_, φ, hφ1, hφ2⟩
  rw [ValidLieTypeIndex.card_fixedField]
  exact LieTypeIndex.fieldOrder_E6 q

theorem exists_four_commuting_SL2_te6Index
    (d : TypeTwistedE6LieIndex) :
    ∃ φ : Fin 4 → SL(2, d.1.fixedField) →* FixedPointCandidate d.steinberg,
      (∀ i, Function.Injective (φ i)) ∧
        ∀ i j, i ≠ j → ∀ A B, φ i A * φ j B = φ j B * φ i A := by
  have hC := commutator_fixedGroup_quadField d
  have hj : ∀ x, quadFrob d (quadIncl d x) = quadIncl d x := quadFrob_quadIncl d
  refine ⟨fun i => (toQuot (te6Embed d) hC).comp (te6SL2 (quadFrob d) (quadIncl d) hj i),
    fun i => toQuot_comp_injective (te6Embed_injective d) hC _ fun A hA =>
      te6SL2_central (quadFrob d) (quadIncl d) hj i hA, fun i i' hii A B => ?_⟩
  simp only [MonoidHom.comp_apply, ← map_mul,
    te6SL2_commute (quadFrob d) (quadIncl d) hj hii A B]

theorem exists_four_commuting_SL2_twistedE6
    (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q.card ∧
      ∃ φ : Fin 4 → SL(2, K) →* (CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group,
        (∀ i, Function.Injective (φ i)) ∧
          ∀ i j, i ≠ j → ∀ A B, φ i A * φ j B = φ j B * φ i A := by
  obtain ⟨φ, hφ1, hφ2⟩ := exists_four_commuting_SL2_te6Index
    (⟨⟨.twistedE6 q, hv⟩, (LieTypeIndex.isTypeTwistedE6_iff _).2 trivial⟩ :
      TypeTwistedE6LieIndex)
  have hfin : ∀ d : ValidLieTypeIndex, Finite d.fixedField := fun d => inferInstance
  refine ⟨ValidLieTypeIndex.fixedField (⟨.twistedE6 q, hv⟩ : ValidLieTypeIndex), inferInstance,
    hfin _, ?_, φ, hφ1, hφ2⟩
  rw [ValidLieTypeIndex.card_fixedField]
  exact LieTypeIndex.fieldOrder_twistedE6 q

end CFSG.RankThree.PartOne.KFU

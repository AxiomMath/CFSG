module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Sporadic.Recognition.HeMultiplierTables

public section

namespace CFSG.Sporadic.Recognition.HeMultiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Open CFSG.Sporadic.He

theorem isPresentation_heGen_of_bound (hTab : heTabCheck = true)
    (hP : Finite (PG 4 heRels) ∧ Nat.card (PG 4 heRels) ≤ 4030387200) :
    IsPresentation heGen (wordSet heRels) := by
  obtain ⟨hfin, hle⟩ := hP
  have : Finite (PresentedGroup (wordSet heRels)) := hfin
  exact IsPresentation.of_card_le (lift_heGen_rels hTab) (closure_heGen hTab)
    (by rw [card_J]; exact hle)

theorem presentedCover_card_le_of_bound
    (hC : Finite (PG 4 heCover) ∧ Nat.card (PG 4 heCover) ≤ 4030387200) :
    Finite (PresentedCover (wordSet heRels) fun i => FreeGroup.mk (heCommWord i)) ∧
      Nat.card (PresentedCover (wordSet heRels) fun i => FreeGroup.mk (heCommWord i)) ≤
        4030387200 := by
  change Finite (PresentedGroup (coverRelators (wordSet heRels)
      fun i => FreeGroup.mk (heCommWord i))) ∧
    Nat.card (PresentedGroup (coverRelators (wordSet heRels)
      fun i => FreeGroup.mk (heCommWord i))) ≤ 4030387200
  rw [coverRelators_wordSet]
  exact hC

theorem card_griessHopfMultiplier_of_mulEquiv_of_bounds
    {Y : Type} [Group Y] (e : Y ≃* J) (hTab : heTabCheck = true)
    (hP : Finite (PG 4 heRels) ∧ Nat.card (PG 4 heRels) ≤ 4030387200)
    (hC : Finite (PG 4 heCover) ∧ Nat.card (PG 4 heCover) ≤ 4030387200) :
    Nat.card (griessHopfMultiplier Y) = 1 := by
  have hPres : IsPresentation (fun i => e.symm (heGen i)) (wordSet heRels) :=
    (isPresentation_heGen_of_bound hTab hP).mulEquiv e.symm
  have hw : ∀ i, FreeGroup.mk (heCommWord i) ∈ commutator (FreeGroup (Fin 4)) :=
    fun i => mk_commWords_mem_commutator _
  have hwg : ∀ i, FreeGroup.lift (fun i => e.symm (heGen i))
      (FreeGroup.mk (heCommWord i)) = e.symm (heGen i) := fun i => by
    rw [lift_mulEquiv, lift_heCommWord hTab]
  obtain ⟨hfin, hle⟩ := presentedCover_card_le_of_bound hC
  have hc := card_presentedCover hPres hw hwg
  rw [Nat.card_congr e.toEquiv, card_J] at hc
  have hpos : 0 < Nat.card (PresentedCover (wordSet heRels) fun i => FreeGroup.mk (heCommWord i)) :=
    Nat.card_pos
  rw [hc] at hpos hle
  have h1 : 0 < Nat.card (griessHopfMultiplier Y) := Nat.pos_of_mul_pos_left hpos
  have h2 : Nat.card (griessHopfMultiplier Y) ≤ 1 := by
    by_contra hcon
    have : 4030387200 * 2 ≤ 4030387200 * Nat.card (griessHopfMultiplier Y) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  omega

theorem card_griessHopfMultiplier_He_of_bounds
    (hTab : heTabCheck = true)
    (hP : Finite (PG 4 heRels) ∧ Nat.card (PG 4 heRels) ≤ 4030387200)
    (hC : Finite (PG 4 heCover) ∧ Nat.card (PG 4 heCover) ≤ 4030387200) :
    Nat.card (griessHopfMultiplier CFSG.Blueprint.NativeSporadic.He) = 1 :=
  card_griessHopfMultiplier_of_mulEquiv_of_bounds heEquivJ hTab hP hC

end CFSG.Sporadic.Recognition.HeMultiplier

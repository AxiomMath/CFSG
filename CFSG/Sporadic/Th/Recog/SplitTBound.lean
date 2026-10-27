module

public import Certificates.Certificate687004
public import CFSG.GH74.QTGen4.Recog.G23.Words
public import CFSG.Sporadic.Recognition.PresentedWords

public section

open CFSG.CosetTable CFSG.GH74.QTGen4.Recog.G23
open CFSG.Sporadic.Recognition.PresentedWords

namespace CFSG.Sporadic.Th.Recog

theorem restrictWords_Tc (c : Fin 3 × Fin 3) :
    restrictWords (subsetOf 7 [0, 1, 2, 3, 4]) (Tc c) =
      restrictWords (subsetOf 6 [0, 1, 2, 3, 4]) g23Words := by
  rfl

theorem card_PG_Tc_le
    (c : Fin 3 × Fin 3) (hc : c ≠ (0, 0)) :
    Finite (PG 7 (Tc c)) ∧ Nat.card (PG 7 (Tc c)) ≤ 7371 * 576 := by
  obtain ⟨hfin, hcard⟩ := g23_check_triv
  have hfin' : Finite (PG (subsetOf 7 [0, 1, 2, 3, 4]).length
      (restrictWords (subsetOf 7 [0, 1, 2, 3, 4]) (Tc c))) := by
    rw [restrictWords_Tc c]
    exact hfin
  have hcard' : Nat.card (PG (subsetOf 7 [0, 1, 2, 3, 4]).length
      (restrictWords (subsetOf 7 [0, 1, 2, 3, 4]) (Tc c))) ≤ 576 := by
    rw [restrictWords_Tc c]
    exact hcard
  exact CFSG.KC.MiscCoset.card_le_of_index_restrict (Tc c) (subsetOf 7 [0, 1, 2, 3, 4])
    (Certificates.certificate687004 c hc) ⟨hfin', hcard'⟩

theorem card_closure_le_of_Tc
    {X : Type*} [Group X] (c : Fin 3 × Fin 3) (hc : c ≠ (0, 0)) (e : Fin 7 → X)
    (he : ∀ w ∈ Tc c, wprod e w = 1) :
    Nat.card (Subgroup.closure (Set.range e)) ≤ 7371 * 576 := by
  obtain ⟨hfin, hcard⟩ := card_PG_Tc_le c hc
  haveI := hfin
  let φ : PG 7 (Tc c) →* X := pgHom e he
  have hrange : φ.range = Subgroup.closure (Set.range e) := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of
      {r : FreeGroup (Fin 7) | r ∈ (Tc c).map FreeGroup.mk}, MonoidHom.map_closure]
    congr 1
    ext x
    simp [φ, pgHom_of]
  rw [← hrange]
  exact (Nat.card_le_card_of_surjective _ φ.rangeRestrict_surjective).trans hcard

end CFSG.Sporadic.Th.Recog

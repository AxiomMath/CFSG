module

public import CFSG.Holt.H78.SimpleStabilizer
public import CFSG.Holt.H78.Theorem1
public import CFSG.LocalAnalysis.StandardType.FS81.E7RecogPieces
public import CFSG.LocalAnalysis.StandardType.FS81.HoltEndAux

public section

namespace CFSG.StandardType.FrameRoute.FS81


private theorem isEmpty_mulEquiv_alternatingGroup_fin {H : Type*} [Group H]
    (hna : ∃ a c : H, a * c ≠ c * a)
    (hord : ∀ m : ℕ, 2 ≤ m → 2 * Nat.card H ≠ (2 * m).factorial) (m : ℕ) :
    IsEmpty (H ≃* alternatingGroup (Fin (2 * m))) := by
  refine ⟨fun e => ?_⟩
  rcases lt_or_ge m 2 with hm | hm
  · obtain ⟨a, c, hac⟩ := hna
    have hcomm : ∀ x y : Equiv.Perm (Fin (2 * m)), x * y = y * x := by
      interval_cases m <;> decide
    exact hac (e.injective (by rw [map_mul, map_mul]; exact Subtype.ext (hcomm _ _)))
  · haveI : Nontrivial (Fin (2 * m)) := Fin.nontrivial_iff_two_le.mpr (by omega)
    refine hord m hm ?_
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, two_mul_card_alternatingGroup,
      Fintype.card_perm, Fintype.card_fin]

theorem holtSimpleControl_holds : HoltSimpleControl := by
  intro G _ _ H S z hHs hna hord hS hzS hz hzc hfix
  haveI := hHs
  obtain ⟨P, hP⟩ := fs81Hl_sylow2In_sylow hS hzS hfix
  refine CFSG.Holt.H78.eq_top_of_isSimpleGroup_of_conj_mem CFSG.Holt.H78.holtTheorem1
    (hS.1 hzS) hz hfix ⟨P, by rw [hP]; exact hzS, fun s hs => ?_⟩ hna
    (isEmpty_mulEquiv_alternatingGroup_fin hna hord)
  rw [hP] at hs
  exact Subgroup.mem_centralizer_singleton_iff.mpr (hzc s hs)

end CFSG.StandardType.FrameRoute.FS81

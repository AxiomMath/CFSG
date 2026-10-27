module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22g

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem jM_mem_of_nonempty {D : Data G} {p : ℕ} (h : (calL0Star D p).Nonempty) :
    1 ≤ jM D p ∧ jM D p ≤ 5 ∧ (calLjStar D p (jM D p)).Nonempty ∧
      ∀ j, 1 ≤ j → j < jM D p → calLjStar D p j = ∅ := by
  classical
  set S : Set ℕ := {j | 1 ≤ j ∧ j ≤ 5 ∧ (calLjStar D p j).Nonempty} with hS
  have hSne : S.Nonempty := by
    by_contra hne
    have hemp : S = ∅ := Set.not_nonempty_iff_eq_empty.1 hne
    have h0 : jM D p = 0 := by
      unfold jM
      rw [← hS, hemp, Nat.sInf_empty]
    obtain ⟨X, hX⟩ := h
    rw [calL0Star, h0] at hX
    simp [calLjStar] at hX
  have hmemS : jM D p ∈ S := by
    rw [show jM D p = sInf S by rw [jM, hS]]
    exact Nat.sInf_mem hSne
  rw [hS] at hmemS
  have h1M : 1 ≤ jM D p := hmemS.1
  have h5M : jM D p ≤ 5 := hmemS.2.1
  refine ⟨h1M, h5M, hmemS.2.2, ?_⟩
  intro j hj1 hjl
  rw [Set.eq_empty_iff_forall_notMem]
  intro X hX
  have hjS : j ∈ S := by
    rw [hS]
    exact ⟨hj1, by omega, ⟨X, hX⟩⟩
  have hle : jM D p ≤ j := by
    rw [show jM D p = sInf S by rw [jM, hS]]
    exact Nat.sInf_le hjS
  omega

theorem not_isSimpleGroup_of_isA5xA5 {Y : Type} [Group Y] (hs : IsSimpleGroup Y)
    (h : IsA5xA5 Y) : False := by
  obtain ⟨e⟩ := h
  haveI := hs
  exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22g_prod_not_simple
    (A := alternatingGroup (Fin 5)) (B := alternatingGroup (Fin 5)) e.symm.isSimpleGroup

theorem not_isQuasisimple_of_isA5xA5 {Y : Type} [Group Y] (h : IsA5xA5 Y) :
    ¬ CFSG.Open.IsQuasisimple Y := by
  rintro ⟨-, hq⟩
  obtain ⟨e⟩ := h
  have hZ5 : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ :=
    alternatingGroup.center_eq_bot (by norm_num)
  have hZprod : Subgroup.center (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) = ⊥ := by
    rw [Subgroup.center_prod, hZ5, Subgroup.bot_prod_bot]
  have hZ : Subgroup.center Y = ⊥ := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [show Subgroup.map e.toMonoidHom (Subgroup.center Y) = ⊥ by
      simpa [MulEquiv.coe_toMonoidHom, hZprod] using Subgroup.map_center_eq e]
    rw [Subgroup.map_bot]
  have hA5q : IsA5xA5 (Y ⧸ Subgroup.center Y) :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩
  exact not_isSimpleGroup_of_isA5xA5 hq hA5q

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

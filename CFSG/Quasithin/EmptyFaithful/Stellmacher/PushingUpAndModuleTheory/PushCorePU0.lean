module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushCoreOffender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type*} [Group G]

theorem le_thompsonJ_of_isMax {S A : Subgroup G} (hA : IsMaxElemAbelian S A) : A ≤ thompsonJ S :=
  le_iSup₂_of_le A hA le_rfl

theorem isMaxElemAbelian_iff_of_thompsonJ_le [Finite G] {S R A : Subgroup G}
    (hJR : thompsonJ S ≤ R) (hRS : R ≤ S) : IsMaxElemAbelian R A ↔ IsMaxElemAbelian S A := by
  refine ⟨fun hA => ?_, fun hA => isMaxElemAbelian_of_le hA ((le_thompsonJ_of_isMax hA).trans hJR) hRS⟩
  obtain ⟨A', hA'⟩ := exists_isMaxElemAbelian S
  have hA'R : A' ≤ R := (le_thompsonJ_of_isMax hA').trans hJR
  have h1 : Nat.card A' ≤ Nat.card A := hA.2.2 A' hA'R hA'.2.1
  have h2 : Nat.card A ≤ Nat.card A' := hA'.2.2 A (hA.1.trans hRS) hA.2.1
  exact ⟨hA.1.trans hRS, hA.2.1, fun B hB hBe => (hA'.2.2 B hB hBe).trans h1⟩

theorem not_le_core_of_noCharNormal [Finite G] {X S Z : Subgroup G} (h : PushHyp X S Z)
    (hS : S ≠ ⊥)
    (hnc : ∀ C : Subgroup G, C ≤ S → C ≠ ⊥ → (C.subgroupOf S).Characteristic →
      ¬ X ≤ Subgroup.normalizer (C : Set G)) :
    ¬ thompsonJ S ≤ pCoreOf 2 X := by
  intro hJQ
  have hJeq : thompsonJ (pCoreOf 2 X) = thompsonJ S := by
    apply le_antisymm
    · refine iSup₂_le fun A hA => le_thompsonJ_of_isMax ?_
      exact (isMaxElemAbelian_iff_of_thompsonJ_le hJQ h.core_le).mp hA
    · refine iSup₂_le fun A hA => le_thompsonJ_of_isMax ?_
      exact (isMaxElemAbelian_iff_of_thompsonJ_le hJQ h.core_le).mpr hA
  refine hnc (thompsonJ S) (thompsonJ_le_self S)
    (CFSG.QuasithinUnique.Setup.thompsonJ_ne_bot h.sylow.2.1 hS)
    (CFSG.QuasithinUnique.Setup.characteristic_thompsonJ S) ?_
  rw [← hJeq]
  exact le_normalizer_thompsonJ_core X

end CFSG.Quasithin.F53Push

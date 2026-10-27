module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.XLinear
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.XOrth
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.XSympUnit
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.XProd
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.XData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv

open CFSG.Open Subgroup

theorem ordData_ordA_one_or {k : ℕ} (hk : 3 ≤ k) :
    OrdData (ordA 1 (2 ^ k)) ∨ ordA 1 (2 ^ k) = 504 := by
  rcases (show k = 3 ∨ 4 ≤ k by omega) with rfl | hk4
  · exact Or.inr ordA_one_two_pow_three
  · exact Or.inl (ordData_ordA_one hk4)

theorem xCases {X : Type} [Group X] {k : ℕ} (hX : IsClassicalGroup23 X k)
    (hk : 3 ≤ k ∨ (2 ≤ k ∧ PartTwo.IsOmegaMinus X 4 k)) :
    (IsSimpleGroup (X ⧸ center X) ∧
        (OrdData (Nat.card (X ⧸ center X)) ∨ Nat.card (X ⧸ center X) = 504)) ∨
      ∃ (S₀ : Type) (_ : Group S₀), IsSimpleGroup S₀ ∧
        (OrdData (Nat.card S₀) ∨ Nat.card S₀ = 504) ∧ Nonempty ((X ⧸ center X) ≃* S₀ × S₀) := by
  rcases hk with hk | ⟨hk, hXm⟩
  · rcases hX with h | h | h | h | h | ⟨a, rfl, h⟩ | h | h | h | h | h
    · obtain ⟨hs, hc⟩ := quotient_center_of_isL2 h
      exact Or.inl ⟨hs, hc ▸ ordData_ordA_one_or hk⟩
    · obtain ⟨hs, hc⟩ := quotient_center_of_isOmegaMinus_four h (by omega)
      exact Or.inl ⟨hs, Or.inl (hc ▸ ordData_ordA_one (by omega))⟩
    · obtain ⟨S₀, _, hs, hc, he⟩ := quotient_center_of_isOmegaPlus_four h (by omega)
      exact Or.inr ⟨S₀, inferInstance, hs, hc ▸ ordData_ordA_one_or hk, he⟩
    · obtain ⟨hs, hc⟩ := quotient_center_of_isSp4 h
      exact Or.inl ⟨hs, Or.inl (hc ▸ ordData_ordBC_two (by omega))⟩
    · obtain ⟨hs, hc⟩ := quotient_center_of_isSLn_three h (by omega)
      exact Or.inl ⟨hs, Or.inl (hc ▸ ordData_ordA_two hk)⟩
    · obtain ⟨hs, hc⟩ := quotient_center_of_isSUn_four h (by omega)
      exact Or.inl ⟨hs, Or.inl (hc ▸ ordData_ordTwistedA_three (by omega))⟩
    · obtain ⟨hs, hc⟩ := quotient_center_of_isOmegaMinus_six h (by omega)
      exact Or.inl ⟨hs, Or.inl (hc ▸ ordData_ordTwistedA_three (by omega))⟩
    · obtain ⟨hs, hc⟩ := quotient_center_of_isSLn_four h (by omega)
      exact Or.inl ⟨hs, Or.inl (hc ▸ ordData_ordA_three hk)⟩
    · obtain ⟨hs, hc⟩ := quotient_center_of_isOmegaPlus_six h (by omega)
      exact Or.inl ⟨hs, Or.inl (hc ▸ ordData_ordA_three hk)⟩
    · obtain ⟨hs, hc⟩ := quotient_center_of_isSpn_six h (by omega)
      exact Or.inl ⟨hs, Or.inl (hc ▸ ordData_ordBC_three (by omega))⟩
    · obtain ⟨hs, hc⟩ := quotient_center_of_isOmega8m h
      exact Or.inl ⟨hs, Or.inl (hc ▸ ordData_ordTwistedD_four (by omega))⟩
  · obtain ⟨hs, hc⟩ := quotient_center_of_isOmegaMinus_four hXm hk
    exact Or.inl ⟨hs, Or.inl (hc ▸ ordData_ordA_one (by omega))⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv

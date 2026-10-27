module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourTenDefs
import CFSG.LocalAnalysis.WeakClosure81.InEGroupSThreePair
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L2SevenLocal17Holds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.A6Exp4Models
public import CFSG.Adapters.StatedPSLTwoNine
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81

theorem inEGroup_of_isL2_seven {Q : Type} [Group Q] [Finite Q] {i : ℕ} (hi : 1 ≤ i)
    (h : F6.IsL2 7 1 Q) : InEGroup i Q := by
  have hL : IsL2Odd Q 7 :=
    (CFSG.Blueprint.LieModel.classical_iff (t := .PSL) (by decide)).2 h
  refine inEGroup_of_sThreePair hi fun T hT => ?_
  obtain ⟨X₁, X₂, -, -, -, -, -, hsup, hB₁, hB₂⟩ := (k_L27Local_holds Q hL T hT).2
  have hsup' : (T ⊔ X₁) ⊔ (T ⊔ X₂) = ⊤ := by
    apply top_unique
    rw [← hsup]
    exact sup_le le_sup_left (le_sup_right.trans le_sup_right)
  exact ⟨T ⊔ X₁, T ⊔ X₂, le_sup_left, le_sup_left, hsup', hB₁, hB₂⟩

theorem inEGroup_of_mulEquiv_alt_six {Q : Type} [Group Q] [Finite Q] {i : ℕ} (hi : 1 ≤ i)
    (e : Q ≃* alternatingGroup (Fin 6)) : InEGroup i Q := by
  refine inEGroup_of_sThreePair hi fun T hT => ?_
  obtain ⟨Q₀, Q₁, h₀, h₁, hsup⟩ := exists_sThree_pair_of_alt_six hT e
  exact ⟨Q₀, Q₁, h₀.1, h₁.1, hsup, h₀.bar2 hT, h₁.bar2 hT⟩

theorem inEGroup_of_mulEquiv_perm_six {Q : Type} [Group Q] [Finite Q] {i : ℕ} (hi : 1 ≤ i)
    (e : Q ≃* Equiv.Perm (Fin 6)) : InEGroup i Q := by
  refine inEGroup_of_sThreePair hi fun T hT => ?_
  obtain ⟨Q₀, Q₁, h₀, h₁, hsup⟩ := exists_sThree_pair_of_perm_six hT e
  exact ⟨Q₀, Q₁, h₀.1, h₁.1, hsup, h₀.bar2 hT, h₁.bar2 hT⟩

theorem w4Lem4_10Small_holds : W4Lem4_10Small := by
  intro Q _ _ h
  rcases h with h | h | h
  · exact inEGroup_of_isL2_seven le_rfl h
  · obtain ⟨e⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_alternating_six_of_psl_two_nine h
    exact inEGroup_of_mulEquiv_alt_six le_rfl e
  · obtain ⟨e⟩ : Nonempty (Q ≃* Equiv.Perm (Fin 6)) := h
    exact inEGroup_of_mulEquiv_perm_six le_rfl e

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

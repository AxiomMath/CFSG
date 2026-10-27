module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem w135c2_gs03_general (hL4 : GS03AlphaL4) (hA6 : GS03AlphaA6) (hU33 : GS03AlphaU33) :
    (∀ (G : Type) [Group G] [Finite G] (S : Subgroup G), S.Normal → Subgroup.centralizer (S : Set G)
        = ⊥ → ∀ A : ℕ, AlphaCase ↥S A → ∀ x : G, orderOf x = 2 → ∃ T : Finset G, T.card ≤ A ∧ (∀ y ∈
        T, ∃ s ∈ S, y = s * x * s⁻¹) ∧ S ≤ Subgroup.closure (T : Set
        G)) ∧ GS03AlphaOuterGeneral := by
  refine ⟨?_, hL4⟩
  intro G _ _ S hS hC A hA x hx
  rcases hA with ⟨h6, rfl⟩ | ⟨h33, rfl⟩
  · exact hA6 G S hS hC h6 x hx
  · exact hU33 G S hS hC h33 x hx

theorem w135c2_rows_of_idx (h : Chev135Rows) {t : StatedLieTag} {n f D : ℕ}
    (hi : Chev2RowIdx t n f D) : FinRowStmt t n f D := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  unfold Chev2RowIdx at hi
  split at hi
  · subst_vars; exact h1
  · subst_vars; exact h2
  · subst_vars; exact h3
  · subst_vars; exact h4
  · subst_vars; exact h5
  · subst_vars; exact h6
  · subst_vars; exact h7
  · subst_vars; exact h8
  · exact hi.elim

theorem w135c2_three_le_gs03Bound {S : Type} [Group S] {t : StatedLieTag} {n f : ℕ}
    (h : LieModel S t n 2 f) : 3 ≤ gs03Bound t n f := by
  have hadm := h.admissible
  cases t
  · rcases hadm with ⟨-, -, hn2, -, -⟩
    rcases n with _ | _ | _ | _ | _ | n
    · omega
    · omega
    · simp only [gs03Bound]; split_ifs <;> omega
    · simp only [gs03Bound]; split_ifs <;> omega
    · simp only [gs03Bound]; split_ifs <;> omega
    · simp only [gs03Bound]; omega
  · rcases hadm with ⟨-, -, hn3, -⟩
    rcases n with _ | _ | _ | _ | _ | n
    · omega
    · omega
    · omega
    · simp only [gs03Bound]; omega
    · simp only [gs03Bound]; omega
    · simp only [gs03Bound]; omega
  · rcases hadm with ⟨-, -, hn2, -⟩
    rcases n with _ | _ | _ | n
    · omega
    · omega
    · simp only [gs03Bound]; omega
    · simp only [gs03Bound]; omega
  · rcases hadm with ⟨-, -, -, hne⟩
    exact absurd rfl hne
  · rcases hadm with ⟨-, -, hn4⟩
    simp only [gs03Bound]; omega
  · rcases hadm with ⟨-, -, hn4⟩
    simp only [gs03Bound]; omega
  · simp only [gs03Bound]; omega
  · simp only [gs03Bound]; omega
  · simp only [gs03Bound]; omega
  · simp only [gs03Bound]; omega
  · simp only [gs03Bound]; omega
  · simp only [gs03Bound]; omega
  · simp only [gs03Bound]; omega
  · simp only [gs03Bound]; omega
  · rcases hadm with ⟨-, -, -, h23, -⟩
    exact absurd h23 (by norm_num)
  · simp only [gs03Bound]; omega
  · simp only [gs03Bound]; omega

theorem w135c2_concl_of_item3 {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}
    {t : MulAut W} (h : Chev2Item3 W L) : W4Lem13_5Concl W Y L t := by
  unfold W4Lem13_5Concl
  rcases h with h | h | h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
      Or.inr (Or.inl h)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
      Or.inr (Or.inr h)))))))))

end CFSG.LocalAnalysis.WeakClosure81

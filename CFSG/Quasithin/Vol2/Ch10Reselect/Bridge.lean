module

public import CFSG.Quasithin.Vol2.Ch10Reselect.Statements
public import CFSG.Quasithin.Vol2.Ch7Stmt326Lt

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.Vol2.Ch10
open scoped IsMulCommutative

@[expose] def Stmt3_2_6LtA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), FSU G T L I → L < fsuL0 T L →
    (∃ _ : IsMulCommutative ↥(fsuV T I), I = fsuV T I ∧ fsuV T I = fsuVM T L I ∧
        ((∃ n : ℕ, Row711OmegaPlus T L I n) ∨ Row711L3Wreath T L I)) ∨
      Concl326ThreeCA T L I

theorem stmt3_2_6Lt_of_A (h : Stmt3_2_6LtA) : Stmt3_2_6Lt := fun G _ _ T L I hfsu hlt =>
  (h G T L I hfsu hlt).imp_right concl326ThreeC_of_A

theorem stmt3_2_6LtA_of_C (h326 : Stmt3_2_6C) : Stmt3_2_6LtA := by
  intro G _ _ T L I hfsu hlt
  have hbr := (tmpL6_3_2_6C_of_stmt3_2_6C h326 G T L I hfsu hlt).2.2
  obtain ⟨⟨hcV, hqV⟩, hcVM, hqVM, hcases⟩ := h326 G T L I hfsu hlt.ne
  rcases hcases with ⟨n, K, _, _, hcard, hlie, hV0, hVVM, hreal⟩ | ⟨-, hV0, hVVM, hreal⟩ |
    ⟨⟨ha, -, -⟩, -⟩
  ·
    refine Or.inl ⟨hcV, hV0, hVVM, Or.inl ⟨n, hlt, two_le_of_lieModel_psl_two hlie, K,
      inferInstance, inferInstance, hcard, ?_⟩⟩
    rw [← tensorNatModel_eq]
    exact realizesMod_of_eq hVVM _ _ hreal
  ·
    refine Or.inl ⟨hcV, hV0, hVVM, Or.inr ⟨hlt, ?_⟩⟩
    rw [← tensorNatModel_eq]
    exact realizesMod_of_eq hVVM _ _ hreal
  ·
    rcases hbr with hrow | h3
    · exact Or.inl hrow
    · exact Or.inr (h3.imp_right fun ⟨hc, hiv⟩ => ⟨hc, ha, hiv⟩)

end CFSG.Quasithin.H13

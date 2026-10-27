module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K108Rows
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dTitsModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.RankThreeUC.S15.K21dTitsProof (solvOver_of_lieModel)

theorem k108BT_of_lieModel {F : (S : Type) → [Group S] → Prop}
    (hF : ∀ (S : Type) [Group S], F S → ∃ (t : StatedLieTag) (m n : ℕ), 2 ≤ n ∧
      (t = .PSL ∨ t = .PSp ∨ t = .PSU ∨ t = .POmegaMinus) ∧ LieModel S t m 2 n) :
    K108BT F := by
  intro S _ _ _ _ hS T hT H hTH hH
  obtain ⟨t, m, n, hn, ht, h⟩ := hF S hS
  exact solvOver_of_lieModel hn ht h
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2 hT) H hTH hH

theorem k108BTL2_holds : K108BTL2 := by
  refine k108BT_of_lieModel fun S _ hS => ?_
  obtain ⟨n, hn, h⟩ := hS
  exact ⟨.PSL, 2, n, hn.le, Or.inl rfl, h⟩

theorem k108BTU3_holds : K108BTU3 := by
  refine k108BT_of_lieModel fun S _ hS => ?_
  obtain ⟨n, hn, h⟩ := hS
  exact ⟨.PSU, 3, n, hn.le, Or.inr (Or.inr (Or.inl rfl)), h⟩

theorem k108BTL3_holds : K108BTL3 := by
  refine k108BT_of_lieModel fun S _ hS => ?_
  obtain ⟨n, hn, h⟩ := hS
  exact ⟨.PSL, 3, n, hn.le, Or.inl rfl, h⟩

theorem k108BTSp4_holds : K108BTSp4 := by
  refine k108BT_of_lieModel fun S _ hS => ?_
  obtain ⟨n, hn, h⟩ := hS
  exact ⟨.PSp, 2, n, hn.le, Or.inr (Or.inl rfl), h⟩

theorem k108BTU4_holds : K108BTU4 := by
  refine k108BT_of_lieModel fun S _ hS => ?_
  obtain ⟨n, hn, h⟩ := hS
  exact ⟨.PSU, 4, n, hn, Or.inr (Or.inr (Or.inl rfl)), h⟩

theorem k108BTU5_holds : K108BTU5 :=
  k108BT_of_lieModel fun _ _ hS => ⟨.PSU, 5, 2, le_rfl, Or.inr (Or.inr (Or.inl rfl)), hS⟩

theorem k108BTL4_holds : K108BTL4 := by
  refine k108BT_of_lieModel fun S _ hS => ?_
  obtain ⟨n, hn, h⟩ := hS
  exact ⟨.PSL, 4, n, hn.le, Or.inl rfl, h⟩

theorem k108BTSp6_holds : K108BTSp6 := by
  refine k108BT_of_lieModel fun S _ hS => ?_
  obtain ⟨n, hn, h⟩ := hS
  exact ⟨.PSp, 3, n, hn.le, Or.inr (Or.inl rfl), h⟩

theorem k108BTO8m_holds : K108BTO8m := by
  refine k108BT_of_lieModel fun S _ hS => ?_
  obtain ⟨n, hn, h⟩ := hS
  exact ⟨.POmegaMinus, 4, n, hn, Or.inr (Or.inr (Or.inr rfl)), h⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10

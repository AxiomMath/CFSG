module

public import CFSG.Quasithin.H13.Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped MatrixGroups

@[expose] def SevenModels (G : Type) [Group G] : Prop :=
  LieModel G .PSp 3 2 1 ∨ LieModel G .PSU 4 3 1 ∨ LieModel G .PSU 4 2 1 ∨
    LieModel G .PSL 4 3 1 ∨ LieModel G .G2 0 3 1 ∨
    Nonempty (G ≃* NativeSporadic.HS) ∨ Nonempty (G ≃* NativeSporadic.Ru)

theorem nonempty_quotient_center_equiv_of_equiv_alt6 {Q : Type} [Group Q]
    (h : Nonempty (Q ≃* alternatingGroup (Fin 6))) :
    Nonempty (Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨e⟩ := h
  have hZ : Subgroup.center Q = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
    have hez : e z ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
      refine Subgroup.mem_center_iff.2 fun y => ?_
      obtain ⟨x, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz x]
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hez
    exact e.injective (hez.trans (map_one e).symm)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e)⟩

theorem sevenModels_of_inputs (h137 : Stmt13_1_7) (h1312 : Stmt13_1_2_three)
    (h13316 : Stmt13_3_16) (h1361 : Stmt13_6_1) (h1381 : Stmt13_8_1)
    (h14813 : Stmt14_8_1_three) {G : Type} [Group G] [Finite G] {T L : Subgroup G}
    (hH : QTH13 G T L) (hmax : quasithinIsMaximalLocal T L) : SevenModels G := by
  have hq := h137 G T hH.simple hH.nonabelian hH.qtke hH.sylow hH.not_excluded L hH.faithful
  rcases h1312 G T L hH.simple hH.nonabelian hH.qtke hH.sylow hH.not_excluded hmax hH.faithful
      hq with hA5 | hL32 | hA6 | ⟨-, -, hA6c⟩ | hU33
  · rcases h1361 G T L hH ((quasithinO2QuotientIso_iff L _).2 hA5) with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases h14813 G T L hH hL32 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  · rcases h1381 G T L hH (nonempty_quotient_center_equiv_of_equiv_alt6 hA6) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases h1381 G T L hH hA6c with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact absurd hU33 (h13316 G T L hH)

theorem catalog_of_sevenModels {G : Type} [Group G] (h : SevenModels G) : Catalog G := by
  rcases h with h | h | h | h | h | h | h
  · exact lieModel_catalog G _ _ _ _ h
  · exact lieModel_catalog G _ _ _ _ h
  · exact lieModel_catalog G _ _ _ _ h
  · exact lieModel_catalog G _ _ _ _ h
  · exact lieModel_catalog G _ _ _ _ h
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨.HS, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨.Ru, h⟩)))

theorem qt_h13_maximal_local_catalog_assembly_of_inputs (h137 : Stmt13_1_7)
    (h1312 : Stmt13_1_2_three) (h13316 : Stmt13_3_16) (h1361 : Stmt13_6_1)
    (h1381 : Stmt13_8_1) (h14813 : Stmt14_8_1_three) (G : Type) [Group G] [Finite G]
    (T L : Subgroup G) (hH : QTH13 G T L)
    (hL : quasithinIsMaximalLocal T L ∧ quasithinIsFaithfulLocal T L) : Catalog G :=
  catalog_of_sevenModels (sevenModels_of_inputs h137 h1312 h13316 h1361 h1381 h14813 hH hL.1)

end CFSG.Quasithin.H13

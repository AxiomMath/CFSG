module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2Nat
public import CFSG.Quasithin.Vol2.Ch3Sec3S6Sylow
public import CFSG.Quasithin.Background.G64Statement

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.Quasithin.H13 Subgroup
open scoped Pointwise

private def s16c11_v1_part6 : Finset (Finset (Fin 6)) := {{0, 1}, {2, 3}, {4, 5}}

private def s16c11_v1_wr63 : Subgroup (Equiv.Perm (Fin 6)) :=
  MulAction.stabilizer (Equiv.Perm (Fin 6)) s16c11_v1_part6

private instance : DecidablePred (· ∈ s16c11_v1_wr63) := fun g =>
  inferInstanceAs (Decidable (g • s16c11_v1_part6 = s16c11_v1_part6))

set_option maxRecDepth 100000 in
private theorem s16c11_v1_card_wr63 : Fintype.card ↥s16c11_v1_wr63 = 48 := by
  decide +kernel

private theorem s16c11_v1_sylow_le_wr63 : sylowS6 ≤ s16c11_v1_wr63 := by
  rw [sylowS6, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · show Equiv.swap (0 : Fin 6) 1 ∈ s16c11_v1_wr63
    decide +kernel
  · show Equiv.swap (0 : Fin 6) 2 * Equiv.swap 1 3 ∈ s16c11_v1_wr63
    decide +kernel
  · show Equiv.swap (4 : Fin 6) 5 ∈ s16c11_v1_wr63
    decide +kernel

private theorem s16c11_v1_relIndex_wr63 :
    sylowS6.relIndex s16c11_v1_wr63 = 3 := by
  have hle := s16c11_v1_sylow_le_wr63
  have h1 := Subgroup.relIndex_mul_card sylowS6 s16c11_v1_wr63
  rw [inf_eq_left.2 hle] at h1
  have hT : Nat.card ↥sylowS6 = 16 := S6Syl.card_sylowS6
  have hX : Nat.card ↥s16c11_v1_wr63 = 48 := by
    rw [Nat.card_eq_fintype_card, s16c11_v1_card_wr63]
  rw [hT, hX] at h1
  omega

private theorem s16c11_v1_index_sylow_odd : ¬ 2 ∣ sylowS6.index := by
  have h1 := Subgroup.card_mul_index sylowS6
  rw [S6Syl.card_sylowS6, S6Syl.card_perm_six] at h1
  have h2 : sylowS6.index = 45 := by omega
  rw [h2]
  decide

private def s16c11_v1_y6 : PermMod 6 :=
  Multiplicative.ofAdd (fun i => if i ∈ ({0, 1, 2, 3} : Finset (Fin 6)) then 1 else 0)

private theorem s16c11_v1_y6_mem : s16c11_v1_y6 ∈ G6.coreMod 6 := by
  rw [mem_coreMod]
  decide +kernel

private theorem s16c11_v1_y6_fix : ∀ t ∈ sylowS6,
    G6.permAct 6 t s16c11_v1_y6 * s16c11_v1_y6⁻¹ ∈ (⊥ : Subgroup (PermMod 6)) := by
  intro t ht
  rw [Subgroup.mem_bot]
  refine mul_inv_eq_one.2 ?_
  have ht' : t ∈ S6Syl.elemsS := by
    rwa [S6Syl.sylowS6_eq] at ht
  have h : ∀ t ∈ S6Syl.elemsS, permAct 6 t s16c11_v1_y6 = s16c11_v1_y6 := by
    decide +kernel
  exact h t ht'

private def s16c11_v1_g6 : Equiv.Perm (Fin 6) where
  toFun i := ![2, 3, 4, 5, 0, 1] i
  invFun i := ![4, 5, 0, 1, 2, 3] i
  left_inv := by decide
  right_inv := by decide

private theorem s16c11_v1_g6_mem : s16c11_v1_g6 ∈ s16c11_v1_wr63 := by
  show s16c11_v1_g6 • s16c11_v1_part6 = s16c11_v1_part6
  decide +kernel

private theorem s16c11_v1_g6_moves :
    G6.permAct 6 s16c11_v1_g6 s16c11_v1_y6 * s16c11_v1_y6⁻¹ ∉
      (⊥ : Subgroup (PermMod 6)) := by
  rw [Subgroup.mem_bot]
  intro h
  have h1 : G6.permAct 6 s16c11_v1_g6 s16c11_v1_y6 = s16c11_v1_y6 :=
    mul_inv_eq_one.1 h
  have h2 := congrArg Multiplicative.toAdd h1
  revert h2
  decide +kernel

theorem s16c11_v1_modelRF3_symCore_six : S16C11ModelRF3 (G64.symCoreModel 6) := by
  change ∃ T X : Subgroup (Equiv.Perm (Fin 6)), T ≤ X ∧ IsPGroup 2 ↥T ∧
    ¬ 2 ∣ T.index ∧ T.relIndex X = 3 ∧
    ∃ y ∈ G6.coreMod 6, (∀ t ∈ T, G6.permAct 6 t y * y⁻¹ ∈ (⊥ : Subgroup (PermMod 6))) ∧
      ∃ g ∈ X, G6.permAct 6 g y * y⁻¹ ∉ (⊥ : Subgroup (PermMod 6))
  exact ⟨sylowS6, s16c11_v1_wr63, s16c11_v1_sylow_le_wr63,
    IsPGroup.of_card (n := 4) (by rw [S6Syl.card_sylowS6]; norm_num),
    s16c11_v1_index_sylow_odd, s16c11_v1_relIndex_wr63, s16c11_v1_y6, s16c11_v1_y6_mem,
    s16c11_v1_y6_fix, s16c11_v1_g6, s16c11_v1_g6_mem, s16c11_v1_g6_moves⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

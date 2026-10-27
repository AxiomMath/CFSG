module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.S126P31

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem center_statedSL_eq (n : ℕ) (F : Type) [Field F] :
    Subgroup.center ↥(StatedSL n F) = (StatedScalars (Fin n) F).subgroupOf (StatedSL n F) := by
  rw [← map_center_eq_statedScalars n F, Subgroup.map_center_eq]

theorem commutator_statedSL_three (F : Type) [Field F] : commutator ↥(StatedSL 3 F) = ⊤ := by
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := F) (n := 3) le_rfl
  have h : Group.IsPerfect ↥(StatedSL 3 F) :=
    Group.IsPerfect.ofSurjective (f := (specialLinearGroupEquivStatedSL 3 F).toMonoidHom)
      (specialLinearGroupEquivStatedSL 3 F).surjective
  exact Group.isPerfect_def.mp h

theorem card_center_statedSL_three {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) :
    Nat.card (Subgroup.center ↥(StatedSL 3 F)) = 3 := by
  have hS : Nat.card ↥(StatedSL 3 F) = 60480 := by
    rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 3 F).toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num : 1 ≤ 3), hF]
    decide
  have hP : Nat.card (StatedProj (StatedSL 3 F)) = 20160 := by
    rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 3), hF]
    decide
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F))
  have hP' : Nat.card (↥(StatedSL 3 F) ⧸ (StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F)) =
      20160 := hP
  rw [hS, hP'] at h
  rw [center_statedSL_eq]
  omega

theorem sl34_central_extension {K : Type} [Group K] [Finite K] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) (e : K ≃* ↥(StatedSL 3 F)) :
    commutator K = ⊤ ∧ Nat.card (Subgroup.center K) = 3 ∧
      IsPSL 3 2 2 (K ⧸ Subgroup.center K) := by
  have hmap : (Subgroup.center K).map e.toMonoidHom =
      (StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F) :=
    (Subgroup.map_center_eq e).trans (center_statedSL_eq 3 F)
  refine ⟨?_, ?_, ?_⟩
  · have h : Group.IsPerfect ↥(StatedSL 3 F) :=
      Group.isPerfect_def.mpr (commutator_statedSL_three F)
    have h' : Group.IsPerfect K :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact Group.isPerfect_def.mp h'
  · have h1 : Nat.card ((Subgroup.center K).map e.toMonoidHom) = Nat.card (Subgroup.center K) :=
      Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective
    have h3 := card_center_statedSL_three hF
    rw [center_statedSL_eq] at h3
    rw [← h1, hmap]
    exact h3
  · refine ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩, F, inferInstance,
      inferInstance, by rw [hF]; norm_num, ⟨QuotientGroup.congr _ _ e hmap⟩⟩

end CFSG.Quasithin.H13.S126P31

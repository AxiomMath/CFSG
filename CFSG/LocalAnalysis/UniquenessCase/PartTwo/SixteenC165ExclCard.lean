module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22d
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatAlt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

namespace Om8Excl

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open scoped MatrixGroups

theorem card_isOmegaPlus_four {X : Type} [Group X] {a : ℕ} (ha : 2 ≤ a)
    (h : IsOmegaPlus X 4 a) : Nat.card X = (2 ^ a * (4 ^ a - 1)) ^ 2 := by
  obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := h
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hcard
  have h4 : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hv : ∃ v, quadPlus 2 K v ≠ 0 := by
    refine ⟨fun i => if i = Sum.inl 0 ∨ i = Sum.inr 0 then 1 else 0, ?_⟩
    rw [coe_quadPlus]
    simp [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Fin.sum_univ_two]
  obtain ⟨e2⟩ := uc22p22d_omegaPlus4_equiv (F := K) h4
  rw [Nat.card_congr e.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega (coe_quadPlus 2 K) hv,
    ← Nat.card_congr e2.toEquiv, Nat.card_prod]
  rw [Nat.card_congr (specialLinearGroupEquivStatedSL 2 K).toEquiv,
    CFSG.Open.StatedAPI.card_statedSL_two, hcard, ← sq]
  congr 2
  rw [show (4 : ℕ) ^ a = (2 ^ a) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]

theorem card_isAlt_five {X : Type} [Group X] (h : UC22.IsAlt X 5) : Nat.card X = 60 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  have h2 : 2 * Nat.card (alternatingGroup (Fin 5)) = Nat.card (Equiv.Perm (Fin 5)) :=
    two_mul_nat_card_alternatingGroup
  rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 5)), Fintype.card_perm,
    Fintype.card_fin] at h2
  rw [show Nat.factorial 5 = 120 by decide] at h2
  omega

theorem card_isL3_one {X : Type} [Group X] (h : IsL3 X 1) : Nat.card X = 168 := by
  have hc := CFSG.SeitzReduction.LinearPilot.card_of_lieModel_PSL_two h
  rw [hc]
  decide

end Om8Excl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

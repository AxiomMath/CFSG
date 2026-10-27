module

public import CFSG.Quasithin.Vol2.Ch11SecA02Card
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp StatedProj StatedScalars
  specialLinearGroupEquivStatedSL)

@[expose] def ShapeData (X : Type) [Group X] (n : ℕ) : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K) (c : ℕ), Nat.card K = 2 ^ n ∧ c ∣ 2 ^ n - 1 ∧
      c * Nat.card X = 2 ^ (3 * n) * oSL3 n ∧ (c = 1 → Nat.card (Subgroup.center X) ≤ 3) ∧
      ∃ f : Matrix.SpecialLinearGroup (Fin 3) K →* X, Function.Surjective f) ∨
    (∃ c : ℕ, c ∣ 2 ^ n - 1 ∧ c * Nat.card X = 2 ^ (4 * n) * oSp4 n) ∨
    Nat.card X = 2 ^ (6 * n) * oG2 n

theorem card_statedProj_mul {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] (H : Subgroup (GL ι K)) :
    Nat.card ((StatedScalars ι K).subgroupOf H) * Nat.card (StatedProj H) = Nat.card H := by
  rw [mul_comm]
  exact ((StatedScalars ι K).subgroupOf H).card_eq_card_quotient_mul_card_subgroup.symm

theorem shapeData_of_shape11 (hG2 : FactG2AdjointOrder) {X : Type} [Group X] [Finite X] {n : ℕ}
    (hn : 2 ≤ n) (hs : (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
        Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) K)) ∨
      LieModel X .PSL 3 2 n ∨ LieModel X .PSp 2 2 n ∨ LieModel X .G2 0 2 n) :
    ShapeData X n := by
  rcases hs with ⟨K, _, _, hK, ⟨e⟩⟩ | hL | hL | hL
  · refine Or.inl ⟨K, inferInstance, inferInstance, 1, hK, one_dvd _, ?_, fun _ => ?_,
      e.symm.toMonoidHom, e.symm.surjective⟩
    · rw [one_mul, Nat.card_congr e.toEquiv, card_SL_three' hK]
    · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
      exact card_center_SL_three_le
  · rcases hL with ⟨-, -, K, _, _, hK, ⟨e⟩⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · set c := Nat.card ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K))
      have hc : c * Nat.card X = 2 ^ (3 * n) * oSL3 n := by
        rw [Nat.card_congr e.toEquiv, card_statedProj_mul, ← card_SL_three' hK,
          Nat.card_congr (specialLinearGroupEquivStatedSL 3 K).toEquiv]
      have hcd : c ∣ 2 ^ n - 1 := by
        have := card_scalars_subgroupOf_dvd (K := K) (StatedSL 3 K)
        rwa [hK] at this
      refine Or.inl ⟨K, inferInstance, inferInstance, c, hK, hcd, hc, fun hc1 => ?_, ?_⟩
      · have hbot : (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K) = ⊥ :=
          (Subgroup.card_eq_one).mp hc1
        let e₁ : X ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
          (e.trans (QuotientGroup.quotientMulEquivOfEq hbot)).trans
            (QuotientGroup.quotientBot.trans (specialLinearGroupEquivStatedSL 3 K).symm)
        rw [Nat.card_congr (Subgroup.centerCongr e₁).toEquiv]
        exact card_center_SL_three_le
      · refine ⟨e.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp
          (specialLinearGroupEquivStatedSL 3 K).toMonoidHom), ?_⟩
        exact e.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp
          (specialLinearGroupEquivStatedSL 3 K).surjective)
    · exact absurd h (by norm_num)
    · exact absurd h (by norm_num)
    · exact absurd h (by norm_num)
  · rcases hL with ⟨-, -, K, _, _, hK, ⟨e⟩⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · refine Or.inr (Or.inl ⟨Nat.card ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf
        (StatedSp 2 K)), ?_, ?_⟩)
      · have := card_scalars_subgroupOf_dvd (K := K) (StatedSp 2 K)
        rwa [hK] at this
      · rw [Nat.card_congr e.toEquiv, card_statedProj_mul, card_Sp_four hK]
    · exact absurd h (by norm_num)
    · exact absurd h (by norm_num)
    · exact absurd h (by norm_num)
  · rcases hL with ⟨h, -⟩ | ⟨-, -, -, K, _, _, hK, ⟨e⟩⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact absurd h (by decide)
    · refine Or.inr (Or.inr ?_)
      rw [Nat.card_congr e.toEquiv, hG2 K n (by omega) hK, oG2, ← pow_mul, ← pow_mul,
        mul_comm n 6, mul_comm n 2]
    · exact absurd h (by decide)
    · exact absurd h (by decide)

end CFSG.Quasithin.Vol2.Ch11.SecA

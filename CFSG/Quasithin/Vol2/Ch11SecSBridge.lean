module

public import CFSG.Quasithin.Vol2.Ch11SecA02Shape

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp StatedProj StatedScalars
  specialLinearGroupEquivStatedSL)

abbrev Shape4 (X : Type) [Group X] : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ 2 ∧
      Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) K)) ∨
    LieModel X .PSL 3 2 2 ∨ LieModel X .PSp 2 2 2 ∨ LieModel X .G2 0 2 2

variable {X : Type} [Group X]

theorem card_of_shape_SL (hs : (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ 2 ∧
      Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) K)) ∨ LieModel X .PSL 3 2 2) :
    ∃ c m, Odd c ∧ Odd m ∧ c * Nat.card X = 2 ^ 6 * m := by
  rcases hs with ⟨K, _, _, hK, ⟨e⟩⟩ | hL
  · obtain ⟨m, hm, hc⟩ := card_SL3_eq (n := 2) (by norm_num) hK
    exact ⟨1, m, odd_one, hm, by rw [one_mul, Nat.card_congr e.toEquiv, hc]⟩
  · rcases hL with ⟨-, -, K, _, _, hK, ⟨e⟩⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · obtain ⟨m, hm, hc⟩ := card_SL3_eq (n := 2) (by norm_num) hK
      set c := Nat.card ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K))
      have hcd : c ∣ 2 ^ 2 - 1 := by
        have := card_scalars_subgroupOf_dvd (K := K) (StatedSL 3 K)
        rwa [hK] at this
      refine ⟨c, m, Odd.of_dvd_nat (by decide) hcd, hm, ?_⟩
      rw [Nat.card_congr e.toEquiv, card_statedProj_mul, ← hc,
        Nat.card_congr (specialLinearGroupEquivStatedSL 3 K).toEquiv]
    · exact absurd h (by norm_num)
    · exact absurd h (by norm_num)
    · exact absurd h (by norm_num)

theorem card_of_shape_Sp (hs : LieModel X .PSp 2 2 2) :
    ∃ c m, Odd c ∧ Odd m ∧ c * Nat.card X = 2 ^ 8 * m := by
  rcases hs with ⟨-, -, K, _, _, hK, ⟨e⟩⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · obtain ⟨m, hm, hc⟩ := card_Sp4_eq (n := 2) (by norm_num) hK
    set c := Nat.card ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K))
    have hcd : c ∣ 2 ^ 2 - 1 := by
      have := card_scalars_subgroupOf_dvd (K := K) (StatedSp 2 K)
      rwa [hK] at this
    exact ⟨c, m, Odd.of_dvd_nat (by decide) hcd, hm, by
      rw [Nat.card_congr e.toEquiv, card_statedProj_mul, hc]⟩
  · exact absurd h (by norm_num)
  · exact absurd h (by norm_num)
  · exact absurd h (by norm_num)

theorem card_of_shape_G2 (hG2a : FactG2AdjointOrder) (hs : LieModel X .G2 0 2 2) :
    ∃ m, Odd m ∧ Nat.card X = 2 ^ 12 * m := by
  rcases hs with ⟨h, -⟩ | ⟨-, -, -, K, _, _, hK, ⟨e⟩⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  · exact absurd h (by decide)
  · refine ⟨((2 ^ 2) ^ 6 - 1) * ((2 ^ 2) ^ 2 - 1), by decide, ?_⟩
    rw [Nat.card_congr e.toEquiv, hG2a K 2 (by norm_num) hK]
    norm_num
  · exact absurd h (by decide)
  · exact absurd h (by decide)

theorem isPSp4_of_shape (hG2a : FactG2AdjointOrder) (hs : Shape4 X)
    (hk : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ 2 ∧
      Nonempty (X ≃* ↥(StatedSp 2 K))) : IsPSp4 2 2 X := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hk
  obtain ⟨m, hm, hc⟩ := card_Sp4_eq (n := 2) (by norm_num) hK
  have hX : Nat.card X = 2 ^ 8 * m := by rw [Nat.card_congr e.toEquiv, hc]
  have hSL : ¬ ((∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ 2 ∧
      Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) K)) ∨ LieModel X .PSL 3 2 2) := by
    intro hs'
    obtain ⟨c, m', hc', hm', h⟩ := card_of_shape_SL hs'
    rw [hX] at h
    have := eq_of_two_pow_mul_odd (a := 8) (b := 6) (hc'.mul hm) hm' (by rw [← h]; ring)
    omega
  rcases hs with hs | hs | hs | hs
  · exact absurd (Or.inl hs) hSL
  · exact absurd (Or.inr hs) hSL
  · rcases hs with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h (by norm_num)
    · exact absurd h (by norm_num)
    · exact absurd h (by norm_num)
  · obtain ⟨m', hm', h⟩ := card_of_shape_G2 hG2a hs
    rw [hX] at h
    have := eq_of_two_pow_mul_odd (a := 8) (b := 12) hm hm' h
    omega

theorem isG2_of_shape (hG2 : FactG2DerivedOrder) (hs : Shape4 X)
    (hk : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ 2 ∧
      Nonempty (X ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆)) : IsG2 2 2 X := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hk
  obtain ⟨m, hm, hc⟩ := card_G2_eq hG2 (n := 2) le_rfl hK
  have hX : Nat.card X = 2 ^ 12 * m := by rw [Nat.card_congr e.toEquiv, hc]
  rcases hs with hs | hs | hs | hs
  · obtain ⟨c, m', hc', hm', h⟩ := card_of_shape_SL (Or.inl hs)
    rw [hX] at h
    have := eq_of_two_pow_mul_odd (a := 12) (b := 6) (hc'.mul hm) hm' (by rw [← h]; ring)
    omega
  · obtain ⟨c, m', hc', hm', h⟩ := card_of_shape_SL (Or.inr hs)
    rw [hX] at h
    have := eq_of_two_pow_mul_odd (a := 12) (b := 6) (hc'.mul hm) hm' (by rw [← h]; ring)
    omega
  · obtain ⟨c, m', hc', hm', h⟩ := card_of_shape_Sp hs
    rw [hX] at h
    have := eq_of_two_pow_mul_odd (a := 12) (b := 8) (hc'.mul hm) hm' (by rw [← h]; ring)
    omega
  · rcases hs with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact absurd h (by decide)
    · exact h
    · exact absurd h (by decide)
    · exact absurd h (by decide)

end CFSG.Quasithin.Vol2.Ch11.SecS

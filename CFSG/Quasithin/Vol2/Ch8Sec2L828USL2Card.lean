module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.Quasithin.H13

open scoped MatrixGroups

abbrev ob5SL : Type := Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)

theorem ob5_card_GF16 : Nat.card (GaloisField 2 4) = 16 := by
  rw [GaloisField.card 2 4 (by norm_num)]
  norm_num

theorem ob5_card_SL : Nat.card ob5SL = 4080 := by
  haveI : Fintype (GaloisField 2 4) := Fintype.ofFinite _
  have h16 : Fintype.card (GaloisField 2 4) = 16 := by
    rw [← Nat.card_eq_fintype_card, ob5_card_GF16]
  rw [Matrix.card_SL_field, h16]
  norm_num [Fin.prod_univ_two]

theorem ob5_center_SL : Subgroup.center ob5SL = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hAr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h2 : (2 : GaloisField 2 4) = 0 := CharTwo.two_eq_zero
  have hmul : (r - 1) * (r - 1) = 0 := by
    linear_combination hr - r * h2 + h2
  have hr1 : r = 1 := sub_eq_zero.mp (mul_self_eq_zero.mp hmul)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hAr, hr1]
  simp

noncomputable abbrev ob5Proj : ob5SL →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4) :=
  QuotientGroup.mk' (Subgroup.center ob5SL)

theorem ob5_proj_injective : Function.Injective ob5Proj := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hg' : g ∈ Subgroup.center ob5SL := (QuotientGroup.eq_one_iff g).mp hg
  rw [ob5_center_SL, Subgroup.mem_bot] at hg'
  exact hg'

theorem ob5_proj_surjective : Function.Surjective ob5Proj :=
  QuotientGroup.mk'_surjective _

theorem ob5_card_PSL : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4)) =
    4080 := by
  rw [← ob5_card_SL]
  exact Nat.card_congr (Equiv.ofBijective ob5Proj ⟨ob5_proj_injective, ob5_proj_surjective⟩).symm

theorem ob5_normal_two_SL (N : Subgroup ob5SL) [N.Normal] (hN : IsPGroup 2 N) : N = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : 4 ≤ Nat.card (GaloisField 2 4) := by rw [ob5_card_GF16]; norm_num
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF
  haveI : (N.map ob5Proj).Normal := Subgroup.Normal.map inferInstance ob5Proj ob5_proj_surjective
  rcases Subgroup.Normal.eq_bot_or_eq_top (N.map ob5Proj) with h | h
  · rw [eq_bot_iff]
    intro n hn
    have hmem : ob5Proj n ∈ N.map ob5Proj := Subgroup.mem_map_of_mem ob5Proj hn
    rw [h, Subgroup.mem_bot] at hmem
    have hc : n ∈ Subgroup.center ob5SL := (QuotientGroup.eq_one_iff n).mp hmem
    rw [ob5_center_SL, Subgroup.mem_bot] at hc
    exact Subgroup.mem_bot.mpr hc
  · exfalso
    have hp : IsPGroup 2 (N.map ob5Proj) := hN.map ob5Proj
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hp
    rw [h, Subgroup.card_top, ob5_card_PSL] at hk
    have hk12 : k < 12 := by
      by_contra hc
      push Not at hc
      have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hc
      omega
    interval_cases k <;> norm_num at hk

end CFSG.Quasithin.H13

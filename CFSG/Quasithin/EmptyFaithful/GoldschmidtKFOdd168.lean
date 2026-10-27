module

public import CFSG.Quasithin.Background.DicksonPerfectSL2
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PrimeRecognition
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.Quasithin.SBd19F

open Matrix CFSG.Quasithin.Dickson
open scoped MatrixGroups

theorem false_of_perfect_card_168_sl2 {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {J : Type} [Group J] (e : J ≃* SL(2, ZMod p)) {K : Subgroup J}
    [Group.IsPerfect K] (hcard : Nat.card K = 168) : False := by
  have : Fact p.Prime := ⟨hp⟩
  set K' : Subgroup (SL(2, ZMod p)) := K.map e.toMonoidHom with hK'
  have hperf : Group.IsPerfect K' := Group.IsPerfect.map e.toMonoidHom
  have hc' : Nat.card K' = 168 := by
    rw [hK', Subgroup.card_map_of_injective e.injective, hcard]
  have hne : K' ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hc'
    omega
  rcases perfect_subgroup_sl2_prime hp5 (Subgroup.isPerfect_iff.mp hperf) hne with
    h | ⟨⟨e5⟩, -⟩
  · rw [h, Subgroup.card_top, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
      Nat.card_zmod] at hc'
    have h1 : p * (p ^ 2 - 1) = 168 := hc'
    have h2 : p ≤ 6 := by
      by_contra hlt
      push Not at hlt
      have : 7 * (7 ^ 2 - 1) ≤ p * (p ^ 2 - 1) := Nat.mul_le_mul hlt
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hlt 2) 1)
      omega
    interval_cases p <;> omega
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [Nat.card_congr e5.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
      Nat.card_zmod] at hc'
    omega

theorem eq_seven_of_perfect_card_168_psl2 {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {J : Type} [Group J]
    (e : J ≃* ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) {K : Subgroup J}
    [Group.IsPerfect K] (hcard : Nat.card K = 168) : p = 7 := by
  have : Fact p.Prime := ⟨hp⟩
  set K' : Subgroup (ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) := K.map e.toMonoidHom
    with hK'
  have hperf : Group.IsPerfect K' := Group.IsPerfect.map e.toMonoidHom
  have hc' : Nat.card K' = 168 := by
    rw [hK', Subgroup.card_map_of_injective e.injective, hcard]
  have hne : K' ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hc'
    omega
  rcases CFSG.SectionRank.Ccomm.perfect_PSL2_dichotomy hp2 K' hne with h5 | h
  · obtain ⟨e5⟩ := h5
    rw [Nat.card_congr e5.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup] at hc'
    simp [Nat.factorial] at hc'
  · rw [h, Subgroup.card_top, CFSG.SectionRank.Ccomm.card_PSL2_zmod hp2] at hc'
    have h2 : p ≤ 8 := by
      by_contra hlt
      push Not at hlt
      have : 9 * (9 ^ 2 - 1) ≤ p * (p ^ 2 - 1) := Nat.mul_le_mul hlt
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hlt 2) 1)
      omega
    interval_cases p <;> first | rfl | omega

end CFSG.Quasithin.SBd19F

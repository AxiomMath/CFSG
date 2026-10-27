module

public import CFSG.Quasithin.Background.DicksonPerfectSL2
public import CFSG.Quasithin.Vol2.Ch11SecA02Card
public import CFSG.Quasithin.Vol2.Ch11SecB23Two

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Quasithin.Dickson CFSG.Quasithin.A1c
open scoped MatrixGroups

theorem eq_top_of_perfect_sl2_five
    {K : Subgroup (SL(2, ZMod 5))} (hK : ⁅K, K⁆ = K)
    (hne : K ≠ ⊥) : K = ⊤ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rcases perfect_subgroup_sl2_prime (p := 5) le_rfl hK hne with h | ⟨-, -, h5, -⟩
  · exact h
  · exact absurd rfl h5

theorem eq_bot_of_normal_odd_sl2 {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {N : Subgroup (SL(2, ZMod p))} (hN : N.Normal) (hodd : Odd (Nat.card N)) : N = ⊥ := by
  have hp2 : p ≠ 2 := by omega
  have hneg : sl2NegOne p ∉ N := by
    intro h
    have hord : orderOf (⟨sl2NegOne p, h⟩ : N) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_sl2NegOne hp2
    have hdvd : 2 ∣ Nat.card N := by
      have h1 := orderOf_dvd_natCard (⟨sl2NegOne p, h⟩ : N)
      rwa [hord] at h1
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  rcases normal_le_center_or_eq_top hp5 N with h | h
  · rw [eq_bot_iff]
    intro x hx
    rcases eq_one_or_eq_sl2NegOne_of_mem_center (h hx) with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd hx hneg
  · exact absurd (h ▸ Subgroup.mem_top (sl2NegOne p)) hneg

theorem eq_bot_of_normal_odd_sl2_four {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    {N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)} (hN : N.Normal)
    (hodd : Odd (Nat.card N)) : N = ⊥ := by
  have hF' : Nat.card F = 2 ^ 2 := hF
  have hZ := SecB.center_SL2_eq_bot hF' (by norm_num)
  have hsimple : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hF])
  set π := QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) with hπ
  have hNm : (N.map π).Normal := hN.map π (QuotientGroup.mk'_surjective _)
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · rw [eq_bot_iff]
    intro x hx
    have h1 : π x = 1 := by
      have := Subgroup.mem_map_of_mem π hx
      rwa [h, Subgroup.mem_bot] at this
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hZ] at h1
    exact h1
  · exfalso
    have hNtop : N = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : π x ∈ N.map π := h ▸ Subgroup.mem_top _
      obtain ⟨y, hy, hyx⟩ := hx
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hZ,
        Subgroup.mem_bot, inv_mul_eq_one] at hyx
      exact hyx ▸ hy
    rw [hNtop, Subgroup.card_top, SecA.card_SL_two hF'] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) ⟨2 * SecA.oSL2 2, by ring⟩

end CFSG.Quasithin.Vol2.Ch11.SecE

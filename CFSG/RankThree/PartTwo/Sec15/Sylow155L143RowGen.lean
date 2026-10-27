module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155L143Abs
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155L143

variable {S : Type*} [Group S]

theorem L143Row.of_conj {x : S} (g : S) (h : L143Row (g * x * g⁻¹)) : L143Row x :=
  L143Row.of_mulEquiv (MulAut.conj g) (by simpa [MulAut.conj_apply] using h)

theorem L143Row.of_mem {x : S} (E : Subgroup S) (hxE : x ∈ E)
    (hEc : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e) (hE3 : ∀ e ∈ E, e ^ 3 = 1)
    (hE : 27 ≤ Nat.card E) : L143Row x :=
  Or.inr ⟨E, fun e he => hEc e he x hxE, hEc, hE3, hE⟩

theorem L143Row.of_nine_dvd [Finite S] {x : S} (hx3 : x ^ 3 = 1)
    (h9 : 9 ∣ Nat.card (Subgroup.centralizer ({x} : Set S)))
    (hreal : ∀ y : S, (∃ k : ℕ, y ^ (3 ^ k) = 1) → y ^ 3 = 1 ∧ ∃ g : S, g * y * g⁻¹ = y⁻¹) :
    L143Row x := by
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := Subgroup.centralizer ({x} : Set S))
    3 (n := 2) (by norm_num; exact h9)
  have hHS : Nat.card (H.map (Subgroup.centralizer ({x} : Set S)).subtype) = 9 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hH]
    norm_num
  have hzx : Nat.card (Subgroup.zpowers x) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hx3)
  have hnle : ¬ H.map (Subgroup.centralizer ({x} : Set S)).subtype ≤ Subgroup.zpowers x := by
    intro hle
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨y, hyH, hyx⟩ := Set.not_subset.mp hnle
  obtain ⟨y', hy'H, rfl⟩ := Subgroup.mem_map.mp hyH
  have hy9 : (y' : S) ^ (3 ^ 2) = 1 := by
    have h1 : orderOf y' ∣ 9 := by
      have := Subgroup.orderOf_dvd_natCard H hy'H
      rwa [hH] at this
    have h2 : y' ^ 9 = 1 := orderOf_dvd_iff_pow_eq_one.mp h1
    have h3 : ((y' : S)) ^ 9 = 1 := by rw [← Subgroup.coe_pow, h2, Subgroup.coe_one]
    simpa using h3
  obtain ⟨hy3, g, hg⟩ := hreal _ ⟨2, hy9⟩
  have hcomm : (y' : S) * x = x * y' := by
    have := Subgroup.mem_centralizer_iff.mp y'.2 x (Set.mem_singleton x)
    exact this.symm
  exact Or.inl ⟨y', g, hcomm, hy3, hyx, hg⟩

theorem L143Rows.of_sylow [Finite S] (P : Sylow 3 S)
    (h : ∀ x ∈ (P : Subgroup S), x ^ 3 = 1 → x ≠ 1 → L143Row x) : L143Rows S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x hx3 hx1
  have hpg : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime hx3 hx1)
  obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S Q P
  have hxQ : x ∈ (Q : Subgroup S) := hQ (Subgroup.mem_zpowers x)
  have hgx : g * x * g⁻¹ ∈ (P : Subgroup S) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨x, hxQ, rfl⟩
  refine L143Row.of_conj g (h _ hgx ?_ ?_)
  · rw [conj_pow, hx3, mul_one, mul_inv_cancel]
  · intro h1
    apply hx1
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group

end CFSG.RankThree.PartTwo.Sec15.Sylow155L143

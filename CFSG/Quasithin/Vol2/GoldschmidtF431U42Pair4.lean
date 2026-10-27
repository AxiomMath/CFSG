module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Pair3
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Pair2

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open U42F431
open scoped Pointwise

theorem xY_ne_one : xY ≠ 1 := by
  intro h
  have h1 : x45 = 1 := congrArg Subtype.val h
  have : xL = idL := repL_unique repL_x (by rw [h1]; exact repL_one 45)
  revert this
  decide +kernel

theorem xY_sq : xY * xY = 1 := Subtype.ext x45_mul_self

theorem normalizer_x :
    Subgroup.normalizer ((Subgroup.zpowers xY : Subgroup Y) : Set Y) = P1 := by
  ext g
  rw [mem_P1_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h
    have hx : g * xY * g⁻¹ ∈ Subgroup.zpowers xY := (h xY).1 (Subgroup.mem_zpowers xY)
    have hx2 : g * xY * g⁻¹ = xY := by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hx
      have hord : orderOf xY = 2 := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact orderOf_eq_prime (by rw [pow_two]; exact xY_sq) xY_ne_one
      have hn' : xY ^ n = xY ^ (n % 2) := by
        have := zpow_mod_orderOf xY n
        rw [hord] at this
        simpa using this.symm
      have hm : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases hm with hm | hm
      · exfalso
        rw [hn', hm] at hn
        have : g * xY * g⁻¹ = 1 := by simpa using hn.symm
        have h2 : xY = 1 := by simpa using this
        exact xY_ne_one h2
      · rw [hn', hm] at hn
        simpa using hn.symm
    have hc : (g : P45) * x45 = x45 * (g : P45) := by
      have this : (g : P45) * x45 * (g : P45)⁻¹ = x45 := congrArg Subtype.val hx2
      calc (g : P45) * x45 = (g : P45) * x45 * (g : P45)⁻¹ * g := by group
        _ = x45 * g := by rw [this]
    exact (mem_centralizer_x_iff g.2).1 hc
  · intro hg h
    have hc := (mem_centralizer_x_iff g.2).2 hg
    have hcY : g * xY = xY * g := Subtype.ext hc
    have hconj : g * xY * g⁻¹ = xY := by
      rw [hcY]; simp
    constructor
    · intro hh
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      rw [show g * xY ^ n * g⁻¹ = (g * xY * g⁻¹) ^ n by simp [conj_zpow], hconj]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers xY) n
    · intro hh
      have hconj' : g⁻¹ * xY * g = xY := by
        calc g⁻¹ * xY * g = g⁻¹ * (xY * g) := by rw [mul_assoc]
          _ = g⁻¹ * (g * xY) := by rw [hcY]
          _ = xY := by rw [← mul_assoc]; simp
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hh
      have : h = g⁻¹ * (g * h * g⁻¹) * g := by simp [mul_assoc]
      have hcz : g⁻¹ * xY ^ n * g = (g⁻¹ * xY * g) ^ n := by
        have := conj_zpow (a := g⁻¹) (b := xY) (i := n)
        simpa using this.symm
      rw [this, ← hn, hcz, hconj']
      exact Subgroup.mem_zpowers_iff.2 ⟨n, rfl⟩

theorem sY_conj (g : Y) (p : Fin 45) :
    g * sY p * g⁻¹ = sY ((g : P45) p) := by
  apply Subtype.ext
  exact tau_conj g.2 p

theorem P2_conj_V {g : Y} (hg : g ∈ P2) {h : Y} (hh : h ∈ Vsub) :
    g * h * g⁻¹ ∈ Vsub := by
  refine conj_mem_closure (S := {g | ∃ p : Fin 45, p ∈ L0S ∧ g = sY p}) ?_ hh
  rintro _ ⟨p, hp, rfl⟩
  rw [sY_conj]
  refine Subgroup.subset_closure ⟨(g : P45) p, ?_, rfl⟩
  have h2 := (mem_P2_iff g).1 hg
  rw [← h2]
  exact ⟨p, hp, rfl⟩

theorem normalizer_V :
    Subgroup.normalizer (Vsub : Set Y) = P2 := by
  have hP2 : P2 ≤ Subgroup.normalizer (Vsub : Set Y) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    exact ⟨fun hh => P2_conj_V hg hh, fun hh => by
      have := P2_conj_V (P2.inv_mem hg) hh
      simpa [mul_assoc] using this⟩
  rcases lattice (B0_le_P2.trans hP2) with h | h | h | h
  · exact absurd (B0_le_P1 (h ▸ hP2 D2_mem_P2)) D2_not_mem_P1
  · exact absurd (h ▸ hP2 D2_mem_P2) D2_not_mem_P1
  · exact h
  · exfalso
    have hnorm : Vsub.Normal := Subgroup.normalizer_eq_top_iff.1 h
    exact Vsub_ne_bot (normal_two_group_trivial hnorm Vsub_isPGroup)

theorem P1_isTwoLocal : IsTwoLocal P1 := by
  refine ⟨Subgroup.zpowers xY, ?_, ?_, normalizer_x.symm⟩
  · intro h
    have : xY ∈ Subgroup.zpowers xY := Subgroup.mem_zpowers xY
    rw [h, Subgroup.mem_bot] at this
    exact xY_ne_one this
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hx2 : xY ^ 2 = 1 := by rw [pow_two]; exact xY_sq
    exact IsPGroup.of_card (n := 1) (by
      have := Nat.card_zpowers xY
      rw [this]
      have hord : orderOf xY = 2 := orderOf_eq_prime hx2 xY_ne_one
      rw [hord]; norm_num)

theorem P2_isTwoLocal :
    IsTwoLocal P2 :=
  ⟨Vsub, Vsub_ne_bot, Vsub_isPGroup, normalizer_V.symm⟩

end CFSG.Quasithin.H13.F431.U42

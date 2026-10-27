module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonSmallAlternating

public section

namespace CFSG.Quasithin.Fan86.Sigma3

structure Klein24 (G : Type*) [Group G] [Finite G] (N : Subgroup G) (x t : G) : Prop where
  card : Nat.card G = 24
  normal : N.Normal
  card_N : Nat.card N = 4
  comm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a
  ord : orderOf x = 3
  fix : ∀ n ∈ N, x * n * x⁻¹ = n → n = 1
  sq : t * t = 1
  moved : ∃ n ∈ N, t * n * t⁻¹ ≠ n

namespace Klein24

variable {G : Type*} [Group G] [Finite G] {N : Subgroup G} {x t : G}

theorem exists_ne_one (h : Klein24 G N x t) : ∃ n ∈ N, n ≠ 1 := by
  by_contra hc
  push Not at hc
  have h1 := h.card_N
  rw [(Subgroup.eq_bot_iff_forall N).2 hc, Subgroup.card_bot] at h1
  omega

omit [Finite G] in
theorem conj_of_mem_zpowers {w : G} (hw : w ∈ Subgroup.zpowers x) : x * w * x⁻¹ = w := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  rw [(Commute.self_zpow x m).eq]
  group

theorem zpowers_not_normal (h : Klein24 G N x t) : ¬ (Subgroup.zpowers x).Normal := by
  intro hX
  obtain ⟨n, hn, hn1⟩ := h.exists_ne_one
  refine hn1 (h.fix n hn ?_)
  have h1 : x * n * x⁻¹ * n⁻¹ ∈ Subgroup.zpowers x := by
    have := hX.conj_mem x⁻¹ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)) n
    have e : x * n * x⁻¹ * n⁻¹ = x * (n * x⁻¹ * n⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers x) this
  have h2 : x * n * x⁻¹ * n⁻¹ ∈ N :=
    N.mul_mem (h.normal.conj_mem n hn x) (N.inv_mem hn)
  have h3 := h.fix _ h2 (by simpa using conj_of_mem_zpowers h1)
  exact mul_inv_eq_one.1 h3

theorem card_sylow_three (h : Klein24 G N x t) : Nat.card (Sylow 3 G) = 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, h.ord]
  have hXp : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [hX, pow_one])
  have hidx : (Subgroup.zpowers x).index = 8 := by
    have := Subgroup.card_mul_index (Subgroup.zpowers x)
    rw [hX, h.card] at this
    omega
  let P : Sylow 3 G := hXp.toSylow (by rw [hidx]; decide)
  have hP : (P : Subgroup G) = Subgroup.zpowers x := rfl
  have h1 := P.card_eq_index_normalizer
  have h2 := P.card_dvd_index
  have h3 := card_sylow_modEq_one 3 G
  rw [hP, hidx] at h2
  have h4 : Nat.card (Sylow 3 G) ≠ 1 := by
    intro h5
    apply h.zpowers_not_normal
    rw [← Subgroup.normalizer_eq_top_iff, ← Subgroup.index_eq_one]
    rw [h1] at h5
    exact h5
  have h5 : Nat.card (Sylow 3 G) ≤ 8 := Nat.le_of_dvd (by norm_num) h2
  generalize Nat.card (Sylow 3 G) = n at h2 h3 h4 h5 ⊢
  interval_cases n <;> simp_all [Nat.ModEq]

theorem center_eq_bot (h : Klein24 G N x t) : Subgroup.center G = ⊥ := by
  have := h.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let ρ : G →* MulAut N := MulAut.conjNormal
  have hρ : ∀ (g : G) (m : N), ((ρ g m : N) : G) = g * m * g⁻¹ := fun g m =>
    MulAut.conjNormal_apply g m
  have hker : ∀ g : G, ρ g = 1 ↔ ∀ m ∈ N, g * m * g⁻¹ = m := by
    intro g
    constructor
    · intro hg m hm
      have := hρ g ⟨m, hm⟩
      rw [hg] at this
      exact this.symm
    · intro hg
      ext m
      rw [hρ]
      exact hg m m.2
  have hker_ge : N ≤ ρ.ker := by
    intro n hn
    rw [MonoidHom.mem_ker, hker]
    intro m hm
    rw [mul_inv_eq_iff_eq_mul]
    exact h.comm n hn m hm
  have hx3 : x ^ 3 = 1 := by rw [← h.ord]; exact pow_orderOf_eq_one x
  have ht2 : t ^ 2 = 1 := by rw [pow_two]; exact h.sq
  have hρx : ρ x ≠ 1 := by
    intro h1
    obtain ⟨n, hn, hn1⟩ := h.exists_ne_one
    exact hn1 (h.fix n hn (by simpa using (hker x).1 h1 n hn))
  have hρt : ρ t ≠ 1 := by
    intro h1
    obtain ⟨n, hn, hne⟩ := h.moved
    exact hne ((hker t).1 h1 n hn)
  have h3 : orderOf (ρ x) = 3 := orderOf_eq_prime (by rw [← map_pow, hx3, map_one]) hρx
  have h2 : orderOf (ρ t) = 2 := orderOf_eq_prime (by rw [← map_pow, ht2, map_one]) hρt
  have d3 : 3 ∣ Nat.card ρ.range := h3 ▸ Subgroup.orderOf_dvd_natCard ρ.range ⟨x, rfl⟩
  have d2 : 2 ∣ Nat.card ρ.range := h2 ▸ Subgroup.orderOf_dvd_natCard ρ.range ⟨t, rfl⟩
  have d6 : 6 ∣ Nat.card ρ.range := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d3 d2
  have hpos : 0 < Nat.card ρ.range := Nat.card_pos
  have hprod : 24 = Nat.card ρ.range * Nat.card ρ.ker := by
    rw [← h.card, Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
  have hr6 : 6 ≤ Nat.card ρ.range := Nat.le_of_dvd hpos d6
  have hk4 : Nat.card ρ.ker ≤ 4 := by
    have : 6 * Nat.card ρ.ker ≤ 24 := by
      calc 6 * Nat.card ρ.ker ≤ Nat.card ρ.range * Nat.card ρ.ker :=
            Nat.mul_le_mul_right _ hr6
        _ = 24 := hprod.symm
    omega
  have hNker : N = ρ.ker := Subgroup.eq_of_le_of_card_ge hker_ge (by rw [h.card_N]; exact hk4)
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hzc := Subgroup.mem_center_iff.1 hz
  have hzN : z ∈ N := by
    rw [hNker, MonoidHom.mem_ker, hker]
    intro m _
    rw [mul_inv_eq_iff_eq_mul]
    exact (hzc m).symm
  exact h.fix z hzN (by rw [mul_inv_eq_iff_eq_mul]; exact hzc x)

theorem nonempty_perm_four (h : Klein24 G N x t) : Nonempty (G ≃* Equiv.Perm (Fin 4)) :=
  CFSG.Glauberman.Dickson.huppert_II_8_17_c_order_twenty_four_four_sylow_three h.card
    h.card_sylow_three h.center_eq_bot

end Klein24

end CFSG.Quasithin.Fan86.Sigma3

module

public import CFSG.Walter.ReeOrder.JT.Section4IA
public import CFSG.Walter.ReeOrder.JT.Section7ZA

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

structure L46Data {h : JTHyp G} (c : Config h) where
  L : Subgroup G
  t₂ : G
  M : Subgroup G
  L_cyclic : IsCyclic L
  card_L : Nat.card L = c.toSetup.m
  μ_mem_L : c.μ ∈ L
  L_le : L ≤ Subgroup.centralizer ({c.t₁} : Set G)
  orderOf_t₂ : orderOf t₂ = 2
  comm : t₂ * c.t₁ = c.t₁ * t₂
  ne : t₂ ≠ c.t₁
  inv_L : ∀ x ∈ L, t₂ * x * t₂⁻¹ = x⁻¹
  M_le : M ≤ Subgroup.normalizer (Subgroup.zpowers c.μ : Set G)
  normal : ∀ n ∈ Subgroup.normalizer (Subgroup.zpowers c.μ : Set G),
    n ∈ Subgroup.normalizer (M : Set G)
  odd : Odd (Nat.card M)
  mem : ∀ y ∈ Subgroup.normalizer (Subgroup.zpowers c.μ : Set G), Odd (orderOf y) → y ∈ M
  inf_t₁ : ∀ y ∈ M, y * c.t₁ = c.t₁ * y → y ∈ L

namespace Config

variable {h : JTHyp G} (c : Config h) (hp : h.p ≠ 2) (hp3 : h.p ≠ 3)
  (h3Q : ¬ 3 ∣ Nat.card c.Q)
include hp hp3 h3Q

theorem nonempty_l46Data :
    Nonempty (L46Data c) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hm3 := c.toSetup.three_dvd_m hp hp3 h3Q
  have hmadd := c.toSetup.m_add hp
  have h3 : (h.q % 4 = 3 ∧ 3 ∣ (h.q - 1) / 2) ∨ (h.q % 4 = 1 ∧ 3 ∣ (h.q + 1) / 2) := by
    rcases c.toSetup.four_mul_card_Q_cases hp with ⟨hq4, h4⟩ | ⟨hq4, h4⟩
    · left
      refine ⟨hq4, ?_⟩
      have : (h.q - 1) / 2 = c.toSetup.m := by omega
      rw [this]; exact hm3
    · right
      refine ⟨hq4, ?_⟩
      have : (h.q + 1) / 2 = c.toSetup.m := by omega
      rw [this]; exact hm3
  obtain ⟨L, t₂, hLc, hLcard, hμL, hLt₁, ht₂, ht₂t₁, ht₂ne, hinvL, hLodd⟩ :=
    h.exists_torus_of_orderOf_three hp hp3 c.orderOf_μ c.orderOf_t₁ c.comm h3
  have hLcard' : Nat.card L = c.toSetup.m := by
    rcases hLcard with ⟨hq4, hc⟩ | ⟨hq4, hc⟩ <;>
      rcases c.toSetup.four_mul_card_Q_cases hp with ⟨hq4', h4⟩ | ⟨hq4', h4⟩ <;> omega
  set N₀ := Subgroup.normalizer (Subgroup.zpowers c.μ : Set G) with hN₀def
  have hμ1 : c.μ ≠ 1 := by
    intro h0
    have := c.orderOf_μ
    rw [h0, orderOf_one] at this
    norm_num at this
  have ht₁t₁ : c.t₁ * c.t₁ = 1 := by rw [← pow_two, ← c.orderOf_t₁, pow_orderOf_eq_one]
  have ht₂t₂ : t₂ * t₂ = 1 := by rw [← pow_two, ← ht₂, pow_orderOf_eq_one]
  have ht₁N : c.t₁ ∈ N₀ := mem_normalizer_zpowers_of_commute c.comm.symm
  have ht₂μ : t₂ * c.μ * t₂⁻¹ = c.μ⁻¹ := hinvL c.μ hμL
  have ht₂N : t₂ ∈ N₀ := by
    refine mem_normalizer_of_conj_mem fun z hz => ?_
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← conj_zpow, ht₂μ, inv_zpow']
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
  have ht₁1 : c.t₁ ≠ 1 := by
    intro h0
    have := c.orderOf_t₁
    rw [h0, orderOf_one] at this
    omega
  have ht₂1 : t₂ ≠ 1 := by
    intro h0
    rw [h0, orderOf_one] at ht₂
    omega
  have hct : Commute c.t₁ t₂ := ht₂t₁.symm
  set V := GorensteinWalter.kleinFourOfCommutingInvolutions c.t₁ t₂ ht₁t₁ ht₂t₂ hct with hVdef
  have hV : IsKleinFour V := GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
    _ _ _ _ ht₁1 ht₂1 (Ne.symm ht₂ne) hct
  have hmemV : ∀ y, y ∈ V ↔ y = c.t₁ * t₂ ∨ y = c.t₁ ∨ y = t₂ ∨ y = 1 := fun y => Iff.rfl
  have ht₁V : c.t₁ ∈ V := (hmemV _).mpr (Or.inr (Or.inl rfl))
  have ht₂V : t₂ ∈ V := (hmemV _).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hVN : V ≤ N₀ := fun y hy => by
    rcases (hmemV y).mp hy with rfl | rfl | rfl | rfl
    · exact N₀.mul_mem ht₁N ht₂N
    · exact ht₁N
    · exact ht₂N
    · exact N₀.one_mem
  have h8 : ¬ 8 ∣ Nat.card N₀ := by
    intro h8
    obtain ⟨g, hg⟩ := c.toSetup.exists_conj_le_Q_of_eight_dvd hp
      (by rw [Nat.card_zpowers, c.orderOf_μ]; decide) h8
    apply h3Q
    have := Subgroup.card_dvd_of_le hg
    rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective, Nat.card_zpowers,
      c.orderOf_μ] at this
  have hVcard : Nat.card (V.subgroupOf N₀) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN).toEquiv, hV.card_four]
  have hfacN : (Nat.card N₀).factorization 2 = 2 := by
    have h4 : 2 ^ 2 ∣ Nat.card N₀ := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hV.card_four]
      exact Subgroup.card_dvd_of_le hVN
    have h8' : ¬ 2 ^ 3 ∣ Nat.card N₀ := by norm_num; exact h8
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne'] at h4 h8'
    omega
  let VS : Sylow 2 N₀ := Sylow.ofCard (V.subgroupOf N₀) (by rw [hVcard, hfacN]; norm_num)
  have hVS : IsKleinFour (VS : Subgroup N₀) := by
    have e : (V.subgroupOf N₀) ≃* V := Subgroup.subgroupOfEquivOfLe hVN
    exact ⟨hVcard, by
      change Monoid.exponent (V.subgroupOf N₀) = 2
      rw [Monoid.exponent_eq_of_mulEquiv e, hV.exponent_two]⟩
  have hnc : ∀ g : N₀, g * ⟨c.t₁, ht₁N⟩ * g⁻¹ ≠ ⟨t₂, ht₂N⟩ := by
    intro g hg
    have hg' : (g : G) * c.t₁ * (g : G)⁻¹ = t₂ := congrArg Subtype.val hg
    have hgμ : (g : G) * c.μ * (g : G)⁻¹ ∈ Subgroup.zpowers c.μ :=
      (Subgroup.mem_normalizer_iff.mp g.2 c.μ).mp (Subgroup.mem_zpowers c.μ)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hgμ
    have hc : t₂ * ((g : G) * c.μ * (g : G)⁻¹) = ((g : G) * c.μ * (g : G)⁻¹) * t₂ := by
      rw [← hg']
      calc (g : G) * c.t₁ * (g : G)⁻¹ * ((g : G) * c.μ * (g : G)⁻¹) =
          (g : G) * (c.t₁ * c.μ) * (g : G)⁻¹ := by group
        _ = (g : G) * (c.μ * c.t₁) * (g : G)⁻¹ := by rw [c.comm]
        _ = ((g : G) * c.μ * (g : G)⁻¹) * ((g : G) * c.t₁ * (g : G)⁻¹) := by group
    rw [← hk] at hc
    have hko : orderOf (c.μ ^ k) = 3 := by
      rw [hk, ← MulAut.conj_apply, MulEquiv.orderOf_eq, c.orderOf_μ]
    have hμmem : c.μ ∈ Subgroup.zpowers (c.μ ^ k) := by
      have hle : Subgroup.zpowers (c.μ ^ k) ≤ Subgroup.zpowers c.μ :=
        (Subgroup.zpowers_le).mpr (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _)
      have heq := Subgroup.eq_of_le_of_card_ge hle (by
        rw [Nat.card_zpowers, Nat.card_zpowers, hko, c.orderOf_μ])
      rw [heq]
      exact Subgroup.mem_zpowers _
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hμmem
    have hc' : t₂ * c.μ = c.μ * t₂ := by
      rw [← hj]
      exact ((Commute.zpow_right (hc : Commute t₂ (c.μ ^ k)) j)).eq
    have hμμ : c.μ = c.μ⁻¹ := by
      rw [← ht₂μ, hc', mul_inv_cancel_right]
    have h2 : orderOf c.μ ∣ 2 := orderOf_dvd_of_pow_eq_one (by
      rw [pow_two]; nth_rewrite 2 [hμμ]; exact mul_inv_cancel _)
    rw [c.orderOf_μ] at h2
    norm_num at h2
  obtain ⟨M, hMn, hModd, hMcard⟩ := exists_normal_odd_of_kleinFour_sylow VS hVS
    (u := ⟨c.t₁, ht₁N⟩) (w := ⟨t₂, ht₂N⟩) (by
      change (⟨c.t₁, ht₁N⟩ : N₀) ∈ V.subgroupOf N₀
      rw [Subgroup.mem_subgroupOf]; exact ht₁V)
    (by change (⟨t₂, ht₂N⟩ : N₀) ∈ V.subgroupOf N₀; rw [Subgroup.mem_subgroupOf]; exact ht₂V)
    (fun h0 => ht₁1 (congrArg Subtype.val h0)) (fun h0 => ht₂1 (congrArg Subtype.val h0)) hnc
  set MG := M.map N₀.subtype with hMGdef
  have hMGcard : Nat.card MG = Nat.card M := Subgroup.card_map_of_injective N₀.subtype_injective
  have hMidx : M.index = 4 := by
    have h1 := M.card_mul_index
    rw [hMcard] at h1
    have : 0 < Nat.card M := Nat.card_pos
    nlinarith
  have hmem : ∀ y ∈ N₀, Odd (orderOf y) → y ∈ MG := by
    intro y hyN hyodd
    have h4 : (⟨y, hyN⟩ : N₀) ^ 4 ∈ M := by
      have := Subgroup.pow_index_mem M (⟨y, hyN⟩ : N₀)
      rwa [hMidx] at this
    have h1 : (⟨y, hyN⟩ : N₀) ^ orderOf y ∈ M := by
      have : (⟨y, hyN⟩ : N₀) ^ orderOf y = 1 :=
        Subtype.ext (by simp [pow_orderOf_eq_one])
      rw [this]
      exact M.one_mem
    have hcop : Nat.Coprime 4 (orderOf y) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hyodd)
    exact ⟨⟨y, hyN⟩, mem_of_pow_mem_of_coprime h4 h1 hcop, rfl⟩
  refine ⟨⟨L, t₂, MG, hLc, hLcard', hμL, hLt₁, ht₂, ht₂t₁, ht₂ne, hinvL,
    Subgroup.map_subtype_le _, ?_, hMGcard ▸ hModd, hmem, ?_⟩⟩
  · intro n hn
    have hmem' : (⟨n, hn⟩ : N₀) ∈ Subgroup.normalizer (M : Set N₀) := by
      have := hMn
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top _
    exact Subgroup.le_normalizer_map N₀.subtype ⟨⟨n, hn⟩, hmem', rfl⟩
  · intro y hyM hyt₁
    have hyN : y ∈ N₀ := Subgroup.map_subtype_le _ hyM
    have hyodd : Odd (orderOf y) := Odd.of_dvd_nat (hMGcard ▸ hModd)
      (Subgroup.orderOf_dvd_natCard MG hyM)
    exact hLodd y (Subgroup.mem_centralizer_singleton_iff.mpr hyt₁) hyN hyodd

end Config

end CFSG.Walter.JT

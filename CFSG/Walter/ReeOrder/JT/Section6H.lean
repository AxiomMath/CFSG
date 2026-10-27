module

public import CFSG.Walter.ReeOrder.JT.Section6G
public import CFSG.Walter.ReeOrder.JT.Section6F

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

namespace BorelData

variable {h : JTHyp G} {b : BorelData h}

namespace M1Data

variable (d : b.M1Data) (hp : h.p ≠ 2) (hq5 : h.q % 8 = 5) (hp3 : h.p ≠ 3)
  (hq3 : h.q % 3 = 2) (hS : SuzukiFourGroupTheorem) (hH : HuppertMetacyclicTheorem)
include d hp hq5 hp3 hq3 hS hH

theorem false :
    False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨μ, hμ3, -, hμT, x, hxP, hx1, hxμ⟩ := d.exists_orderOf_three hp hq5 hp3 hq3
  obtain ⟨s, hsT⟩ := b.exists_setup
  obtain ⟨c, rfl⟩ := s.exists_config hp
  have h3Q := c.toSetup.lemma_4_5 hp hS hH
  obtain ⟨D⟩ := c.nonempty_l46Data hp hp3 h3Q
  set NT := Subgroup.normalizer (b.T : Set G) with hNTdef
  have hNTcard : Nat.card NT = 24 * Nat.card b.C := by
    rw [hNTdef, ← hsT, c.toSetup.card_normalizer_T hp, b.Q_eq hp hq5 hsT]
  have h3C : ¬ 3 ∣ Nat.card b.C := by
    have := b.card_C
    omega
  have hfac : (Nat.card NT).factorization 3 = 1 := by
    have h1 : 3 ^ 1 ∣ Nat.card NT := by rw [hNTcard]; omega
    have h2 : ¬ 3 ^ 2 ∣ Nat.card NT := by rw [hNTcard]; omega
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne'] at h1 h2
    omega
  have hμ₀NT : c.μ ∈ NT := by rw [hNTdef, ← hsT]; exact c.μ_mem_NT
  have hcard3 : ∀ {z : G} (hz : z ∈ NT), orderOf z = 3 →
      Nat.card ((Subgroup.zpowers z).subgroupOf NT) = 3 ^ (Nat.card NT).factorization 3 := by
    intro z hz hz3
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe ((Subgroup.zpowers_le).mpr hz)).toEquiv,
      Nat.card_zpowers, hz3, hfac, pow_one]
  let S₁ : Sylow 3 NT := Sylow.ofCard _ (hcard3 hμT hμ3)
  let S₂ : Sylow 3 NT := Sylow.ofCard _ (hcard3 hμ₀NT c.orderOf_μ)
  have hS₁ : (S₁ : Subgroup NT) = (Subgroup.zpowers μ).subgroupOf NT := Sylow.coe_ofCard _ _
  have hS₂ : (S₂ : Subgroup NT) = (Subgroup.zpowers c.μ).subgroupOf NT := Sylow.coe_ofCard _ _
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq NT S₁ S₂
  have hν : (n : G) * μ * (n : G)⁻¹ ∈ Subgroup.zpowers c.μ := by
    have hmem : n * ⟨μ, hμT⟩ * n⁻¹ ∈ (S₂ : Subgroup NT) := by
      rw [← hn, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      refine ⟨⟨μ, hμT⟩, ?_, rfl⟩
      rw [hS₁]
      exact Subgroup.mem_zpowers μ
    rw [hS₂, Subgroup.mem_subgroupOf] at hmem
    simpa using hmem
  set ν := (n : G) * μ * (n : G)⁻¹ with hνdef
  have hν3 : orderOf ν = 3 := by rw [hνdef, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hμ3]
  have hμ₀ν : c.μ ∈ Subgroup.zpowers ν := by
    have heq := Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hν) (by
      rw [Nat.card_zpowers, Nat.card_zpowers, hν3, c.orderOf_μ])
    rw [heq]
    exact Subgroup.mem_zpowers _
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hμ₀ν
  set x' := (n : G) * x * (n : G)⁻¹ with hx'def
  have hx'ν : x' * ν = ν * x' := by
    rw [hx'def, hνdef]
    calc (n : G) * x * (n : G)⁻¹ * ((n : G) * μ * (n : G)⁻¹) = (n : G) * (x * μ) * (n : G)⁻¹ := by
          group
      _ = (n : G) * (μ * x) * (n : G)⁻¹ := by rw [hxμ]
      _ = (n : G) * μ * (n : G)⁻¹ * ((n : G) * x * (n : G)⁻¹) := by group
  have hx'μ₀ : x' * c.μ = c.μ * x' := by
    rw [← hj]
    exact ((Commute.zpow_right (hx'ν : Commute x' ν) j)).eq
  have hx'1 : x' ≠ 1 := by
    rw [hx'def]
    intro h0
    apply hx1
    have := congrArg (fun z => (n : G)⁻¹ * z * (n : G)) h0
    simpa [mul_assoc] using this
  obtain ⟨k, hk⟩ := d.isPGroup ⟨x, hxP⟩
  have hxk : x ^ h.p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hx'k : x' ^ h.p ^ k = 1 := by rw [hx'def, conj_pow, hxk, mul_one, mul_inv_cancel]
  have hpodd : Odd (orderOf x') := Odd.of_dvd_nat ((Fact.out : h.p.Prime).odd_of_ne_two hp).pow
    (orderOf_dvd_of_pow_eq_one hx'k)
  have hx'M : x' ∈ D.M := D.mem x' (mem_normalizer_zpowers_of_commute hx'μ₀) hpodd
  have hpx' : h.p ∣ orderOf x' := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow (Fact.out : h.p.Prime)).mp
      (orderOf_dvd_of_pow_eq_one hx'k)
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hi
      exact hx'1 (orderOf_eq_one_iff.mp hi)
    rw [hi]
    exact dvd_pow_self _ hi0
  have hpM : h.p ∣ Nat.card D.M := hpx'.trans (Subgroup.orderOf_dvd_natCard _ hx'M)
  have ht₁t₁ : c.t₁ * c.t₁ = 1 := by rw [← pow_two, ← c.orderOf_t₁, pow_orderOf_eq_one]
  have ht₂t₂ : D.t₂ * D.t₂ = 1 := by rw [← pow_two, ← D.orderOf_t₂, pow_orderOf_eq_one]
  have ht₁1 : c.t₁ ≠ 1 := by
    intro h0
    have := c.orderOf_t₁
    rw [h0, orderOf_one] at this
    omega
  have ht₂1 : D.t₂ ≠ 1 := by
    intro h0
    have := D.orderOf_t₂
    rw [h0, orderOf_one] at this
    omega
  have hBW := card_mul_card_sq_eq_mul ht₁t₁ ht₂t₂ ht₁1 ht₂1 (Ne.symm D.ne) D.comm.symm D.M
    D.t₁_mem_normalizer D.t₂_mem_normalizer D.odd
  have hMt₁ : D.M ⊓ Subgroup.centralizer ({c.t₁} : Set G) = D.L :=
    le_antisymm (fun y hy => D.inf_t₁ y hy.1 (Subgroup.mem_centralizer_singleton_iff.mp hy.2))
      (le_inf (D.L_le_M hp) D.L_le)
  have hMT : D.M ⊓ Subgroup.centralizer ({c.t₁} : Set G) ⊓
      Subgroup.centralizer ({D.t₂} : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    exact Subgroup.mem_bot.mpr (D.eq_one_of_commute (Or.inl rfl) hy.1.1
      (Subgroup.mem_centralizer_singleton_iff.mp hy.1.2)
      (Subgroup.mem_centralizer_singleton_iff.mp hy.2))
  rw [hMT, Subgroup.card_bot, one_pow, mul_one, hMt₁, D.card_L] at hBW
  have hmp : Nat.Coprime h.p c.toSetup.m := by
    refine (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr fun hpm => ?_
    have hq := c.toSetup.m_add hp
    have hpq : h.p ∣ h.q := by rw [JTHyp.q_eq]; exact dvd_pow_self _ h.f_pos
    have h2Q : h.p ∣ 2 * Nat.card c.Q := (Nat.dvd_add_right hpm).mp (by rw [hq]; exact hpq)
    have : h.p ∣ Nat.card c.Q := ((Nat.Prime.dvd_mul Fact.out).mp h2Q).resolve_left
      (fun h2 => hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h2))
    exact c.toSetup.not_dvd_card_Q hp this
  have hpu : h.p ∣ Nat.card (D.M ⊓ Subgroup.centralizer ({D.t₂} : Set G) : Subgroup G) *
      Nat.card (D.M ⊓ Subgroup.centralizer ({c.t₁ * D.t₂} : Set G) : Subgroup G) := by
    have : h.p ∣ c.toSetup.m * (Nat.card (D.M ⊓ Subgroup.centralizer ({D.t₂} : Set G) :
        Subgroup G) * Nat.card (D.M ⊓ Subgroup.centralizer ({c.t₁ * D.t₂} : Set G) :
        Subgroup G)) := by
      rw [← mul_assoc, ← hBW]
      exact hpM
    exact hmp.dvd_of_dvd_mul_left this
  obtain ⟨u, hu, hpu'⟩ : ∃ u : G, (u = D.t₂ ∨ u = c.t₁ * D.t₂) ∧
      h.p ∣ Nat.card (D.M ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) := by
    rcases (Nat.Prime.dvd_mul Fact.out).mp hpu with h1 | h1
    · exact ⟨D.t₂, Or.inl rfl, h1⟩
    · exact ⟨c.t₁ * D.t₂, Or.inr rfl, h1⟩
  obtain ⟨⟨d₀, hd₀⟩, hd₀o⟩ := exists_prime_orderOf_dvd_card' h.p hpu'
  rw [Subgroup.orderOf_mk] at hd₀o
  obtain ⟨huu, -, hu1, -, -, -⟩ := D.inv_props hu
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact huu) hu1
  have hD₀u : Subgroup.zpowers d₀ ≤ Subgroup.centralizer ({u} : Set G) :=
    (Subgroup.zpowers_le).mpr hd₀.2
  have hD₀p : IsPGroup h.p (Subgroup.zpowers d₀) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hd₀o, pow_one] :
      Nat.card (Subgroup.zpowers d₀) = h.p ^ 1)
  have hD₀1 : Subgroup.zpowers d₀ ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    intro h0
    rw [h0, orderOf_one] at hd₀o
    exact (Fact.out : h.p.Prime).one_lt.ne hd₀o
  have hμ₀D₀ : c.μ ∈ Subgroup.normalizer (Subgroup.zpowers d₀ : Set G) :=
    mem_normalizer_zpowers_of_commute (D.commute_μ hd₀.1).symm
  exact d.not_mem_normalizer hp hq5 hp3 hq3 hu2 hD₀u hD₀p hD₀1 c.orderOf_μ hμ₀D₀

end M1Data

end BorelData

namespace JTHyp

variable (h : JTHyp G)

theorem p_eq_three_of_cube_dvd
    (hp : h.p ≠ 2) (hS : SuzukiFourGroupTheorem)
    (hH : HuppertMetacyclicTheorem) (h51 : h.p ≠ 3 → h.q ^ 3 ∣ Nat.card G) : h.p = 3 := by
  by_contra hp3
  have hq5 := h.lemma_4_6_c hp hp3 hS hH
  have hq3 := h.q_mod_three hp hp3 hS hH
  obtain ⟨b⟩ := h.nonempty_borelData hp hq5
  obtain ⟨d⟩ := b.nonempty_m1Data hp hq5 hp3 (h51 hp3)
  exact d.false hp hq5 hp3 hq3 hS hH

end JTHyp

end CFSG.Walter.JT

module

public import CFSG.Walter.ReeOrder.JT.Section4I
public import CFSG.Walter.ReeOrder.JT.PSL2Torus
public import CFSG.Walter.ReeOrder.JT.Section4H

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

namespace Setup

variable {h : JTHyp G} (s : Setup h)

@[expose] noncomputable def m : ℕ := h.q - 2 * Nat.card s.Q

variable (hp : h.p ≠ 2)
include hp

theorem four_mul_card_Q_cases :
    (h.q % 4 = 3 ∧ 4 * Nat.card s.Q = h.q + 1) ∨ (h.q % 4 = 1 ∧ 4 * Nat.card s.Q + 1 = h.q) := by
  have h4 := s.four_mul_card_Q hp
  have hq8 := h.mod_eight hp
  unfold JTHyp.eps at h4
  by_cases hq4 : h.q % 4 = 3
  · left
    simp only [hq4, ↓reduceIte] at h4
    exact ⟨hq4, by exact_mod_cast h4⟩
  · right
    simp only [hq4, ↓reduceIte] at h4
    refine ⟨by omega, ?_⟩
    have : (4 * Nat.card s.Q : ℤ) + 1 = h.q := by linarith
    exact_mod_cast this

theorem m_add :
    s.m + 2 * Nat.card s.Q = h.q := by
  have := s.four_mul_card_Q_cases hp
  unfold m
  omega

theorem tori_cases :
    ((h.q - 1) / 2 = s.m ∧ (h.q + 1) / 2 = 2 * Nat.card s.Q) ∨
      ((h.q - 1) / 2 = 2 * Nat.card s.Q ∧ (h.q + 1) / 2 = s.m) := by
  have := s.four_mul_card_Q_cases hp
  unfold m
  omega

theorem odd_m : Odd s.m := by
  have h1 := s.m_add hp
  have h2 := s.odd_card_Q hp
  have hqodd : Odd h.q := by
    rw [JTHyp.q_eq]
    exact ((Fact.out : h.p.Prime).odd_of_ne_two hp).pow
  obtain ⟨a, ha⟩ := h2
  obtain ⟨b, hb⟩ := hqodd
  exact ⟨b - 2 * a - 1, by omega⟩

theorem not_dvd_card_Q :
    ¬ h.p ∣ Nat.card s.Q := by
  intro hpQ
  have hf := h.f_pos
  have hpq : h.p ∣ h.q := by rw [JTHyp.q_eq]; exact dvd_pow_self _ hf
  have := s.four_mul_card_Q_cases hp
  have hp1 := (Fact.out : h.p.Prime).two_le
  rcases this with ⟨-, h4⟩ | ⟨-, h4⟩
  · have h1 : h.p ∣ h.q + 1 := h4 ▸ Dvd.dvd.mul_left hpQ 4
    have := (Nat.dvd_add_right hpq).mp h1
    have := Nat.le_of_dvd (by norm_num) this
    omega
  · have h1 : h.p ∣ 4 * Nat.card s.Q + 1 := h4 ▸ hpq
    have := (Nat.dvd_add_right (Dvd.dvd.mul_left hpQ 4)).mp h1
    have := Nat.le_of_dvd (by norm_num) this
    omega

theorem coprime_m_card_Q :
    Nat.Coprime s.m (Nat.card s.Q) := by
  refine Nat.coprime_of_dvd fun r hr hrm hrQ => ?_
  have h1 := s.m_add hp
  have hrq : r ∣ h.q := h1 ▸ Nat.dvd_add hrm (Dvd.dvd.mul_left hrQ 2)
  rw [JTHyp.q_eq] at hrq
  have hrp : r = h.p := (Nat.prime_dvd_prime_iff_eq hr (Fact.out : h.p.Prime)).mp
    (hr.dvd_of_dvd_pow hrq)
  exact s.not_dvd_card_Q hp (hrp ▸ hrQ)

variable (hp3 : h.p ≠ 3) (h3Q : ¬ 3 ∣ Nat.card s.Q)
include hp3 h3Q

theorem three_dvd_m : 3 ∣ s.m := by
  have h1 := s.m_add hp
  have hq3 : ¬ 3 ∣ h.q := by
    intro h3
    rw [JTHyp.q_eq] at h3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out : h.p.Prime)).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  have h4 := s.four_mul_card_Q_cases hp
  have hQ : Nat.card s.Q % 3 = 1 ∨ Nat.card s.Q % 3 = 2 := by omega
  rcases h4 with ⟨-, h4⟩ | ⟨-, h4⟩ <;> rcases hQ with hQ | hQ <;> omega

theorem nine_le_m : 9 ≤ s.m := by
  have h1 := s.m_add hp
  have h3 := s.three_dvd_m hp hp3 h3Q
  have hodd := s.odd_m hp
  have hq5 := h.five_lt
  rw [← JTHyp.q_eq] at hq5
  have hq8 := h.mod_eight hp
  have := s.four_mul_card_Q_cases hp
  obtain ⟨k, hk⟩ := h3
  obtain ⟨j, hj⟩ := hodd
  by_contra hlt
  have : s.m = 3 := by omega
  omega

end Setup

namespace JTHyp

variable (h : JTHyp G)

theorem exists_torus_of_orderOf_three
    (hp : h.p ≠ 2) (hp3 : h.p ≠ 3) {μ u : G}
    (hμ : orderOf μ = 3)
    (hu : orderOf u = 2) (hμu : μ * u = u * μ)
    (h3 : (h.q % 4 = 3 ∧ 3 ∣ (h.q - 1) / 2) ∨ (h.q % 4 = 1 ∧ 3 ∣ (h.q + 1) / 2)) :
    ∃ L : Subgroup G, ∃ t₂ : G, IsCyclic L ∧
      ((h.q % 4 = 3 ∧ 2 * Nat.card L + 1 = h.q) ∨ (h.q % 4 = 1 ∧ 2 * Nat.card L = h.q + 1)) ∧
      μ ∈ L ∧ L ≤ Subgroup.centralizer ({u} : Set G) ∧ orderOf t₂ = 2 ∧ t₂ * u = u * t₂ ∧
      t₂ ≠ u ∧ (∀ x ∈ L, t₂ * x * t₂⁻¹ = x⁻¹) ∧
      ∀ y ∈ Subgroup.centralizer ({u} : Set G),
        y ∈ Subgroup.normalizer (Subgroup.zpowers μ : Set G) → Odd (orderOf y) → y ∈ L := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := h.exists_conj_eq_t hp hu
  set μ₁ := g * μ * g⁻¹ with hμ₁def
  have hμ₁3 : orderOf μ₁ = 3 := by rw [hμ₁def, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hμ]
  have hμ₁t : μ₁ ∈ Subgroup.centralizer ({h.t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hg, hμ₁def]
    calc g * μ * g⁻¹ * (g * u * g⁻¹) = g * (μ * u) * g⁻¹ := by group
      _ = g * (u * μ) * g⁻¹ := by rw [hμu]
      _ = g * u * g⁻¹ * (g * μ * g⁻¹) := by group
  have hμ₁F : μ₁ ∈ h.F := h.mem_F_of_odd hμ₁t (by rw [hμ₁3]; decide)
  obtain ⟨U, w, hU, hUcard⟩ := (h.facts hp).odd_torus
  rw [← JTHyp.q_eq] at hUcard
  have h3U : 3 ∣ Nat.card U := by
    rcases hUcard with ⟨hq4, hc⟩ | ⟨hq4, hc⟩ <;> rcases h3 with ⟨hq4', h3'⟩ | ⟨hq4', h3'⟩
    · have : (h.q - 1) / 2 = Nat.card U := by omega
      rwa [this] at h3'
    · omega
    · omega
    · have : (h.q + 1) / 2 = Nat.card U := by omega
      rwa [this] at h3'
  obtain ⟨⟨u₃, hu₃U⟩, hu₃⟩ := exists_prime_orderOf_dvd_card' (G := U) 3 h3U
  have hu₃o : orderOf u₃ = 3 := by rw [← hu₃, Subgroup.orderOf_mk]
  have hu₃F : u₃ ∈ h.F := hU.le hu₃U
  obtain ⟨f, hfF, hf⟩ : ∃ f ∈ h.F, f * μ₁ * f⁻¹ ∈ Subgroup.zpowers u₃ := by
    have h3F : ∀ x : h.F, orderOf (x : G) = 3 →
        IsPGroup 3 (Subgroup.zpowers x) := fun x hx =>
      IsPGroup.of_card (by rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, hx, pow_one] :
        Nat.card (Subgroup.zpowers x) = 3 ^ 1)
    obtain ⟨S₁, hS₁⟩ := (h3F ⟨μ₁, hμ₁F⟩ hμ₁3).exists_le_sylow
    obtain ⟨S₂, hS₂⟩ := (h3F ⟨u₃, hu₃F⟩ hu₃o).exists_le_sylow
    obtain ⟨k, hk⟩ := MulAction.exists_smul_eq h.F S₁ S₂
    have hcyc : IsCyclic (S₂ : Subgroup h.F) := by
      have hc := (h.facts hp).cyclic 3 Nat.prime_three (by norm_num) (Ne.symm hp3)
        ((S₂ : Subgroup h.F).map h.F.subtype) (Subgroup.map_subtype_le _)
        (S₂.isPGroup'.map _)
      exact isCyclic_of_surjective
        ((S₂ : Subgroup h.F).equivMapOfInjective _ h.F.subtype_injective).symm.toMonoidHom
        (MulEquiv.surjective _)
    have hkμ : k * ⟨μ₁, hμ₁F⟩ * k⁻¹ ∈ (S₂ : Subgroup h.F) := by
      rw [← hk, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact ⟨_, hS₁ (Subgroup.mem_zpowers _), rfl⟩
    have heq := eq_of_le_of_isCyclic hcyc ((Subgroup.zpowers_le).mpr hkμ)
      (hS₂.trans le_rfl) (by
        rw [Nat.card_zpowers, Nat.card_zpowers, ← MulAut.conj_apply, MulEquiv.orderOf_eq,
          ← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe, hμ₁3, hu₃o])
    have hmem : k * ⟨μ₁, hμ₁F⟩ * k⁻¹ ∈ Subgroup.zpowers (⟨u₃, hu₃F⟩ : h.F) :=
      heq ▸ Subgroup.mem_zpowers _
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine ⟨k, k.2, Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩⟩
    have := congrArg Subtype.val hj
    simpa using this
  have hL₁ := hU.conj (h.F.inv_mem hfF)
  set L₁ := U.map (MulAut.conj f⁻¹).toMonoidHom with hL₁def
  set w₁ := f⁻¹ * w * f⁻¹⁻¹ with hw₁def
  have hμ₁L₁ : μ₁ ∈ L₁ := by
    refine ⟨f * μ₁ * f⁻¹, (Subgroup.zpowers_le.mpr hu₃U) hf, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  refine ⟨L₁.map (MulAut.conj g⁻¹).toMonoidHom, g⁻¹ * w₁ * g, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hL₁.cyclic
    exact isCyclic_of_surjective (L₁.equivMapOfInjective _ (MulAut.conj g⁻¹).injective).toMonoidHom
      (MulEquiv.surjective _)
  · rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective,
      Subgroup.card_map_of_injective (MulAut.conj f⁻¹).injective]
    exact hUcard
  · refine ⟨μ₁, hμ₁L₁, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hμ₁def]
    group
  · rintro _ ⟨x, hx, rfl⟩
    have hxt := h.commute_of_mem_F (hL₁.le hx)
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hu' : u = g⁻¹ * h.t * g := by rw [← hg]; group
    rw [hu']
    calc g⁻¹ * x * g * (g⁻¹ * h.t * g) = g⁻¹ * (x * h.t) * g := by group
      _ = g⁻¹ * (h.t * x) * g := by rw [hxt]
      _ = g⁻¹ * h.t * g * (g⁻¹ * x * g) := by group
  · have hw₁o : orderOf w₁ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hL₁.w_mul_self)
      (fun h0 => hL₁.w_not_mem (h0 ▸ L₁.one_mem))
    rw [show g⁻¹ * w₁ * g = g⁻¹ * w₁ * g⁻¹⁻¹ by rw [inv_inv], ← MulAut.conj_apply,
      MulEquiv.orderOf_eq, hw₁o]
  · have hw₁t := h.commute_of_mem_F hL₁.w_mem
    have hu' : u = g⁻¹ * h.t * g := by rw [← hg]; group
    rw [hu']
    calc g⁻¹ * w₁ * g * (g⁻¹ * h.t * g) = g⁻¹ * (w₁ * h.t) * g := by group
      _ = g⁻¹ * (h.t * w₁) * g := by rw [hw₁t]
      _ = g⁻¹ * h.t * g * (g⁻¹ * w₁ * g) := by group
  · intro h0
    apply h.t_not_mem
    have : h.t = w₁ := by
      calc h.t = g * u * g⁻¹ := hg.symm
        _ = g * (g⁻¹ * w₁ * g) * g⁻¹ := by rw [h0]
        _ = w₁ := by group
    rw [this]
    exact hL₁.w_mem
  · rintro _ ⟨x, hx, rfl⟩
    have := hL₁.inv x hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * w₁ * g * (g⁻¹ * x * g) * (g⁻¹ * w₁ * g)⁻¹ = g⁻¹ * (w₁ * x * w₁⁻¹) * g := by
          group
      _ = (g⁻¹ * x * g)⁻¹ := by rw [this]; group
  · intro y hyu hyN hyodd
    set y₁ := g * y * g⁻¹ with hy₁def
    have hy₁t : y₁ ∈ Subgroup.centralizer ({h.t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hg, hy₁def]
      have hyu' := Subgroup.mem_centralizer_singleton_iff.mp hyu
      calc g * y * g⁻¹ * (g * u * g⁻¹) = g * (y * u) * g⁻¹ := by group
        _ = g * (u * y) * g⁻¹ := by rw [hyu']
        _ = g * u * g⁻¹ * (g * y * g⁻¹) := by group
    have hy₁o : orderOf y₁ = orderOf y := by
      rw [hy₁def, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    have hy₁F : y₁ ∈ h.F := h.mem_F_of_odd hy₁t (hy₁o ▸ hyodd)
    have hy₁N : y₁ ∈ Subgroup.normalizer (Subgroup.zpowers μ₁ : Set G) := by
      refine mem_normalizer_of_conj_mem fun z hz => ?_
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have h1 := (Subgroup.mem_normalizer_iff.mp hyN μ).mp (Subgroup.mem_zpowers μ)
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h1
      refine Subgroup.mem_zpowers_iff.mpr ⟨i * j, ?_⟩
      calc μ₁ ^ (i * j) = g * (μ ^ i) ^ j * g⁻¹ := by rw [hμ₁def, conj_zpow, zpow_mul]
        _ = g * (y * μ * y⁻¹) ^ j * g⁻¹ := by rw [hi]
        _ = g * (y * μ ^ j * y⁻¹) * g⁻¹ := by rw [conj_zpow]
        _ = y₁ * μ₁ ^ j * y₁⁻¹ := by rw [hy₁def, hμ₁def, conj_zpow]; group
    have hR : Subgroup.zpowers μ₁ ≤ L₁ := (Subgroup.zpowers_le).mpr hμ₁L₁
    have hR1 : Subgroup.zpowers μ₁ ≠ ⊥ := by
      rw [Ne, Subgroup.zpowers_eq_bot]
      intro h0
      rw [h0, orderOf_one] at hμ₁3
      norm_num at hμ₁3
    have hmem : y₁ ∈ h.F ⊓ Subgroup.normalizer ((Subgroup.zpowers μ₁ : Subgroup G) : Set G) :=
      ⟨hy₁F, hy₁N⟩
    rw [hL₁.normalizer _ hR hR1] at hmem
    have hy₁L₁ : y₁ ∈ L₁ := by
      rcases hL₁.mem_sup_iff.mp hmem with h1 | h1
      · exact h1
      · have h2 := hL₁.mul_self_of_mul_mem h1
        have h3 : orderOf y₁ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
        have hodd' := hy₁o ▸ hyodd
        have h4 : orderOf y₁ = 1 := by
          rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h5 | h5
          · exact h5
          · rw [h5] at hodd'
            exact absurd hodd' (by decide)
        rw [orderOf_eq_one_iff.mp h4]
        exact L₁.one_mem
    refine ⟨y₁, hy₁L₁, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hy₁def]
    group

end JTHyp

end CFSG.Walter.JT

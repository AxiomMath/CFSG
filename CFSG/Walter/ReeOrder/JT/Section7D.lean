module

public import CFSG.Walter.ReeOrder.JT.Ward
public import CFSG.Assembly.Defs
public import CFSG.Walter.ReeOrder.JT.PSL2Torus

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups

namespace JTHyp

variable {G : Type} [Group G] [Finite G] (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem lemma_7_12_b_of_lemma712a
    (hS : SuzukiFourGroupTheorem) (h712 : Lemma712a h)
    (s : Setup h) {x : G} (hxQ : x ∈ s.Q) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.centralizer ({h.t} : Set G) := by
  have hp := h.p_ne_two_of_eq_three hp3
  obtain ⟨c, rfl⟩ := s.exists_config hp
  have hxodd := ((c.toSetup.mem_Q_iff hp).mp hxQ).2
  have hxinv : x⁻¹ ≠ x := by
    intro h0
    apply hx1
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by
      rw [pow_two]; nth_rewrite 1 [← h0]; exact inv_mul_cancel x)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · rw [h1] at hxodd
      exact absurd hxodd (by decide)
  have hR : Subgroup.zpowers x ≤ c.Q := (Subgroup.zpowers_le).mpr hxQ
  have hR1 : Subgroup.zpowers x ≠ ⊥ := by rw [Ne, Subgroup.zpowers_eq_bot]; exact hx1
  have hNx : Subgroup.normalizer (Subgroup.zpowers x : Set G) =
      Subgroup.normalizer (c.T : Set G) := by
    rw [c.toSetup.lemma_4_3 hp hS hR hR1, c.toSetup.lemma_7_1_b hp3 hS]
  intro g hg
  have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hgT : g ∈ Subgroup.normalizer (c.T : Set G) :=
    hNx ▸ mem_normalizer_zpowers_of_commute hgx
  have hle : Subgroup.zpowers c.μ ≤
      Subgroup.normalizer ((Subgroup.centralizer (c.T : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_of_conj_mem fun y hy => c.toSetup.conj_mem_centralizer_T c.μ_mem_NT hy
  rw [c.normalizer_T_eq, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hgT
  obtain ⟨a, ha, b, hb, hgab⟩ := hgT
  simp only at hgab
  subst hgab
  have hSQ : (c.S : Subgroup G) ≤ Subgroup.normalizer (c.Q : Set G) :=
    c.toSetup.S_le_centralizer_T.trans (c.toSetup.centralizer_T_le_normalizer_T.trans
      (c.toSetup.normalizer_T_le_normalizer_Q hp))
  rw [c.toSetup.centralizer_T_eq hp,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hSQ] at hb
  obtain ⟨s₀, hs₀, r₀, hr₀, hbsr⟩ := hb
  simp only at hbsr
  subst hbsr
  have hQab : ∀ y ∈ c.Q, ∀ z ∈ c.Q, y * z = z * y := by
    have := c.toSetup.isCyclic_Q hp
    intro y hy z hz
    exact congrArg Subtype.val ((IsCyclic.commGroup (α := c.Q)).mul_comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hconj : a * s₀ * r₀ * x * (a * s₀ * r₀)⁻¹ = a * (s₀ * x * s₀⁻¹) * a⁻¹ := by
    rw [show a * s₀ * r₀ * x * (a * s₀ * r₀)⁻¹ = a * s₀ * (r₀ * x * r₀⁻¹) * s₀⁻¹ * a⁻¹ by group,
      hQab r₀ hr₀ x hxQ, mul_inv_cancel_right]
    group
  have hgx' : a * s₀ * r₀ * x * (a * s₀ * r₀)⁻¹ = x := by
    calc a * s₀ * r₀ * x * (a * s₀ * r₀)⁻¹ = a * (s₀ * r₀) * x * (a * (s₀ * r₀))⁻¹ := by group
      _ = x * (a * (s₀ * r₀)) * (a * (s₀ * r₀))⁻¹ := by rw [hgx]
      _ = x := by group
  rw [hconj] at hgx'
  have hs₀x : s₀ * x * s₀⁻¹ = x ∨ (s₀ ∉ c.T ∧ s₀ * x * s₀⁻¹ = x⁻¹) := by
    by_cases hs₀T : s₀ ∈ c.T
    · left
      have := (Subgroup.mem_centralizer_iff.mp (c.toSetup.T_le_centralizer_Q hs₀T)) x hxQ
      rw [← this, mul_inv_cancel_right]
    · exact Or.inr ⟨hs₀T, c.toSetup.conj_eq_inv_of_mem_S hp hs₀ hs₀T hxQ⟩
  have hμQ := c.μ_mem_normalizer_Q hp
  have hfix : ∀ k : ℤ, c.μ ^ k * x = x * c.μ ^ k → c.μ ^ k = 1 := by
    intro k hk
    have hμ3 := pow_three_eq_one_of_orderOf c.orderOf_μ
    have hmem : c.μ ^ k ∈ Subgroup.zpowers c.μ := Subgroup.zpow_mem_zpowers _ _
    rcases (mem_zpowers_iff_of_orderOf_three c.orderOf_μ).mp hmem with h1 | h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hk
      exact hx1 (h712 c.toSetup c.μ hμQ c.orderOf_μ x hxQ hk)
    · exfalso
      rw [h1] at hk
      have hk' : c.μ * x = x * c.μ := by
        calc c.μ * x = c.μ * x * (c.μ ^ 2 * c.μ) := by rw [← pow_succ, hμ3, mul_one]
          _ = c.μ * (x * c.μ ^ 2) * c.μ := by group
          _ = c.μ * (c.μ ^ 2 * x) * c.μ := by rw [hk]
          _ = (c.μ * c.μ ^ 2) * x * c.μ := by group
          _ = x * c.μ := by rw [← pow_succ', hμ3, one_mul]
      exact hx1 (h712 c.toSetup c.μ hμQ c.orderOf_μ x hxQ hk')
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  rcases hs₀x with h1 | ⟨-, h1⟩
  ·
    rw [h1] at hgx'
    have hk : c.μ ^ k * x = x * c.μ ^ k := by
      calc c.μ ^ k * x = c.μ ^ k * x * (c.μ ^ k)⁻¹ * c.μ ^ k := by group
        _ = x * c.μ ^ k := by rw [hgx']
    have hk1 := hfix k hk
    rw [hk1, one_mul]
    have hs₀T : s₀ ∈ c.T := by
      by_contra hs₀T
      exact hxinv ((c.toSetup.conj_eq_inv_of_mem_S hp hs₀ hs₀T hxQ).symm.trans h1)
    have htT := c.t_mem_T
    have hs₀t : s₀ * h.t = h.t * s₀ :=
      congrArg Subtype.val (c.four.isMulCommutative.is_comm.comm ⟨s₀, hs₀T⟩ ⟨h.t, htT⟩)
    have hr₀t : r₀ * h.t = h.t * r₀ :=
      (Subgroup.mem_centralizer_iff.mp (c.toSetup.T_le_centralizer_Q htT)) r₀ hr₀
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [mul_assoc, hr₀t, ← mul_assoc, hs₀t, mul_assoc]
  ·
    exfalso
    rw [h1] at hgx'
    have hk : c.μ ^ (2 * k) * x = x * c.μ ^ (2 * k) := by
      have e1 : c.μ ^ k * x⁻¹ = x * c.μ ^ k := by
        calc c.μ ^ k * x⁻¹ = c.μ ^ k * x⁻¹ * (c.μ ^ k)⁻¹ * c.μ ^ k := by group
          _ = x * c.μ ^ k := by rw [hgx']
      have e2 : c.μ ^ k * x = x⁻¹ * c.μ ^ k := by
        have := congrArg (·⁻¹) e1
        simp only [mul_inv_rev, inv_inv] at this
        calc c.μ ^ k * x = c.μ ^ k * x * ((c.μ ^ k)⁻¹ * c.μ ^ k) := by group
          _ = c.μ ^ k * (x * (c.μ ^ k)⁻¹) * c.μ ^ k := by group
          _ = c.μ ^ k * ((c.μ ^ k)⁻¹ * x⁻¹) * c.μ ^ k := by rw [this]
          _ = x⁻¹ * c.μ ^ k := by group
      rw [show 2 * k = k + k by ring, zpow_add]
      calc c.μ ^ k * c.μ ^ k * x = c.μ ^ k * (c.μ ^ k * x) := by group
        _ = c.μ ^ k * (x⁻¹ * c.μ ^ k) := by rw [e2]
        _ = (c.μ ^ k * x⁻¹) * c.μ ^ k := by group
        _ = x * c.μ ^ k * c.μ ^ k := by rw [e1]
        _ = x * (c.μ ^ k * c.μ ^ k) := by group
    have hk1 := hfix (2 * k) hk
    have hk1' : c.μ ^ k = 1 := by
      have h3 := pow_three_eq_one_of_orderOf c.orderOf_μ
      have hμ3z : c.μ ^ (3 : ℤ) = 1 := by
        rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, h3]
      have : c.μ ^ k = c.μ ^ (3 * k - 2 * k) := by ring_nf
      rw [this, zpow_sub, zpow_mul, hμ3z, one_zpow, hk1, inv_one, one_mul]
    rw [hk1', one_mul, inv_one, mul_one] at hgx'
    exact hxinv hgx'

theorem centralizer_le_of_lemma712a_of_lemma716
    (hS : SuzukiFourGroupTheorem)
    (h712 : Lemma712a h) (h716 : Lemma716 h) {x : G}
    (hx : x ∈ Subgroup.centralizer ({h.t} : Set G)) (hx1 : x ≠ 1)
    (hcop : Nat.Coprime (orderOf x) 6) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.centralizer ({h.t} : Set G) := by
  have hp := h.p_ne_two_of_eq_three hp3
  have hq8 := h.q_mod_eight_of_eq_three hp3
  have hodd : Odd (orderOf x) :=
    Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 6) hcop)
  have hxF := h.mem_F_of_odd hx hodd
  have hcop3 : Nat.Coprime (orderOf x) h.p := by
    rw [hp3]
    exact Nat.Coprime.coprime_dvd_right (by norm_num : 3 ∣ 6) hcop
  obtain ⟨C, hCF, hCc, hxC, hCcard⟩ := exists_cyclic_of_coprime h.F h.iso hp h.five_lt hxF hx1
    hcop3
  rw [← JTHyp.q_eq] at hCcard
  rcases hCcard with hC | hC
  · exact h716 C hCF hCc hC x hxC hx1
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨⟨v, hvC⟩, hv⟩ := exists_prime_orderOf_dvd_card' (G := C) 2
      (by omega : 2 ∣ Nat.card C)
    have hv2 : orderOf v = 2 := by rw [← hv, Subgroup.orderOf_mk]
    have hvF : v ∈ h.F := hCF hvC
    have hvv : v * v = 1 := by rw [← pow_two, ← hv2, pow_orderOf_eq_one]
    have hv1 : v ≠ 1 := fun h0 => by rw [h0, orderOf_one] at hv2; omega
    have htv : Commute h.t v := (h.commute_of_mem_F hvF).symm
    have htne : h.t ≠ v := fun h0 => h.t_not_mem (h0 ▸ hvF)
    set T := GorensteinWalter.kleinFourOfCommutingInvolutions h.t v h.t_mul_t hvv htv with hTdef
    have hT : IsKleinFour T := GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
      _ _ _ _ h.t_ne_one hv1 htne htv
    have hmemT : ∀ y, y ∈ T ↔ y = h.t * v ∨ y = h.t ∨ y = v ∨ y = 1 := fun y => Iff.rfl
    have htT : h.t ∈ T := (hmemT _).mpr (Or.inr (Or.inl rfl))
    have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by rw [hT.card_four]; norm_num)
    obtain ⟨S', hS'⟩ := hT2.exists_le_sylow
    let s : Setup h := ⟨S', hS' htT, T, hS', hT, htT⟩
    have hCab : ∀ y ∈ C, ∀ z ∈ C, y * z = z * y := fun y hy z hz =>
      congrArg Subtype.val ((IsCyclic.commGroup (α := C)).mul_comm ⟨y, hy⟩ ⟨z, hz⟩)
    have hxT : x ∈ Subgroup.centralizer (s.T : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have htx : h.t * x = x * h.t := (h.commute_of_mem_F hxF).symm
      have hvx : v * x = x * v := hCab v hvC x hxC
      rcases (hmemT y).mp hy with rfl | rfl | rfl | rfl
      · rw [mul_assoc, hvx, ← mul_assoc, htx, mul_assoc]
      · exact htx
      · exact hvx
      · rw [one_mul, mul_one]
    exact h.lemma_7_12_b_of_lemma712a hp3 hS h712 s ((s.mem_Q_iff hp).mpr ⟨hxT, hodd⟩) hx1

end JTHyp

end CFSG.Walter.JT

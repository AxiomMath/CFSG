module

public import CFSG.Walter.W67.W1Basic
public import CFSG.Walter.JRAssembly

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups

namespace JRGroup

variable {L : Type} [Group L] [Finite L] (h : JRGroup L)

theorem J_mul_J : h.J * h.J = 1 := by
  rw [← pow_two, ← h.orderOf_J, pow_orderOf_eq_one]

theorem J_inv : h.J⁻¹ = h.J := inv_eq_of_mul_eq_one_right h.J_mul_J

theorem J_ne_one : h.J ≠ 1 := by
  intro h1
  have := h.orderOf_J
  rw [h1, orderOf_one] at this
  omega

theorem J_mem_H : h.J ∈ Subgroup.centralizer ({h.J} : Set L) :=
  Subgroup.mem_centralizer_singleton_iff.mpr rfl

theorem commute_J_of_mem_K {x : L} (hx : x ∈ h.K) : x * h.J = h.J * x :=
  Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hx)

theorem odd_p : Odd h.p := (Fact.out : h.p.Prime).odd_of_ne_two h.p_ne_two

theorem odd_q : Odd h.q := h.odd_p.pow

theorem five_lt_q (hq5 : h.q ≠ 5) (hq3 : 3 < h.q) : 5 < h.q := by
  obtain ⟨k, hk⟩ := h.odd_q
  omega

@[simp] theorem toJTHyp_p (hq : 5 < h.q) : (h.toJTHyp hq).p = h.p := rfl

@[simp] theorem toJTHyp_f (hq : 5 < h.q) : (h.toJTHyp hq).f = h.f := rfl

@[simp] theorem toJTHyp_t (hq : 5 < h.q) : (h.toJTHyp hq).t = h.J := rfl

@[simp] theorem toJTHyp_F (hq : 5 < h.q) : (h.toJTHyp hq).F = h.K := rfl

@[simp] theorem toJTHyp_q (hq : 5 < h.q) : (h.toJTHyp hq).q = h.q := rfl

theorem p_eq_three (hJT : JTThreeHyp) (hq : 5 < h.q) : h.p = 3 :=
  hJT L (h.toJTHyp hq) h.p_ne_two

theorem odd_f
    (hJT : JTThreeHyp) (hq : 5 < h.q) : Odd h.f ∧ 1 < h.f :=
  (h.toJTHyp hq).odd_f_of_three (h.p_eq_three hJT hq)

theorem q_eq_three_pow (hJT : JTThreeHyp) (hq : 5 < h.q) : h.q = 3 ^ h.f := by
  rw [JRGroup.q, h.p_eq_three hJT hq]

@[expose] def toReeTypeHyp
    (hJT : JTThreeHyp) (hq : 5 < h.q) : Ward.ReeTypeHyp L where
  p := h.p
  f := h.f
  p_ne_two := h.p_ne_two
  f_pos := h.f_pos
  card_sylow := h.card_sylow
  elementary_sylow := h.elementary_sylow
  index_ne_two := h.index_ne_two
  J := h.J
  orderOf_J := h.orderOf_J
  L := h.K
  le_centralizer := h.le_centralizer
  J_not_mem := h.J_not_mem
  centralizer_eq := h.centralizer_eq
  iso := h.iso
  normalizer_le := by
    have hp3 := h.p_eq_three hJT hq
    have hq8 := (h.toJTHyp hq).q_mod_eight_of_eq_three hp3
    have hward : Ward.wardSign (h.p ^ h.f) = -1 := by
      rw [Ward.wardSign]
      simp [show (h.p ^ h.f) % 8 = 3 from hq8]
    intro R hRF hR R₀ hR₀ hR₀1
    rw [hward] at hR
    have hR' : 2 * orderOf R + 1 = (h.toJTHyp hq).q := by
      change 2 * orderOf R + 1 = h.p ^ h.f
      have : ((h.p ^ h.f : ℕ) : ℤ) = (h.p : ℤ) ^ h.f := by push_cast; ring
      omega
    exact (h.toJTHyp hq).normalizer_le_of_lemma716 hp3 ((h.toJTHyp hq).lemma_7_16 hp3) hRF hR'
      hR₀ hR₀1
  not_commute := by
    have hp3 := h.p_eq_three hJT hq
    have hq8 := (h.toJTHyp hq).q_mod_eight_of_eq_three hp3
    have hward : Ward.wardSign (h.p ^ h.f) = -1 := by
      rw [Ward.wardSign]
      simp [show (h.p ^ h.f) % 8 = 3 from hq8]
    intro J' hJ'F hJ' S hSF hS hSJ A hA hAN
    rw [hward] at hS
    have hS' : 4 * orderOf S = (h.toJTHyp hq).q + 1 := by
      change 4 * orderOf S = h.p ^ h.f + 1
      have : ((h.p ^ h.f : ℕ) : ℤ) = (h.p : ℤ) ^ h.f := by push_cast; ring
      omega
    exact (h.toJTHyp hq).not_commute_of_lemma712a hp3 ((h.toJTHyp hq).lemma_7_12_a hp3) hJ'F
      hJ' hSF hS' hSJ hA hAN

@[simp] theorem toReeTypeHyp_q
    (hJT : JTThreeHyp) (hq : 5 < h.q) :
    (h.toReeTypeHyp hJT hq).q = h.q := rfl

@[simp] theorem toReeTypeHyp_J
    (hJT : JTThreeHyp) (hq : 5 < h.q) :
    (h.toReeTypeHyp hJT hq).J = h.J := rfl

@[simp] theorem toReeTypeHyp_L
    (hJT : JTThreeHyp) (hq : 5 < h.q) :
    (h.toReeTypeHyp hJT hq).L = h.K := rfl

theorem normal_K : (h.K.subgroupOf (Subgroup.centralizer ({h.J} : Set L))).Normal := by
  have hle : Subgroup.centralizer ({h.J} : Set L) ≤ Subgroup.normalizer (h.K : Set L) := by
    rw [h.centralizer_eq]
    refine sup_le ?_ Subgroup.le_normalizer
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro k
    have hc : ∀ k ∈ h.K, h.J * k * h.J⁻¹ = k := fun k hk => by
      rw [← h.commute_J_of_mem_K hk, mul_inv_cancel_right]
    constructor
    · intro hk
      rw [hc k hk]
      exact hk
    · intro hk
      have : k = h.J * (h.J * k * h.J⁻¹) * h.J⁻¹ := by
        calc k = (h.J * h.J) * k * (h.J * h.J)⁻¹ := by rw [h.J_mul_J]; group
          _ = h.J * (h.J * k * h.J⁻¹) * h.J⁻¹ := by group
      rw [this, hc _ hk]
      exact hk
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer h.le_centralizer).mpr hle

@[expose] def toHyp : Hyp L where
  p := h.p
  f := h.f
  p_ne_two := h.p_ne_two
  f_pos := h.f_pos
  abelian_sylow := fun P => (h.elementary_sylow P).toIsMulCommutative
  card_sylow := h.card_sylow
  J := h.J
  orderOf_J := h.orderOf_J
  K := h.K
  le_centralizer := h.le_centralizer
  normal := h.normal_K
  iso := h.iso

@[simp] theorem toHyp_q : h.toHyp.q = h.q := rfl

@[simp] theorem toHyp_J : h.toHyp.J = h.J := rfl

@[simp] theorem toHyp_K : h.toHyp.K = h.K := rfl

@[simp] theorem toHyp_p : h.toHyp.p = h.p := rfl

@[simp] theorem toHyp_f : h.toHyp.f = h.f := rfl

theorem mem_K_of_odd {x : L} (hx : x ∈ Subgroup.centralizer ({h.J} : Set L))
    (hodd : Odd (orderOf x)) : x ∈ h.K := by
  rw [h.centralizer_eq] at hx
  have hc : ∀ a ∈ Subgroup.zpowers h.J, ∀ b ∈ h.K, a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ((Commute.zpow_left (h.commute_J_of_mem_K hb).symm n)).eq
  have hset := (card_sup_mul_card_inf_of_commute _ _ hc).2
  have hx' : x ∈ ((Subgroup.zpowers h.J ⊔ h.K : Subgroup L) : Set L) := hx
  rw [hset] at hx'
  obtain ⟨a, ha, b, hb, hab⟩ := hx'
  simp only at hab
  subst hab
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨k, hk⟩ := hodd
  have h1 : (h.J ^ n * b) ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
  have hcomm : Commute (h.J ^ n) b := hc _ (Subgroup.zpow_mem_zpowers _ _) _ hb
  rw [hcomm.mul_pow, ← zpow_natCast, ← zpow_mul] at h1
  have hJb : h.J ^ (n * ((2 * k + 1 : ℕ) : ℤ)) ∈ h.K := by
    have : h.J ^ (n * ((2 * k + 1 : ℕ) : ℤ)) = (b ^ (2 * k + 1))⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact h.K.inv_mem (h.K.pow_mem hb _)
  have hJ2 : orderOf h.J = 2 := h.orderOf_J
  rcases Int.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · have : h.J ^ n = 1 := by
      rw [hm, ← two_mul, zpow_mul]
      have : h.J ^ (2 : ℤ) = 1 := by
        rw [zpow_ofNat, ← hJ2, pow_orderOf_eq_one]
      rw [this, one_zpow]
    rw [this, one_mul]
    exact hb
  · exfalso
    apply h.J_not_mem
    have hodd' : Odd (n * ((2 * k + 1 : ℕ) : ℤ)) :=
      Int.odd_mul.mpr ⟨⟨m, hm⟩, by push_cast; exact ⟨k, by ring⟩⟩
    obtain ⟨r, hr⟩ := hodd'
    have : h.J ^ (n * ((2 * k + 1 : ℕ) : ℤ)) = h.J := by
      rw [hr, zpow_add, zpow_mul, zpow_one]
      have : h.J ^ (2 : ℤ) = 1 := by
        rw [zpow_ofNat, ← hJ2, pow_orderOf_eq_one]
      rw [this, one_zpow, one_mul]
    rw [← this]
    exact hJb

end JRGroup

end CFSG.Walter.W67

module

public import CFSG.Walter.ReeOrder.JT.Section7J

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_conj_of_mem_centralizer {X : Type*} [Group X] [Finite X]
    {p : ℕ} [Fact p.Prime] (P : Sylow p X) {x y g : X}
    (hx : x ∈ Subgroup.centralizer ((P : Subgroup X) : Set X))
    (hy : y ∈ Subgroup.centralizer ((P : Subgroup X) : Set X)) (hgxy : g * x * g⁻¹ = y) :
    ∃ n ∈ Subgroup.normalizer ((P : Subgroup X) : Set X), n * x * n⁻¹ = y := by
  have hy' : g⁻¹⁻¹ * x * g⁻¹⁻¹⁻¹ ∈ Subgroup.centralizer ((P : Subgroup X) : Set X) := by
    simpa [hgxy] using hy
  obtain ⟨n, hn, hneq⟩ := Sylow.conj_eq_normalizer_conj_of_mem_centralizer P x g⁻¹ hx (by
    simpa [mul_assoc] using hy')
  refine ⟨n⁻¹, Subgroup.inv_mem _ hn, ?_⟩
  rw [inv_inv, ← hneq, ← hgxy]
  group

namespace JTHyp

variable (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem inf_centralizer_le_torus
    (c : TorusConf h) {x : G} (hxC : x ∈ c.C) (hx1 : x ≠ 1) :
    h.F ⊓ Subgroup.centralizer ({x} : Set G) ≤ c.C := by
  have hxodd : Odd (orderOf x) := by
    refine Odd.of_dvd_nat (Nat.odd_iff.mpr ?_) (Subgroup.orderOf_dvd_natCard c.C hxC)
    have := c.card_C
    have hq8 := h.q_mod_eight_of_eq_three hp3
    omega
  intro z ⟨hzF, hzx⟩
  have hzx' := Subgroup.mem_centralizer_singleton_iff.mp hzx
  have hzN : z ∈ h.F ⊓ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) :=
    ⟨hzF, mem_normalizer_zpowers_of_commute hzx'⟩
  have hR : Subgroup.zpowers x ≤ c.C := (Subgroup.zpowers_le).mpr hxC
  have hR1 : Subgroup.zpowers x ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact hx1
  rw [c.torus.normalizer _ hR hR1] at hzN
  rcases c.torus.conj_eq hzN hxC with ⟨hzC, -⟩ | ⟨-, hinv⟩
  · exact hzC
  · exfalso
    rw [hzx', mul_inv_cancel_right] at hinv
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by
      rw [pow_two]
      nth_rewrite 2 [hinv]
      exact mul_inv_cancel x)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
    · exact hx1 (orderOf_eq_one_iff.mp h1)
    · rw [h1] at hxodd
      exact absurd hxodd (by decide)

theorem subset_of_isPGroup_two
    (c : TorusConf h) {x : G} (hxC : x ∈ c.C) (hx1 : x ≠ 1)
    {R : Subgroup G} (hR : IsPGroup 2 R) (htR : h.t ∈ R)
    (hRx : R ≤ Subgroup.centralizer ({x} : Set G)) : ∀ y ∈ R, y = 1 ∨ y = h.t := by
  have hp := h.p_ne_two_of_eq_three hp3
  have hCodd : Odd (Nat.card c.C) := by
    have := c.card_C
    have hq8 := h.q_mod_eight_of_eq_three hp3
    exact Nat.odd_iff.mpr (by omega)
  have hle := h.inf_centralizer_le_torus hp3 c hxC hx1
  intro y hy
  have hyy : y * y = 1 := h.mul_self_of_isPGroup_two hp3 hR hy
  obtain ⟨S, hS⟩ := hR.exists_le_sylow
  have hyt : y * h.t = h.t * y := congrArg Subtype.val
    ((h.abelian_sylow S).is_comm.comm ⟨y, hS hy⟩ ⟨h.t, hS htR⟩)
  have hyC : y ∈ Subgroup.centralizer ({h.t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hyt
  have hodd1 : ∀ z ∈ c.C, z * z = 1 → z = 1 := by
    intro z hz hzz
    have h1 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hzz)
    have h2 : Odd (orderOf z) := Odd.of_dvd_nat hCodd (Subgroup.orderOf_dvd_natCard _ hz)
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h3 | h3
    · exact orderOf_eq_one_iff.mp h3
    · rw [h3] at h2; exact absurd h2 (by decide)
  rcases h.mem_centralizer_t.mp hyC with hyF | hyF
  · left
    exact hodd1 y (hle ⟨hyF, hRx hy⟩) hyy
  · right
    have htyx : h.t * y ∈ Subgroup.centralizer ({x} : Set G) :=
      Subgroup.mul_mem _ (hRx htR) (hRx hy)
    have h1 := hodd1 (h.t * y) (hle ⟨hyF, htyx⟩) (by
      rw [show h.t * y * (h.t * y) = (h.t * h.t) * (y * y) by
        rw [mul_assoc, ← mul_assoc y, hyt]; group, h.t_mul_t, hyy, one_mul])
    rw [← mul_one h.t, ← h1, ← mul_assoc, h.t_mul_t, one_mul]

theorem not_four_dvd_card_centralizer
    (c : TorusConf h) {r : ℕ} [hr : Fact r.Prime]
    (hrq : r ∣ (h.q - 1) / 2) {x u : G} (hx : orderOf x = r) (hu : orderOf u = 2)
    (hxu : x * u = u * x) : ¬ 4 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr7 := h.seven_le_of_pi hp3 hrq
  obtain ⟨g, hg⟩ := h.exists_conj_mem_of_commute hp3 c.torus.le c.torus.cyclic c.card_C hrq hx hu
    hxu
  set x' := g * x * g⁻¹ with hx'def
  have hx'1 : x' ≠ 1 := by
    intro h0
    have : x = 1 := by
      have := congrArg (fun y => g⁻¹ * y * g) h0
      simpa [x', mul_assoc] using this
    rw [this, orderOf_one] at hx
    omega
  have hcard : Nat.card (Subgroup.centralizer ({x'} : Set G)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
    have := centralizer_singleton_map (MulAut.conj g) x
    rw [MulAut.conj_apply] at this
    rw [hx'def, ← this, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rw [← hcard]
  intro h4
  have htx' : h.t ∈ Subgroup.centralizer ({x'} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (h.commute_of_mem_F (c.torus.le hg)).symm
  have hT : IsPGroup 2 (Subgroup.zpowers h.t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.orderOf_t, pow_one])
  obtain ⟨S, hS⟩ := (hT.comap_subtype (K := Subgroup.centralizer ({x'} : Set G))).exists_le_sylow
  set SG : Subgroup G := (S : Subgroup _).map (Subgroup.centralizer ({x'} : Set G)).subtype
  have hSG2 : IsPGroup 2 SG := S.isPGroup'.map _
  have htS : h.t ∈ SG := ⟨⟨h.t, htx'⟩, hS (by
    rw [Subgroup.mem_comap]
    exact Subgroup.mem_zpowers _), rfl⟩
  have hsub := h.subset_of_isPGroup_two hp3 c hg hx'1 hSG2 htS (Subgroup.map_subtype_le _)
  have hScard : Nat.card SG ≤ 2 := by
    have : (SG : Set G) ⊆ {1, h.t} := fun y hy => by
      rcases hsub y hy with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    have := Set.ncard_le_ncard this (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe] at this
    exact this.trans ((Set.ncard_insert_le 1 {h.t}).trans (by rw [Set.ncard_singleton]))
  have h4S : 2 ^ 2 ∣ Nat.card (S : Subgroup (Subgroup.centralizer ({x'} : Set G))) :=
    S.pow_dvd_card_of_pow_dvd_card (n := 2) (by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact h4)
  rw [← Subgroup.card_map_of_injective (Subgroup.centralizer ({x'} : Set G)).subtype_injective]
    at h4S
  have h5 : 2 ^ 2 ≤ Nat.card SG := Nat.le_of_dvd Nat.card_pos h4S
  omega

theorem card_eq_mul_of_le_normalizer
    (c : TorusConf h) {p : ℕ} [hp : Fact p.Prime]
    (hpq : p ∣ (h.q - 1) / 2) {K : Subgroup G} (hK : IsPGroup p K)
    (hT₀K : c.T₀ ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card K = Nat.card (K ⊓ Subgroup.centralizer ({h.t} : Set G) : Subgroup G) *
      Nat.card (K ⊓ Subgroup.centralizer ({c.w} : Set G) : Subgroup G) *
      Nat.card (K ⊓ Subgroup.centralizer ({h.t * c.w} : Set G) : Subgroup G) := by
  have hp7 := h.seven_le_of_pi hp3 hpq
  have hKodd : Odd (Nat.card K) := by
    obtain ⟨n, hn⟩ := hK.exists_card_eq
    rw [hn]
    exact (hp.out.odd_of_ne_two (by omega)).pow
  have hBW := card_mul_card_sq_eq_mul h.t_mul_t c.w_mul_w h.t_ne_one c.w_ne_one c.t_ne_w
    c.commute_t_w K (hT₀K c.t_mem_T₀) (hT₀K c.w_mem_T₀) hKodd
  have hbot : K ⊓ Subgroup.centralizer ({h.t} : Set G) ⊓
      Subgroup.centralizer ({c.w} : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxV : x ∈ Subgroup.centralizer (c.T₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hxt := Subgroup.mem_centralizer_singleton_iff.mp hx.1.2
      have hxw := Subgroup.mem_centralizer_singleton_iff.mp hx.2
      rcases c.mem_T₀.mp hv with rfl | rfl | rfl | rfl
      · rw [mul_assoc, ← hxw, ← mul_assoc, ← hxt, mul_assoc]
      · exact hxt.symm
      · exact hxw.symm
      · simp
    have h1 : orderOf x ∣ Nat.card (Subgroup.centralizer (c.T₀ : Set G)) :=
      Subgroup.orderOf_dvd_natCard _ hxV
    obtain ⟨n, hn⟩ := hK.exists_card_eq
    have h2 : orderOf x ∣ p ^ n := hn ▸ Subgroup.orderOf_dvd_natCard K hx.1.1
    have hcop : Nat.Coprime (p ^ n) (Nat.card (Subgroup.centralizer (c.T₀ : Set G))) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr
        (h.not_dvd_card_centralizer_of_isKleinFour hp3 hpq c.isKleinFour_T₀))
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h1)
  rw [hbot, Subgroup.card_bot, one_pow, mul_one] at hBW
  exact hBW

end JTHyp

end CFSG.Walter.JT

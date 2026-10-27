module

public import CFSG.Walter.ReeOrder.JT.Section7L

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

section General

variable {X : Type*} [Group X] [Finite X]

theorem exists_conj_of_not_four_dvd (h4 : ¬ 4 ∣ Nat.card X) {a b : X} (ha : orderOf a = 2)
    (hb : orderOf b = 2) : ∃ g : X, g * a * g⁻¹ = b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card X := ha ▸ orderOf_dvd_natCard a
  have hfac : (Nat.card X).factorization 2 = 1 := by
    have h1 : 1 ≤ (Nat.card X).factorization 2 :=
      (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two Nat.card_pos.ne').mp h2
    have h3 : (Nat.card X).factorization 2 < 2 := by
      by_contra h3
      replace h3 := not_lt.mp h3
      exact h4 ((Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mpr h3)
    omega
  have hcard : ∀ x : X, orderOf x = 2 →
      Nat.card (Subgroup.zpowers x) = 2 ^ (Nat.card X).factorization 2 := fun x hx => by
    rw [Nat.card_zpowers, hx, hfac, pow_one]
  let Sa := Sylow.ofCard (Subgroup.zpowers a) (hcard a ha)
  let Sb := Sylow.ofCard (Subgroup.zpowers b) (hcard b hb)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Sa Sb
  refine ⟨g, ?_⟩
  have hmem : g * a * g⁻¹ ∈ Subgroup.zpowers b := by
    have : g * a * g⁻¹ ∈ ((g • Sa : Sylow 2 X) : Subgroup X) := by
      rw [Sylow.coe_subgroup_smul]
      exact ⟨a, Subgroup.mem_zpowers a, rfl⟩
    rw [hg] at this
    exact this
  rw [mem_zpowers_iff_mem_range_orderOf, hb] at hmem
  simp only [Finset.mem_image, Finset.mem_range] at hmem
  obtain ⟨k, hk, hkb⟩ := hmem
  interval_cases k
  · exfalso
    rw [pow_zero] at hkb
    have : a = 1 := by
      have := congrArg (fun y => g⁻¹ * y * g) hkb
      simpa [mul_assoc] using this.symm
    rw [this, orderOf_one] at ha
    omega
  · rw [pow_one] at hkb
    exact hkb.symm

theorem eq_three_of_dvd_six {r : ℕ} (h6 : r ∣ 6) (h2 : ¬ 2 ∣ r) (h1 : r ≠ 1) : r = 3 := by
  have hr : r ≤ 6 := Nat.le_of_dvd (by norm_num) h6
  interval_cases r <;> simp_all

omit [Finite X] in
theorem mem_centralizer_of_mem_omegaZ {p : ℕ} {P : Subgroup X} {z : X}
    (hz : z ∈ omegaZ P p) : z ∈ Subgroup.centralizer (P : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (hz.2.1 y hy).symm

end General

namespace JTHyp

variable (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem exists_conj_zpow_eq
    (c : TorusConf h) {r : ℕ} [hr : Fact r.Prime]
    (hrq : r ∣ (h.q - 1) / 2) {x y u v : G} (hx : orderOf x = r) (hy : orderOf y = r)
    (hu : orderOf u = 2) (hv : orderOf v = 2) (hxu : x * u = u * x) (hyv : y * v = v * y) :
    ∃ g : G, ∃ k : ℤ, g * x ^ k * g⁻¹ = y := by
  obtain ⟨g₁, hg₁⟩ := h.exists_conj_mem_of_commute hp3 c.torus.le c.torus.cyclic c.card_C hrq hx
    hu hxu
  obtain ⟨g₂, hg₂⟩ := h.exists_conj_mem_of_commute hp3 c.torus.le c.torus.cyclic c.card_C hrq hy
    hv hyv
  have hcard : Nat.card (Subgroup.zpowers (g₂ * y * g₂⁻¹)) =
      Nat.card (Subgroup.zpowers (g₁ * x * g₁⁻¹)) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hy,
      ← MulAut.conj_apply, MulEquiv.orderOf_eq, hx]
  have heq := eq_of_le_of_isCyclic c.torus.cyclic ((Subgroup.zpowers_le).mpr hg₂)
    ((Subgroup.zpowers_le).mpr hg₁) hcard
  have hmem : g₂ * y * g₂⁻¹ ∈ Subgroup.zpowers (g₁ * x * g₁⁻¹) :=
    heq ▸ Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  refine ⟨g₂⁻¹ * g₁, k, ?_⟩
  have : (g₁ * x * g₁⁻¹) ^ k = g₁ * x ^ k * g₁⁻¹ := by
    rw [← MulAut.conj_apply, ← map_zpow, MulAut.conj_apply]
  rw [this] at hk
  calc g₂⁻¹ * g₁ * x ^ k * (g₂⁻¹ * g₁)⁻¹ = g₂⁻¹ * (g₁ * x ^ k * g₁⁻¹) * g₂ := by group
    _ = g₂⁻¹ * (g₂ * y * g₂⁻¹) * g₂ := by rw [hk]
    _ = y := by group

theorem card_omegaZ_inf_le
    {p : ℕ} [Fact p.Prime] (hpq : p ∣ (h.q - 1) / 2) {P : Subgroup G}
    (hP : IsPGroup p P) {u : G} (hu : orderOf u = 2) :
    Nat.card (omegaZ P p ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) ≤ p :=
  h.card_le_of_le_centralizer hp3 hpq (hP.to_le (inf_le_left.trans omegaZ_le))
    (fun _ hx => pow_eq_one_of_mem_omegaZ hx.1) hu inf_le_right

theorem exists_orderOf_three
    (c : TorusConf h) {p : ℕ} [hp : Fact p.Prime]
    (hpq : p ∣ (h.q - 1) / 2) (P : Sylow p G)
    (hT₀P : c.T₀ ≤ Subgroup.normalizer ((P : Subgroup G) : Set G))
    (hW : ¬ IsCyclic (omegaZ (P : Subgroup G) p)) :
    ∃ s : G, s ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) ∧
      s ∈ Subgroup.normalizer (c.T₀ : Set G) ∧ orderOf s = 3 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp7 := h.seven_le_of_pi hp3 hpq
  set W := omegaZ (P : Subgroup G) p with hWdef
  have hWp : IsPGroup p W := P.isPGroup'.to_le omegaZ_le
  have hTW : c.T₀ ≤ Subgroup.normalizer (W : Set G) :=
    hT₀P.trans normalizer_le_normalizer_omegaZ
  have hP1 : (P : Subgroup G) ≠ ⊥ := by
    intro h0
    apply hW
    have : W = ⊥ := le_bot_iff.mp (h0 ▸ omegaZ_le)
    rw [this]
    infer_instance
  have h8 := h.not_eight_dvd_card_normalizer_of_pi hp3 hpq P.isPGroup' hP1
  have hBW := h.card_eq_mul_of_le_normalizer hp3 c hpq hWp hTW
  have ha := h.card_omegaZ_inf_le hp3 hpq P.isPGroup' h.orderOf_t
  have hb := h.card_omegaZ_inf_le hp3 hpq P.isPGroup' c.orderOf_w
  have hc := h.card_omegaZ_inf_le hp3 hpq P.isPGroup' c.orderOf_tw
  have hWbig : p < Nat.card W := by
    by_contra hle
    replace hle := not_lt.mp hle
    apply hW
    obtain ⟨n, hn⟩ := hWp.exists_card_eq
    rcases n with _ | n
    · rw [pow_zero] at hn
      have : W = ⊥ := Subgroup.card_eq_one.mp hn
      rw [this]
      infer_instance
    · have : n = 0 := by
        by_contra hn0
        have : p ^ 2 ≤ p ^ (n + 1) := Nat.pow_le_pow_right hp.out.pos (by omega)
        nlinarith [hp.out.two_le]
      rw [this, zero_add, pow_one] at hn
      exact isCyclic_of_prime_card hn
  have hpairs : ∃ u₁ u₂ : G, u₁ ∈ c.T₀ ∧ u₂ ∈ c.T₀ ∧ u₁ ≠ 1 ∧ u₂ ≠ 1 ∧ u₁ ≠ u₂ ∧
      1 < Nat.card (W ⊓ Subgroup.centralizer ({u₁} : Set G) : Subgroup G) ∧
      1 < Nat.card (W ⊓ Subgroup.centralizer ({u₂} : Set G) : Subgroup G) := by
    have ha0 := (Nat.card_pos (α := (W ⊓ Subgroup.centralizer ({h.t} : Set G) : Subgroup G)))
    have hb0 := (Nat.card_pos (α := (W ⊓ Subgroup.centralizer ({c.w} : Set G) : Subgroup G)))
    have hc0 := (Nat.card_pos
      (α := (W ⊓ Subgroup.centralizer ({h.t * c.w} : Set G) : Subgroup G)))
    set A := Nat.card (W ⊓ Subgroup.centralizer ({h.t} : Set G) : Subgroup G)
    set B := Nat.card (W ⊓ Subgroup.centralizer ({c.w} : Set G) : Subgroup G)
    set C := Nat.card (W ⊓ Subgroup.centralizer ({h.t * c.w} : Set G) : Subgroup G)
    by_cases hA : 1 < A
    · by_cases hB : 1 < B
      · exact ⟨_, _, c.t_mem_T₀, c.w_mem_T₀, h.t_ne_one, c.w_ne_one, c.t_ne_w, hA, hB⟩
      · by_cases hC : 1 < C
        · exact ⟨_, _, c.t_mem_T₀, c.tw_mem_T₀, h.t_ne_one, c.tw_ne_one, c.t_ne_tw, hA, hC⟩
        · exfalso
          have hB1 : B = 1 := by omega
          have hC1 : C = 1 := by omega
          rw [hB1, hC1] at hBW
          omega
    · have hA1 : A = 1 := by omega
      by_cases hB : 1 < B
      · by_cases hC : 1 < C
        · exact ⟨_, _, c.w_mem_T₀, c.tw_mem_T₀, c.w_ne_one, c.tw_ne_one, c.w_ne_tw, hB, hC⟩
        · exfalso
          have hC1 : C = 1 := by omega
          rw [hA1, hC1] at hBW
          omega
      · exfalso
        have hB1 : B = 1 := by omega
        rw [hA1, hB1] at hBW
        nlinarith
  obtain ⟨u₁, u₂, hu₁T, hu₂T, hu₁1, hu₂1, hu₁₂, hz₁, hz₂⟩ := hpairs
  have := Finite.one_lt_card_iff_nontrivial.mp hz₁
  obtain ⟨⟨z₁, hz₁W, hz₁u⟩, hz₁1⟩ := exists_ne (1 : (W ⊓ Subgroup.centralizer ({u₁} : Set G) :
    Subgroup G))
  have := Finite.one_lt_card_iff_nontrivial.mp hz₂
  obtain ⟨⟨z₂, hz₂W, hz₂u⟩, hz₂1⟩ := exists_ne (1 : (W ⊓ Subgroup.centralizer ({u₂} : Set G) :
    Subgroup G))
  have hz₁1' : z₁ ≠ 1 := fun h0 => hz₁1 (Subtype.ext h0)
  have hz₂1' : z₂ ≠ 1 := fun h0 => hz₂1 (Subtype.ext h0)
  have ho₁ : orderOf z₁ = p := orderOf_eq_prime (pow_eq_one_of_mem_omegaZ hz₁W) hz₁1'
  have ho₂ : orderOf z₂ = p := orderOf_eq_prime (pow_eq_one_of_mem_omegaZ hz₂W) hz₂1'
  have hu₁o := c.orderOf_of_mem hu₁T hu₁1
  have hu₂o := c.orderOf_of_mem hu₂T hu₂1
  have hzu₁ : z₁ * u₁ = u₁ * z₁ := Subgroup.mem_centralizer_singleton_iff.mp hz₁u
  have hzu₂ : z₂ * u₂ = u₂ * z₂ := Subgroup.mem_centralizer_singleton_iff.mp hz₂u
  obtain ⟨g, k, hgk⟩ := h.exists_conj_zpow_eq hp3 c hpq ho₁ ho₂ hu₁o hu₂o hzu₁ hzu₂
  obtain ⟨n, hnN, hn⟩ := exists_mem_normalizer_conj_of_mem_centralizer P
    (mem_centralizer_of_mem_omegaZ (Subgroup.zpow_mem _ hz₁W k))
    (mem_centralizer_of_mem_omegaZ hz₂W) hgk
  set u₁' := n * u₁ * n⁻¹ with hu₁'
  have hu₁'o : orderOf u₁' = 2 := by
    rw [hu₁', ← MulAut.conj_apply, MulEquiv.orderOf_eq, hu₁o]
  have hu₁'z : u₁' * z₂ = z₂ * u₁' := by
    have hc : Commute (z₁ ^ k) u₁ := (Commute.zpow_left (hzu₁ : Commute z₁ u₁) k)
    rw [← hn, hu₁']
    calc n * u₁ * n⁻¹ * (n * z₁ ^ k * n⁻¹) = n * (u₁ * z₁ ^ k) * n⁻¹ := by group
      _ = n * (z₁ ^ k * u₁) * n⁻¹ := by rw [hc.eq]
      _ = n * z₁ ^ k * n⁻¹ * (n * u₁ * n⁻¹) := by group
  set Y := Subgroup.centralizer ({z₂} : Set G) ⊓ Subgroup.normalizer ((P : Subgroup G) : Set G)
  have hu₁'Y : u₁' ∈ Y := ⟨Subgroup.mem_centralizer_singleton_iff.mpr hu₁'z,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hnN (hT₀P hu₁T)) (Subgroup.inv_mem _ hnN)⟩
  have hu₂Y : u₂ ∈ Y := ⟨Subgroup.mem_centralizer_singleton_iff.mpr hzu₂.symm, hT₀P hu₂T⟩
  have hY4 : ¬ 4 ∣ Nat.card Y := fun h4 =>
    h.not_four_dvd_card_centralizer hp3 c hpq ho₂ hu₂o hzu₂
      (h4.trans (Subgroup.card_dvd_of_le inf_le_left))
  obtain ⟨m, hm⟩ := exists_conj_of_not_four_dvd hY4 (a := ⟨u₁', hu₁'Y⟩) (b := ⟨u₂, hu₂Y⟩)
    (by rw [Subgroup.orderOf_mk]; exact hu₁'o) (by rw [Subgroup.orderOf_mk]; exact hu₂o)
  have hm' : (m : G) * n * u₁ * ((m : G) * n)⁻¹ = u₂ := by
    have := congrArg Subtype.val hm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [← this, hu₁']
    group
  have hmnN : (m : G) * n ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ m.2.2 hnN
  set N := Subgroup.normalizer ((P : Subgroup G) : Set G)
  have hN4 : 4 ∣ Nat.card N := by
    have := Subgroup.card_dvd_of_le hT₀P
    rwa [c.isKleinFour_T₀.card_four] at this
  have hTcard : Nat.card (c.T₀.subgroupOf N) = 2 ^ (Nat.card N).factorization 2 := by
    rw [factorization_two_eq_two hN4 h8,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₀P).toEquiv, c.isKleinFour_T₀.card_four]
    norm_num
  let T : Sylow 2 N := Sylow.ofCard _ hTcard
  have hcT : ∀ {u : G} (hu : u ∈ c.T₀),
      (⟨u, hT₀P hu⟩ : N) ∈ Subgroup.centralizer ((T : Subgroup N) : Set N) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subtype.ext (c.comm_of_mem hv hu)
  obtain ⟨k₀, hk₀N, hk₀⟩ := exists_mem_normalizer_conj_of_mem_centralizer T (hcT hu₁T)
    (hcT hu₂T) (g := ⟨_, hmnN⟩) (Subtype.ext (by simpa using hm'))
  have hk₀G : (k₀ : G) ∈ Subgroup.normalizer (c.T₀ : Set G) := by
    have : k₀ ∈ (Subgroup.normalizer (c.T₀ : Set G)).subgroupOf N := by
      rw [Subgroup.subgroupOf_normalizer_eq hT₀P]
      exact hk₀N
    exact this
  have hk₀' : (k₀ : G) * u₁ * (k₀ : G)⁻¹ = u₂ := by
    simpa using congrArg Subtype.val hk₀
  set Z := N ⊓ Subgroup.normalizer (c.T₀ : Set G)
  have hdvd6 := relIndex_inf_centralizer_dvd_six c.isKleinFour_T₀ N
  have hle : N ⊓ Subgroup.centralizer (c.T₀ : Set G) ≤ Z :=
    inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)
  have hk₀Z : (k₀ : G) ∈ Z := ⟨k₀.2, hk₀G⟩
  have hk₀C : (k₀ : G) ∉ N ⊓ Subgroup.centralizer (c.T₀ : Set G) := by
    rintro ⟨-, hC⟩
    apply hu₁₂
    rw [← hk₀', (Subgroup.mem_centralizer_iff.mp hC u₁ hu₁T).symm, mul_inv_cancel_right]
  have hcardZ := card_mul_relIndex hle
  set r := (N ⊓ Subgroup.centralizer (c.T₀ : Set G)).relIndex Z with hr
  have hr1 : r ≠ 1 := fun h1 => hk₀C ((Subgroup.relIndex_eq_one.mp h1) hk₀Z)
  have hT₀C : c.T₀ ≤ N ⊓ Subgroup.centralizer (c.T₀ : Set G) := le_inf hT₀P (fun x hx => by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact c.comm_of_mem hy hx)
  have h4C : 4 ∣ Nat.card (N ⊓ Subgroup.centralizer (c.T₀ : Set G) : Subgroup G) := by
    have := Subgroup.card_dvd_of_le hT₀C
    rwa [c.isKleinFour_T₀.card_four] at this
  have hr2 : ¬ 2 ∣ r := by
    intro h2
    apply h8
    have : 4 * 2 ∣ Nat.card Z := hcardZ ▸ Nat.mul_dvd_mul h4C h2
    exact this.trans (Subgroup.card_dvd_of_le inf_le_left)
  have hr3 : r = 3 := eq_three_of_dvd_six hdvd6 hr2 hr1
  have h3Z : 3 ∣ Nat.card Z := ⟨_, by rw [← hcardZ, hr3, mul_comm]⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := Z) 3 h3Z
  refine ⟨s, s.2.1, s.2.2, ?_⟩
  rw [← Subgroup.orderOf_coe] at hs
  exact hs

end JTHyp

end CFSG.Walter.JT

module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP10Act

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

theorem pow_three_of_card_six {Q : Type*} [Group Q] [Finite Q] (hQ : Nat.card Q = 6) {a b : Q}
    (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : (a * b) ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Q) 3 (by rw [hQ]; norm_num)
  set C := Subgroup.zpowers x with hC
  have hcard : Nat.card C = 3 := by rw [hC, Nat.card_zpowers, hx]
  have hidx : C.index = 2 := by
    have := C.index_mul_card
    rw [hcard, hQ] at this
    omega
  have hnot : ∀ y : Q, y * y = 1 → y ≠ 1 → y ∉ C := by
    intro y hy hy1 hyC
    have h1 : orderOf y ∣ Nat.card C := Subgroup.orderOf_dvd_natCard C hyC
    have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hy)
    rw [hcard] at h1
    have : orderOf y ∣ Nat.gcd 3 2 := Nat.dvd_gcd h1 h2
    have h3 : orderOf y = 1 := by simpa using this
    exact hy1 (orderOf_eq_one_iff.1 h3)
  have hab : a * b ∈ C := by
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    exact iff_of_false (hnot a ha ha1) (hnot b hb hb1)
  have := pow_card_eq_one' (x := (⟨a * b, hab⟩ : C))
  rw [hcard] at this
  exact congrArg Subtype.val this

theorem fhatA_mem_A2h : fhatA ∈ A2h := ⟨fhatL, A_cent_check.2.2.2.2.2.1, repL_fhat⟩

theorem A2h_le_Kh : A2h ≤ p10Kh := fun _ hg =>
  mem_p10Kh.2 ⟨mem_p10Nh.2 (Subgroup.le_normalizer hg),
    Subgroup.mem_centralizer_singleton_iff.2 (A2h_comm hg fhatA_mem_A2h)⟩

namespace RhoData

variable {G : Type} [Group G] (d : RhoData G)

@[expose] noncomputable def A : Subgroup G := A2h.map d.ι

@[expose] noncomputable def H : Subgroup G := Subgroup.normalizer (d.A : Set G)

@[expose] noncomputable def H0 : Subgroup G := p10Nh.map d.ι

@[expose] noncomputable def N0 : Subgroup G := p10Kh.map d.ι

theorem H0_le_H [Finite G] : d.H0 ≤ d.H := by
  rintro _ ⟨a, ha, rfl⟩
  refine normalizer_of_conj_le fun s hs => ?_
  obtain ⟨b, hb, rfl⟩ := hs
  have ha' : a ∈ Subgroup.normalizer (A2h : Set Ah) := mem_p10Nh.1 ha
  refine ⟨a * b * a⁻¹, (Subgroup.mem_normalizer_iff.1 ha' b).1 hb, ?_⟩
  simp

theorem N0_le_H0 : d.N0 ≤ d.H0 := Subgroup.map_mono p10Kh_le_Nh

theorem rho_mem_H [Finite G] :
    d.ρ ∈ d.H := by
  refine normalizer_of_conj_le fun s hs => ?_
  obtain ⟨b, hb, rfl⟩ := hs
  obtain ⟨l, -, hl⟩ := id hb
  obtain ⟨p, -, hp⟩ := d.conj_Kh (A2h_le_Kh hb) hl
  exact ⟨b * fhatA ^ p, A2h.mul_mem hb (A2h.pow_mem fhatA_mem_A2h p), hp.symm⟩

theorem card_H0 :
    Nat.card d.H0 = 192 := by
  rw [H0, Subgroup.card_map_of_injective d.inj, card_Nh_Kh.1]

theorem card_N0 :
    Nat.card d.N0 = 96 := by
  rw [N0, Subgroup.card_map_of_injective d.inj, card_Nh_Kh.2]

theorem rho_not_mem_H0 : d.ρ ∉ d.H0 := fun h => by
  obtain ⟨a, -, ha⟩ := h
  exact d.not_mem ⟨a, ha⟩

theorem H_eq_sup [Finite G]
    (hH : Nat.card d.H = 576) : d.H = d.H0 ⊔ Subgroup.zpowers d.ρ := by
  set J := d.H0 ⊔ Subgroup.zpowers d.ρ with hJ
  have hJH : J ≤ d.H :=
    sup_le d.H0_le_H (Subgroup.zpowers_le.2 d.rho_mem_H)
  have hH0J : d.H0 ≤ J := le_sup_left
  have hρJ : d.ρ ∈ J := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hH0J
  obtain ⟨t, ht⟩ := Subgroup.card_dvd_of_le hJH
  rw [d.card_H0] at hm
  have hmt : m * t = 3 := by
    have : 192 * (m * t) = 192 * 3 := by
      rw [← mul_assoc, ← hm, ← ht, hH]
    omega
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact d.rho_not_mem_H0 (Subgroup.eq_of_le_of_card_ge hH0J (by rw [hm, d.card_H0]) ▸ hρJ)
  have hm3 : m = 3 := by
    have : m ∣ 3 := ⟨t, hmt.symm⟩
    rcases (Nat.dvd_prime Nat.prime_three).1 this with h | h
    · exact absurd h hm1
    · exact h
  have ht1 : t = 1 := by
    rw [hm3] at hmt
    omega
  refine (Subgroup.eq_of_le_of_card_ge hJH ?_).symm
  rw [hm, hm3]
  omega

theorem H0_le_normalizer_N0 [Finite G] :
    d.H0 ≤ Subgroup.normalizer (d.N0 : Set G) := by
  rintro _ ⟨a, ha, rfl⟩
  refine normalizer_of_conj_le fun s hs => ?_
  obtain ⟨k, hk, rfl⟩ := hs
  have h1 : (⟨k, p10Kh_le_Nh hk⟩ : p10Nh) ∈ p10Kh.subgroupOf p10Nh := hk
  have := normal_Kh.conj_mem _ h1 ⟨a, ha⟩
  exact ⟨a * k * a⁻¹, this, by simp⟩

theorem rho_mem_normalizer_N0 [Finite G] :
    d.ρ ∈ Subgroup.normalizer (d.N0 : Set G) := by
  refine normalizer_of_conj_le fun s hs => ?_
  obtain ⟨k, hk, rfl⟩ := hs
  obtain ⟨l, -, hl⟩ := rep_mem_Kh k hk
  obtain ⟨p, -, hp⟩ := d.conj_Kh hk hl
  exact ⟨k * fhatA ^ p, p10Kh.mul_mem hk (p10Kh.pow_mem fhatA_mem_Kh p), hp.symm⟩

theorem H_le_normalizer_N0 [Finite G]
    (hH : Nat.card d.H = 576) : d.H ≤ Subgroup.normalizer (d.N0 : Set G) := by
  rw [d.H_eq_sup hH]
  exact sup_le d.H0_le_normalizer_N0 (Subgroup.zpowers_le.2 d.rho_mem_normalizer_N0)

theorem hh_sq_mem_Kh :
    p10hA * p10hA ∈ p10Kh := by
  obtain ⟨g, hg, hrep⟩ := exists_Kh_rep (p10_K_check.2.2.2.2.2.2.1)
  have h' : RepL (comp p10hL p10hL) ((p10hA * p10hA : Ah) : P45) := repL_mul repL_p10hA repL_p10hA
  have : g = p10hA * p10hA := Subtype.ext (eq_of_repL hrep h')
  rwa [this] at hg

theorem triangle_mem [Finite G]
    (hH : Nat.card d.H = 576) : (d.ρ * d.ι p10hA) ^ 3 ∈ d.N0 := by
  have hN0H : d.N0 ≤ d.H := d.N0_le_H0.trans d.H0_le_H
  have hh : d.ι p10hA ∈ d.H := d.H0_le_H ⟨p10hA, p10hA_mem_Nh, rfl⟩
  have hnorm : (d.N0.subgroupOf d.H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hN0H]
    intro n x hn hx
    exact (Subgroup.mem_normalizer_iff.1 (d.H_le_normalizer_N0 hH hx) n).1 hn
  have hQ : Nat.card (↥d.H ⧸ d.N0.subgroupOf d.H) = 6 := by
    have h := (d.N0.subgroupOf d.H).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN0H).toEquiv, d.card_N0, hH] at h
    show (d.N0.subgroupOf d.H).index = 6
    omega
  have hρN : d.ρ ∉ d.N0 := fun h => d.rho_not_mem_H0 (d.N0_le_H0 h)
  have hhN : d.ι p10hA ∉ d.N0 := by
    rintro ⟨k, hk, hkh⟩
    exact p10hA_not_mem_Kh ((d.inj hkh) ▸ hk)
  have key := pow_three_of_card_six hQ
    (a := (QuotientGroup.mk ⟨d.ρ, d.rho_mem_H⟩ : ↥d.H ⧸ d.N0.subgroupOf d.H))
    (b := (QuotientGroup.mk ⟨d.ι p10hA, hh⟩ : ↥d.H ⧸ d.N0.subgroupOf d.H))
    (by
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      show d.ρ * d.ρ ∈ d.N0
      rw [← pow_two, d.sq]
      exact ⟨fhatA, fhatA_mem_Kh, rfl⟩)
    (by
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      show d.ι p10hA * d.ι p10hA ∈ d.N0
      exact ⟨p10hA * p10hA, hh_sq_mem_Kh, by rw [map_mul]⟩)
    (by
      rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hρN)
    (by
      rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hhN)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at key
  exact key

end RhoData

end CFSG.Quasithin.H13.F431.U42Aut

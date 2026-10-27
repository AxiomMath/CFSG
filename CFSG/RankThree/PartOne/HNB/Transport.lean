module

public import CFSG.RankThree.PartOne.HNB.Moving
public import CFSG.RankThree.PartOne.S11.PlaneData

public section

namespace CFSG.RankThree.PartOne.HNB

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank
open scoped Pointwise commutatorElement

namespace Actor

variable {G : Type} [Group G] {A L : Subgroup G} (a : Actor G A L)

abbrev A0H : Subgroup a.H := a.A0.subgroupOf a.H

abbrev RH : Subgroup a.H := a.R.subgroupOf a.H

abbrev KH : Subgroup a.H := a.K.subgroupOf a.H

abbrev YH : Subgroup a.H := a.Y.subgroupOf a.H

theorem isElementaryAbelian_A0H : IsElementaryAbelian 5 a.A0H := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have := a.isElementaryAbelian_A0
  exact CFSG.IsElementaryAbelian.subgroupOf a.A0_le_H

theorem card_A0H : Nat.card a.A0H = 125 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe a.A0_le_H).toEquiv, a.card_A0]
  norm_num

theorem cH_mem_A0H : a.cH ∈ a.A0H := Subgroup.mem_subgroupOf.mpr a.c_mem_A0

theorem bH_mem_A0H : a.bH ∈ a.A0H := Subgroup.mem_subgroupOf.mpr a.b_mem_A0

end Actor

namespace Successor

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {a : Actor G A L} (s : Successor a)

@[expose] noncomputable def rho (h : SteinbergBM.SectionTenSetup G 5 A) :
    ↥(a.A0H) →* MulAut (↥s.X ⧸ Subgroup.center ↥s.X) :=
  centerQuotientAction (s.A0_le_normalizer h)

@[expose] noncomputable def beta (h : SteinbergBM.SectionTenSetup G 5 A) :
    MulAut (↥s.X ⧸ Subgroup.center ↥s.X) :=
  s.rho h ⟨a.cH, a.cH_mem_A0H⟩

@[expose] noncomputable def Lambda (h : SteinbergBM.SectionTenSetup G 5 A) :
    Subgroup (MulAut (↥s.X ⧸ Subgroup.center ↥s.X)) :=
  (s.rho h).range

theorem rho_eq_one_iff (h : SteinbergBM.SectionTenSetup G 5 A) (hq : CFSG.IsQuasisimple s.X)
    (g : a.A0H) : s.rho h g = 1 ↔ ∀ x : s.X, (g : a.H) * x = x * (g : a.H) := by
  have : Group.IsPerfect s.X := hq.1
  constructor
  · intro h1 x
    exact commute_of_centerQuotientAction_eq_one (s.A0_le_normalizer h) g h1 x
  · intro hc
    rw [rho, centerQuotientAction_eq_one_iff]
    intro l
    have hl := hc l
    have : (s.X.normalizerMonoidHom ⟨(g : a.H), s.A0_le_normalizer h g.2⟩ l : s.X) = l := by
      apply Subtype.ext
      rw [coe_normalizerMonoidHom_apply]
      calc (g : a.H) * l * (g : a.H)⁻¹ = l * (g : a.H) * (g : a.H)⁻¹ := by rw [hl]
        _ = l := by group
    rw [this, div_self']
    exact Subgroup.one_mem _

theorem rho_b (h : SteinbergBM.SectionTenSetup G 5 A) (hq : CFSG.IsQuasisimple s.X) :
    s.rho h ⟨a.bH, a.bH_mem_A0H⟩ = 1 := by
  rw [s.rho_eq_one_iff h hq]
  intro x
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_singleton_iff.mp x.1.2).symm

theorem beta_ne_one (h : SteinbergBM.SectionTenSetup G 5 A) (hq : CFSG.IsQuasisimple s.X) :
    s.beta h ≠ 1 := by
  intro h1
  apply s.c_not_mem_kernel h
  have hc := (s.rho_eq_one_iff h hq _).mp h1
  refine mem_thetaQuotientCentralizer_iff.mpr ⟨Subgroup.mem_top _, s.A0_le_normalizer' h a.c_mem_A0,
    fun k hk => ?_⟩
  obtain ⟨hkH, hkX⟩ := s.mem_X'_iff.mp hk
  have := hc ⟨⟨k, hkH⟩, hkX⟩
  have h2 : a.c * k = k * a.c := congrArg (fun z : a.H => (z : G)) this
  have h3 : a.c * k * a.c⁻¹ * k⁻¹ = 1 := by
    rw [h2]
    group
  rw [h3]
  exact Subgroup.one_mem _

@[expose] noncomputable def kerG (h : SteinbergBM.SectionTenSetup G 5 A) : Subgroup G :=
  ((s.rho h).ker.map a.A0H.subtype).map a.H.subtype

theorem mem_kerG_iff (h : SteinbergBM.SectionTenSetup G 5 A) {g : G} :
    g ∈ s.kerG h ↔ ∃ x : a.A0H, x ∈ (s.rho h).ker ∧ ((x : a.H) : G) = g := by
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩

theorem kerG_le_B (h : SteinbergBM.SectionTenSetup G 5 A) (hq : CFSG.IsQuasisimple s.X) :
    s.kerG h ≤ a.B := by
  intro g hg
  obtain ⟨x, hx, rfl⟩ := (s.mem_kerG_iff h).mp hg
  have hxA : ((x : a.H) : G) ∈ a.A0 := Subgroup.mem_subgroupOf.mp x.2
  refine a.centralizer_K_inf_A0_le_B hxA fun k hk => ?_
  have h1 := (s.rho_eq_one_iff h hq x).mp hx ⟨⟨k, a.K_le_H hk⟩, s.hKX (Subgroup.mem_subgroupOf.mpr hk)⟩
  exact congrArg (fun z : a.H => (z : G)) h1

theorem zpowers_b_le_kerG (h : SteinbergBM.SectionTenSetup G 5 A) (hq : CFSG.IsQuasisimple s.X) :
    Subgroup.zpowers a.b ≤ s.kerG h := by
  rw [Subgroup.zpowers_le, mem_kerG_iff]
  exact ⟨⟨a.bH, a.bH_mem_A0H⟩, s.rho_b h hq, rfl⟩

theorem c_not_mem_kerG (h : SteinbergBM.SectionTenSetup G 5 A) (hq : CFSG.IsQuasisimple s.X) :
    a.c ∉ s.kerG h := by
  intro hc
  obtain ⟨x, hx, hxc⟩ := (s.mem_kerG_iff h).mp hc
  have : x = ⟨a.cH, a.cH_mem_A0H⟩ := Subtype.ext (Subtype.ext hxc)
  rw [this] at hx
  exact s.beta_ne_one h hq hx

theorem card_ker_rho (h : SteinbergBM.SectionTenSetup G 5 A) (hq : CFSG.IsQuasisimple s.X) :
    Nat.card (s.rho h).ker = 5 := by
  have hcard : Nat.card (s.kerG h) = Nat.card (s.rho h).ker := by
    rw [kerG, Subgroup.card_map_of_injective a.H.subtype_injective,
      Subgroup.card_map_of_injective a.A0H.subtype_injective]
  have hle := s.kerG_le_B h hq
  have hdvd25 : Nat.card (s.kerG h) ∣ 25 := by
    have := Subgroup.card_dvd_of_le hle
    rwa [a.card_B] at this
  have hb5 : orderOf a.b = 5 := by
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hAe : IsElementaryAbelian 5 a.A0 := a.isElementaryAbelian_A0
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 5) (A := a.A0) a.b
      a.b_mem_A0) a.b_ne_one
  have hdvd5 : 5 ∣ Nat.card (s.kerG h) := by
    have := Subgroup.card_dvd_of_le (s.zpowers_b_le_kerG h hq)
    rwa [Nat.card_zpowers, hb5] at this
  have hne : Nat.card (s.kerG h) ≠ 25 := by
    intro h25
    have heq : s.kerG h = a.B := Subgroup.eq_of_le_of_card_ge hle (by rw [h25, a.card_B])
    exact s.c_not_mem_kerG h hq (heq ▸ a.c_mem_B)
  have h25 : (25 : ℕ) = 5 ^ 2 := by norm_num
  rw [h25] at hdvd25 hne
  obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp hdvd25
  rw [← hcard]
  interval_cases i
  · rw [hci] at hdvd5; omega
  · rw [hci]; norm_num
  · exact absurd hci hne

theorem card_Lambda (h : SteinbergBM.SectionTenSetup G 5 A) (hq : CFSG.IsQuasisimple s.X) :
    Nat.card (s.Lambda h) = 5 ^ 2 := by
  have := Subgroup.card_ker_mul_card_range (s.rho h)
  rw [a.card_A0H, s.card_ker_rho h hq] at this
  unfold Lambda
  omega

theorem isElementaryAbelian_Lambda (h : SteinbergBM.SectionTenSetup G 5 A) :
    IsElementaryAbelian 5 (s.Lambda h) :=
  isElementaryAbelian_range a.isElementaryAbelian_A0H (s.rho h)

theorem beta_mem_Lambda (h : SteinbergBM.SectionTenSetup G 5 A) : s.beta h ∈ s.Lambda h :=
  ⟨_, rfl⟩

theorem orderOf_beta (h : SteinbergBM.SectionTenSetup G 5 A) (hq : CFSG.IsQuasisimple s.X) :
    orderOf (s.beta h) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ (s.beta_ne_one h hq)
  rw [beta, ← map_pow]
  have : (⟨a.cH, a.cH_mem_A0H⟩ : a.A0H) ^ 5 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    show a.c ^ 5 = 1
    rw [← a.hc5]
    exact pow_orderOf_eq_one a.c
  rw [this, map_one]

end Successor

end CFSG.RankThree.PartOne.HNB

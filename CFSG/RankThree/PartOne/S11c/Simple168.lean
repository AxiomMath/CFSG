module

public import CFSG.RankThree.PartOne.S11c.SporadicPlaneKit

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG

theorem mem_normalizer_of_forall_conj_mem {G : Type*} [Group G] [Finite G] {S : Subgroup G}
    {d : G} (h : ∀ s ∈ S, d * s * d⁻¹ ∈ S) : d ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨h g, fun hg => ?_⟩
  have hle : S.map (MulAut.conj d).toMonoidHom ≤ S := by
    rintro _ ⟨u, hu, rfl⟩
    exact h u hu
  have heq : S.map (MulAut.conj d).toMonoidHom = S :=
    Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (f := (MulAut.conj d).toMonoidHom)
        (MulAut.conj d).injective).ge
  rw [← heq] at hg
  obtain ⟨u, hu, hux⟩ := hg
  have : u = g := by
    simpa [MulAut.conj_apply] using hux
  rwa [← this]

theorem simple168_no_index_three {D : Type*} [Group D] [Finite D] [IsSimpleGroup D]
    (hcard : Nat.card D = 168) (S : Subgroup D) (hS : S.index = 3) : False := by
  have hfin : S.FiniteIndex := ⟨by omega⟩
  have hnorm : S.normalCore.Normal := inferInstance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S.normalCore with h | h
  · have hdvd := S.index_normalCore_dvd_factorial_index
    rw [h, Subgroup.index_bot, hcard, hS] at hdvd
    norm_num [Nat.factorial] at hdvd
  · have : S = ⊤ := by
      rw [eq_top_iff, ← h]
      exact S.normalCore_le
    rw [this, Subgroup.index_top] at hS
    omega

theorem simple168_no_normalized_two_subgroup {D : Type*} [Group D] [Finite D] [IsSimpleGroup D]
    (hcard : Nat.card D = 168) (S : Subgroup D) (hS2 : IsPGroup 2 S) (hS8 : 8 ≤ Nat.card S)
    (d : D) (hd : orderOf d = 7) (hdS : ∀ s ∈ S, d * s * d⁻¹ ∈ S) : False := by
  have hS8' : Nat.card S = 8 := by
    have := card_le_of_isPGroup_two_of_le (C := (⊤ : Subgroup D)) (R2 := S) (a := 3) (m := 21)
      (by rw [Subgroup.card_top, hcard]; norm_num) (by norm_num) hS2 le_top
    omega
  set N : Subgroup D := Subgroup.normalizer (S : Set D) with hN
  have hSN : S ≤ N := Subgroup.le_normalizer
  have hdN : d ∈ N := mem_normalizer_of_forall_conj_mem hdS
  have h8 : 8 ∣ Nat.card N := hS8' ▸ Subgroup.card_dvd_of_le hSN
  have h7 : 7 ∣ Nat.card N := by
    have h1 : Nat.card (Subgroup.zpowers d) ∣ Nat.card N :=
      Subgroup.card_dvd_of_le ((Subgroup.zpowers_le).mpr hdN)
    rwa [Nat.card_zpowers, hd] at h1
  have h56 : 56 ∣ Nat.card N := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 8 7) h8 h7
    simpa using this
  have hNd : Nat.card N ∣ 168 := hcard ▸ Subgroup.card_subgroup_dvd_card N
  have hmul : Nat.card N * N.index = 168 := by rw [← hcard]; exact N.card_mul_index
  obtain ⟨m, hm⟩ := h56
  have hm3 : m ∣ 3 := by
    rw [hm] at hNd
    have : 56 * m ∣ 56 * 3 := by simpa using hNd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  rcases (Nat.dvd_prime Nat.prime_three).1 hm3 with h1 | h1
  ·
    subst h1
    apply simple168_no_index_three hcard N
    rw [hm] at hmul
    omega
  ·
    subst h1
    have hidx : N.index = 1 := by rw [hm] at hmul; omega
    have hNtop : N = ⊤ := Subgroup.index_eq_one.mp hidx
    have hnormal : S.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S with h | h
    · rw [h, Subgroup.card_bot] at hS8'
      omega
    · rw [h, Subgroup.card_top, hcard] at hS8'
      omega


theorem seven_record_no_move {M : Type*} [Group M] [Finite M] {R C : Subgroup M} {x f : M}
    (hC : C = centralizer ({x} : Set M) ⊓ R) (hxR : x ∈ R) (hCcard : Nat.card C = 1176)
    (hxord : orderOf x = 7) (hDs : IsSimpleGroup (⁅C, C⁆ : Subgroup M))
    (hDnab : ∃ g ∈ (⁅C, C⁆ : Subgroup M), ∃ h ∈ (⁅C, C⁆ : Subgroup M), g * h ≠ h * g)
    (hDcard : Nat.card (⁅C, C⁆ : Subgroup M) = 168)
    (hfR : f ∈ R) (hford : orderOf f = 7) (hfx : f * x = x * f)
    {R2 : Subgroup M} (hR2 : IsPGroup 2 R2) (hle : R2 ≤ R ⊓ centralizer ({x} : Set M))
    (hnorm : ∀ r ∈ R2, f * r * f⁻¹ ∈ R2) (hmove : ∃ r ∈ R2, f * r * f⁻¹ ≠ r)
    (h8 : 8 ≤ Nat.card R2) : False := by
  classical
  set D : Subgroup M := ⁅C, C⁆ with hD
  have hDC : D ≤ C := commutator_self_le C
  have hCx : ∀ c ∈ C, c * x = x * c := fun c hc => by
    rw [hC] at hc
    exact Subgroup.mem_centralizer_singleton_iff.mp hc.1
  have hxC : x ∈ C := by
    rw [hC]
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, hxR⟩
  have hfC : f ∈ C := by
    rw [hC]
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr hfx, hfR⟩
  have hR2C : R2 ≤ C := by
    rw [hC, inf_comm]
    exact hle
  have hx7 : x ^ 7 = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
  have hf7 : f ^ 7 = 1 := by rw [← hford]; exact pow_orderOf_eq_one f
  have hxD : x ∉ D := by
    intro hxD
    have : IsSimpleGroup D := hDs
    have hnab : ∃ a b : D, a * b ≠ b * a := by
      obtain ⟨g, hg, h, hh, hne⟩ := hDnab
      exact ⟨⟨g, hg⟩, ⟨h, hh⟩, fun e => hne (congrArg Subtype.val e)⟩
    have hz : (⟨x, hxD⟩ : D) ∈ Subgroup.center D := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hCx g (hDC g.2))
    rw [center_eq_bot_of_simple hnab, Subgroup.mem_bot] at hz
    have : x = 1 := congrArg Subtype.val hz
    rw [this, orderOf_one] at hxord
    omega
  have hNn : (D.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDC).mpr (le_normalizer_commutator_self C)
  have hNcard : Nat.card (D.subgroupOf C) = 168 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv, hDcard]
  have hQcard : Nat.card (C ⧸ D.subgroupOf C) = 7 := by
    have h := (D.subgroupOf C).card_eq_card_quotient_mul_card_subgroup
    rw [hCcard, hNcard] at h
    omega
  let π : C →* C ⧸ D.subgroupOf C := QuotientGroup.mk' (D.subgroupOf C)
  have hπ7 : ∀ c : C ⧸ D.subgroupOf C, c ^ 7 = 1 := fun c => by
    rw [← hQcard]
    exact pow_card_eq_one'
  have hR2D : R2 ≤ D := by
    intro r hr
    obtain ⟨k, hk⟩ := hR2 ⟨r, hr⟩
    have hk' : (⟨r, hR2C hr⟩ : C) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    have h1 : (π ⟨r, hR2C hr⟩) ^ 2 ^ k = 1 := by rw [← map_pow, hk', map_one]
    have h2 : orderOf (π ⟨r, hR2C hr⟩) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf (π ⟨r, hR2C hr⟩) ∣ 7 := orderOf_dvd_of_pow_eq_one (hπ7 _)
    have hcop : Nat.Coprime (2 ^ k) 7 := Nat.Coprime.pow_left k (by norm_num)
    have h4 : orderOf (π ⟨r, hR2C hr⟩) = 1 := Nat.eq_one_of_dvd_coprimes hcop.symm h3 h2
    have h5 : π ⟨r, hR2C hr⟩ = 1 := orderOf_eq_one_iff.mp h4
    have h6 : (⟨r, hR2C hr⟩ : C) ∈ D.subgroupOf C := (QuotientGroup.eq_one_iff _).mp h5
    exact Subgroup.mem_subgroupOf.mp h6
  have hπx : π ⟨x, hxC⟩ ≠ 1 := by
    intro h1
    exact hxD (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1))
  have hπxord : orderOf (π ⟨x, hxC⟩) = 7 := by
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact orderOf_eq_prime (hπ7 _) hπx
  have hzp : Subgroup.zpowers (π ⟨x, hxC⟩) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hπxord, hQcard]
  obtain ⟨i, hi⟩ : ∃ i : ℤ, (π ⟨x, hxC⟩) ^ i = π ⟨f, hfC⟩ := by
    have : π ⟨f, hfC⟩ ∈ Subgroup.zpowers (π ⟨x, hxC⟩) := by rw [hzp]; exact Subgroup.mem_top _
    exact this
  set d : M := x ^ (-i) * f with hd
  have hdC : d ∈ C := C.mul_mem (C.zpow_mem hxC _) hfC
  have hdD : d ∈ D := by
    have h1 : π ⟨d, hdC⟩ = 1 := by
      have : (⟨d, hdC⟩ : C) = ⟨x, hxC⟩ ^ (-i) * ⟨f, hfC⟩ := Subtype.ext (by simp [hd])
      rw [this, map_mul, map_zpow, zpow_neg, hi, inv_mul_cancel]
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
  have hfd : f = x ^ i * d := by rw [hd]; group
  have hxi : ∀ c ∈ C, c * x ^ i = x ^ i * c := fun c hc =>
    ((Commute.zpow_right (hCx c hc) i)).eq
  have hconj : ∀ r ∈ R2, f * r * f⁻¹ = d * r * d⁻¹ := by
    intro r hr
    have hrC : r ∈ C := hR2C hr
    have hdrd : d * r * d⁻¹ ∈ C := C.mul_mem (C.mul_mem hdC hrC) (C.inv_mem hdC)
    have h1 := hxi _ hdrd
    calc f * r * f⁻¹ = (x ^ i * d) * r * (x ^ i * d)⁻¹ := by rw [← hfd]
      _ = (x ^ i * (d * r * d⁻¹)) * (x ^ i)⁻¹ := by group
      _ = ((d * r * d⁻¹) * x ^ i) * (x ^ i)⁻¹ := by rw [h1]
      _ = d * r * d⁻¹ := by group
  have hdnorm : ∀ r ∈ R2, d * r * d⁻¹ ∈ R2 := fun r hr => by
    rw [← hconj r hr]
    exact hnorm r hr
  have hdmove : ∃ r ∈ R2, d * r * d⁻¹ ≠ r := by
    obtain ⟨r, hr, hne⟩ := hmove
    exact ⟨r, hr, by rw [← hconj r hr]; exact hne⟩
  have hd1 : d ≠ 1 := by
    rintro h1
    obtain ⟨r, hr, hne⟩ := hdmove
    apply hne
    rw [h1]
    group
  have hd7 : d ^ 7 = 1 := by
    have hcomm : Commute (x ^ (-i)) f := (Commute.zpow_left (Commute.symm (Commute.symm
      (show Commute x f from hfx.symm))) (-i)).symm.symm
    rw [hd, hcomm.mul_pow, hf7, mul_one]
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hx7,
      _root_.one_zpow]
  have hdord : orderOf d = 7 := by
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact orderOf_eq_prime hd7 hd1
  have : IsSimpleGroup D := hDs
  have hS2 : IsPGroup 2 (R2.subgroupOf D) := hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hR2D).symm
  have hS8 : 8 ≤ Nat.card (R2.subgroupOf D) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR2D).toEquiv]
    exact h8
  refine simple168_no_normalized_two_subgroup hDcard (R2.subgroupOf D) hS2 hS8 ⟨d, hdD⟩ ?_ ?_
  · rw [Subgroup.orderOf_mk, hdord]
  · intro s hs
    rw [Subgroup.mem_subgroupOf] at hs ⊢
    exact hdnorm _ hs

end CFSG.RankThree.PartOne

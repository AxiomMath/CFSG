module

public import CFSG.Sporadic.Recognition.JankoWongLemma16c
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS CFSG.Open

section Abstract

variable {G : Type*} [Group G]

theorem mul_pow_three_of_central_commutator {x y c : G} (hyx : y * x = c * (x * y))
    (hxc : x * c = c * x) (hyc : y * c = c * y) (hc3 : c ^ 3 = 1) :
    (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  have hc3' : c * (c * c) = 1 := by simpa [pow_succ, mul_assoc] using hc3
  have h2 : y * y * x = c * c * (x * (y * y)) := by
    calc y * y * x = y * (y * x) := by group
      _ = y * (c * (x * y)) := by rw [hyx]
      _ = (y * c) * (x * y) := by group
      _ = (c * y) * (x * y) := by rw [hyc]
      _ = c * (y * x) * y := by group
      _ = c * (c * (x * y)) * y := by rw [hyx]
      _ = c * c * (x * (y * y)) := by group
  have hx2c : x * x * (c * c) = c * c * (x * x) := by
    calc x * x * (c * c) = x * (x * c) * c := by group
      _ = x * (c * x) * c := by rw [hxc]
      _ = (x * c) * (x * c) := by group
      _ = (c * x) * (c * x) := by rw [hxc]
      _ = c * (x * c) * x := by group
      _ = c * (c * x) * x := by rw [hxc]
      _ = c * c * (x * x) := by group
  have e1 : (x * y) ^ 3 = x * y * x * y * x * y := by simp [pow_succ, mul_assoc]
  have e2 : x ^ 3 * y ^ 3 = x * x * x * (y * y * y) := by simp [pow_succ, mul_assoc]
  rw [e1, e2]
  calc x * y * x * y * x * y = x * (y * x) * y * x * y := by group
    _ = x * (c * (x * y)) * y * x * y := by rw [hyx]
    _ = (x * c) * (x * y) * y * x * y := by group
    _ = (c * x) * (x * y) * y * x * y := by rw [hxc]
    _ = c * x * x * (y * y * x) * y := by group
    _ = c * x * x * (c * c * (x * (y * y))) * y := by rw [h2]
    _ = c * (x * x * (c * c)) * (x * (y * y)) * y := by group
    _ = c * (c * c * (x * x)) * (x * (y * y)) * y := by rw [hx2c]
    _ = (c * (c * c)) * (x * x * x * (y * y * y)) := by group
    _ = x * x * x * (y * y * y) := by rw [hc3', one_mul]

theorem commute_of_coprime_of_commutator_mem_zpowers {a x y : G} (ha3 : a ^ 3 = 1)
    (hxa : x * a = a * x) (hya : y * a = a * y) (hcomm : x * y * x⁻¹ * y⁻¹ ∈ zpowers a)
    {n : ℕ} (hn : y ^ n = 1) (hn3 : ¬ 3 ∣ n) : x * y = y * x := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcomm
  set c : G := x * y * x⁻¹ * y⁻¹ with hc
  have hcx : c * x = x * c := by
    rw [← hk]; exact ((Commute.zpow_left (show Commute a x from hxa.symm) k).eq)
  have hcy : c * y = y * c := by
    rw [← hk]; exact ((Commute.zpow_left (show Commute a y from hya.symm) k).eq)
  have hc3 : c ^ 3 = 1 := by
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha3, one_zpow]
  have hxy : x * y * x⁻¹ = c * y := by rw [hc]; group
  have hpow : (x * y * x⁻¹) ^ n = 1 := by rw [conj_pow, hn]; group
  have hcn : c ^ n = 1 := by
    have h1 : (c * y) ^ n = c ^ n * y ^ n := (Commute.mul_pow (show Commute c y from hcy) n)
    rw [← hxy, hpow, hn, mul_one] at h1
    exact h1.symm
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hn3
  have hc1 : c = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hc3, hcn⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
  have : x * y * x⁻¹ = y := by rw [hxy, hc1, one_mul]
  calc x * y = (x * y * x⁻¹) * x := by group
    _ = y * x := by rw [this]

end Abstract

namespace Setup

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {S : Setup G} (c : Ctx S)

theorem exists_mem_ocl_s_of_card
    {R : Subgroup G} (hR : R ≤ c.OG) (h : 21 < Nat.card R) : ∃ y ∈ R, y ∈ c.ocl c.s := by
  by_contra hno
  push Not at hno
  have hsub : ((R : Set G) \ {1}) ⊆ c.ocl (c.a : G) := by
    rintro y ⟨hyR, hy1⟩
    have hyOG : y ∈ (c.OG : Set G) \ {1} := ⟨hR hyR, hy1⟩
    rw [c.OG_sdiff_one_eq] at hyOG
    rcases hyOG with hy | hy
    · exact absurd hy (hno y hyR)
    · exact hy
  have hR20 : ((R : Set G) \ {1}).ncard ≤ 20 := by
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [← Nat.card_coe_set_eq (c.ocl (c.a : G)), c.card_ocl_a] at this
    exact this
  have hRcard : ((R : Set G) \ {1}).ncard = Nat.card R - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem R.one_mem, ← Nat.card_coe_set_eq]
    rfl
  omega

@[expose] def MG : Subgroup G := (CFSG.oddCore ↥c.Kg).map c.Kg.subtype

theorem MG_le_Kg : c.MG ≤ c.Kg := Subgroup.map_subtype_le _

theorem card_MG : Nat.card c.MG = Nat.card (CFSG.oddCore ↥c.Kg) :=
  Subgroup.card_map_of_injective c.Kg.subtype_injective

theorem mem_MG_iff {m : G} : m ∈ c.MG ↔ ∃ h : m ∈ c.Kg, (⟨m, h⟩ : ↥c.Kg) ∈ CFSG.oddCore ↥c.Kg := by
  constructor
  · rintro ⟨m', hm', rfl⟩
    exact ⟨m'.2, hm'⟩
  · rintro ⟨h, hm⟩
    exact ⟨⟨m, h⟩, hm, rfl⟩

theorem MG_conj {k m : G} (hk : k ∈ c.Kg) (hm : m ∈ c.MG) : k * m * k⁻¹ ∈ c.MG := by
  obtain ⟨hmK, hm'⟩ := c.mem_MG_iff.mp hm
  refine c.mem_MG_iff.mpr ⟨c.Kg.mul_mem (c.Kg.mul_mem hk hmK) (c.Kg.inv_mem hk), ?_⟩
  have := (CFSG.oddCore_normal ↥c.Kg).conj_mem _ hm' ⟨k, hk⟩
  exact this

theorem odd_card_MG : Odd (Nat.card c.MG) := by
  rw [c.card_MG]
  exact CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd

theorem a_mem_Kg' : (c.a : G) ∈ c.Kg := c.a_mem_Kg

theorem IsW.le_Kg
    {W : Subgroup G} (hW : c.IsW W) : W ≤ c.Kg := fun w hw =>
  Subgroup.mem_centralizer_singleton_iff.mpr (hW.comm_a w hw)

theorem IsW.factorization_three_Kg
    {W : Subgroup G} (hW : c.IsW W) : (Nat.card ↥c.Kg).factorization 3 = 6 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKne : Nat.card ↥c.Kg ≠ 0 := Nat.card_pos.ne'
  have hGne : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hle : (Nat.card ↥c.Kg).factorization 3 ≤ (Nat.card G).factorization 3 :=
    (Nat.factorization_le_iff_dvd hKne hGne).mpr (Subgroup.card_subgroup_dvd_card c.Kg) 3
  have hdvd : 3 ^ 6 ∣ Nat.card ↥c.Kg := by
    rw [← hW.card]; exact Subgroup.card_dvd_of_le hW.le_Kg
  have hge : 6 ≤ (Nat.card ↥c.Kg).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hKne).mp hdvd
  rw [hW.factorization_three_card] at hle
  omega

end Ctx

end Setup

end CFSG.Sporadic.Recognition.JankoWong

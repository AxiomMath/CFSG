module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.Mathlib.GroupTheory.AbelianHallNormal
import CFSG.Mathlib.GroupTheory.SylowConj
import CFSG.GroupTheory.WielandtProductFinal
import CFSG.RankThree.PartTwo.KFacts.KP10LinearTwo
import CFSG.RankThree.PartOne.S11d.WeylThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoSyl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open scoped MatrixGroups Pointwise

structure L3Frame (Γ : Type) [Group Γ] (p : ℕ) (k : Type) [Field k] where
  I : Subgroup Γ
  P : Subgroup Γ
  e : Γ
  r : Γ
  Kb : Subgroup Γ
  Zb : Subgroup Γ
  ρ : ↥(P ⊓ centralizer ({e ^ 2} : Set Γ)) →* PGL(Fin 2, k)
  I_normal : I.Normal
  P_normal : P.Normal
  I_le_P : I ≤ P
  mul_mem_of_not_mem : ∀ g h : Γ, g ∉ P → h ∉ P → g * h ∈ P
  mem_I_of_two : ∀ g ∈ P, ∀ n : ℕ, g ^ 2 ^ n = 1 → g ∈ I
  e_mem : e ∈ I
  r_mem : r ∈ I
  e_pow_four : e ^ 4 = 1
  r_sq : r ^ 2 = 1
  r_e : r * e * r⁻¹ = e⁻¹
  e_sq_ne : e ^ 2 ≠ 1
  isCyclic_cent : IsCyclic ↥(I ⊓ centralizer ({e, r} : Set Γ))
  isPGroup_D8 : IsPGroup 2 ↥(Subgroup.closure ({e, r} : Set Γ))
  Kb_le : Kb ≤ P ⊓ centralizer ({e ^ 2} : Set Γ)
  conj_mem_Kb : ∀ g : Γ, g * e ^ 2 = e ^ 2 * g → ∀ x ∈ Kb, g * x * g⁻¹ ∈ Kb
  mem_Zb : ∀ x : Γ, x ∈ Zb ↔ x ∈ P ⊓ centralizer ({e ^ 2} : Set Γ) ∧
    ∀ y ∈ P ⊓ centralizer ({e ^ 2} : Set Γ), x * y = y * x
  isCyclic_Zb : IsCyclic ↥Zb
  eq_one_of_mem_Kb_Zb : ∀ x ∈ Kb, x ∈ Zb → Odd (orderOf x) → x = 1
  ρ_eq_one : ∀ x, ρ x = 1 ↔ (x : Γ) ∈ Zb
  eight_dvd : 8 ∣ Nat.card ρ.range
  ρ_ne : ∀ (he : e ∈ P ⊓ centralizer ({e ^ 2} : Set Γ))
    (hr : r ∈ P ⊓ centralizer ({e ^ 2} : Set Γ)),
    ρ ⟨e, he⟩ ≠ 1 ∧ ρ ⟨r, hr⟩ ≠ 1 ∧ ρ ⟨e, he⟩ ≠ ρ ⟨r, hr⟩
  isPGroup_of_comm : ∀ (he : e ∈ P ⊓ centralizer ({e ^ 2} : Set Γ))
    (hr : r ∈ P ⊓ centralizer ({e ^ 2} : Set Γ)) (g : PGL(Fin 2, k)),
    g * ρ ⟨e, he⟩ = ρ ⟨e, he⟩ * g → g * ρ ⟨r, hr⟩ = ρ ⟨r, hr⟩ * g → ∃ n : ℕ, g ^ 2 ^ n = 1
  not_unip : ∀ u : ↥(P ⊓ centralizer ({e ^ 2} : Set Γ)), Nat.Coprime (orderOf (u : Γ)) 3 →
    orderOf (ρ u) = p →
    (u : Γ) * (e * u * e⁻¹) = e * u * e⁻¹ * u → (u : Γ) * (r * u * r⁻¹) = r * u * r⁻¹ * u →
      False
  mem_Kb_of_inv : ∀ x w : ↥(P ⊓ centralizer ({e ^ 2} : Set Γ)), Odd (orderOf x) →
    w * x * w⁻¹ = x⁻¹ → (x : Γ) ∈ Kb
  comm_of_comm_Kb : ∀ x ∈ Kb, x ≠ 1 → Nat.Coprime (orderOf x) (6 * p) → ∀ g ∈ P,
    g * x = x * g → g * e ^ 2 = e ^ 2 * g
  comm_of_comm_Zb : ∀ d ∈ Zb, d ≠ 1 → Odd (orderOf d) → ∀ g ∈ P, g * d = d * g →
    g * e ^ 2 = e ^ 2 * g
  not_inv_Zb : ∀ d ∈ Zb, d ≠ 1 → Odd (orderOf d) → ∀ g ∈ P, g * d * g⁻¹ ≠ d⁻¹
  comm_of_abelian : ∀ A B : Subgroup Γ, A ≤ B → B ≤ P → IsMulCommutative ↥B →
    3 ∣ Nat.card B → 5 ∣ Nat.card B → Nat.Coprime (Nat.card A) 6 →
    e ∈ normalizer (A : Set Γ) → r ∈ normalizer (A : Set Γ) → ∀ a ∈ A, a * e ^ 2 = e ^ 2 * a
  exists_conj_Kb : ∀ v : Γ, v * e ^ 2 = e ^ 2 * v →
    ∃ g ∈ P ⊓ centralizer ({e ^ 2} : Set Γ), ∀ x ∈ Kb, v * x * v⁻¹ = g * x * g⁻¹
  comm_of_coprime_six : ∀ y ∈ P, Nat.Coprime (orderOf y) 6 → ∀ R : Subgroup Γ, IsPGroup 2 R →
    y ∈ normalizer (R : Set Γ) → ∀ x ∈ R, y * x = x * y

section Helpers

variable {G : Type*} [Group G]

private theorem eq_of_orderOf_two_of_isCyclic [Finite G] {D : Subgroup G} (hD : IsCyclic ↥D)
    {a b : G} (ha : a ∈ D) (hb : b ∈ D) (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) :
    a = b := by
  have he : zpowers (⟨a, ha⟩ : ↥D) = zpowers ⟨b, hb⟩ := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk, ha2, hb2]
  have hmem : (⟨b, hb⟩ : ↥D) ∈ zpowers (⟨a, ha⟩ : ↥D) := he ▸ mem_zpowers _
  obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hmem
  have hn' : a ^ n = b := by simpa using congrArg Subtype.val hn
  rw [← zpow_mod_orderOf, ha2] at hn'
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · rw [Nat.cast_ofNat, h, zpow_zero] at hn'
    rw [← hn', orderOf_one] at hb2
    exact absurd hb2 (by norm_num)
  · rw [Nat.cast_ofNat, h, zpow_one] at hn'
    exact hn'

private theorem exists_mul_of_permutes {H K : Subgroup G}
    (hHK : (H : Set G) * (K : Set G) = (K : Set G) * (H : Set G)) :
    ∀ g ∈ H ⊔ K, ∃ h ∈ H, ∃ x ∈ K, h * x = g := by
  let W : Subgroup G :=
    { carrier := (H : Set G) * (K : Set G)
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, one_mul 1⟩
      mul_mem' := by
        rintro _ _ ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
        have h : k₁ * h₂ ∈ (K : Set G) * (H : Set G) := Set.mul_mem_mul hk₁ hh₂
        rw [← hHK] at h
        obtain ⟨h₃, hh₃, k₃, hk₃, he⟩ := h
        have he' : h₃ * k₃ = k₁ * h₂ := he
        refine ⟨h₁ * h₃, H.mul_mem hh₁ hh₃, k₃ * k₂, K.mul_mem hk₃ hk₂, ?_⟩
        calc h₁ * h₃ * (k₃ * k₂) = h₁ * (h₃ * k₃) * k₂ := by group
          _ = h₁ * (k₁ * h₂) * k₂ := by rw [he']
          _ = h₁ * k₁ * (h₂ * k₂) := by group
      inv_mem' := by
        rintro _ ⟨h, hh, x, hx, rfl⟩
        have h' : x⁻¹ * h⁻¹ ∈ (K : Set G) * (H : Set G) :=
          Set.mul_mem_mul (K.inv_mem hx) (H.inv_mem hh)
        rw [← hHK] at h'
        rwa [mul_inv_rev] }
  have hle : H ⊔ K ≤ W := sup_le (fun h hh => ⟨h, hh, 1, K.one_mem, mul_one h⟩)
    (fun x hx => ⟨1, H.one_mem, x, hx, one_mul x⟩)
  intro g hg
  exact hle hg

private theorem card_eq_mul_of_decomp [Finite G] {J H K : Subgroup G} (hHJ : H ≤ J) (hKJ : K ≤ J)
    (hcop : Nat.Coprime (Nat.card H) (Nat.card K))
    (hJ : ∀ g ∈ J, ∃ h ∈ H, ∃ x ∈ K, h * x = g) :
    Nat.card J = Nat.card H * Nat.card K := by
  apply le_antisymm
  · have hsurj : Function.Surjective (fun q : ↥H × ↥K =>
        (⟨(q.1 : G) * q.2, J.mul_mem (hHJ q.1.2) (hKJ q.2.2)⟩ : ↥J)) := by
      rintro ⟨g, hg⟩
      obtain ⟨h, hh, x, hx, rfl⟩ := hJ g hg
      exact ⟨(⟨h, hh⟩, ⟨x, hx⟩), rfl⟩
    calc Nat.card ↥J ≤ Nat.card (↥H × ↥K) := Nat.card_le_card_of_surjective _ hsurj
      _ = Nat.card H * Nat.card K := Nat.card_prod _ _
  · exact Nat.le_of_dvd Nat.card_pos (hcop.mul_dvd_of_dvd_of_dvd
      (Subgroup.card_dvd_of_le hHJ) (Subgroup.card_dvd_of_le hKJ))

private theorem inv_of_dihedral {J : Subgroup G} {n : ℕ} (φ : ↥J ≃* DihedralGroup n)
    {Bt : Subgroup G} (hBJ : Bt ≤ J) (hBodd : ∀ b ∈ Bt, Odd (orderOf b)) {t₁ t₂ : G}
    (ht₁ : t₁ ∈ J) (ht₂ : t₂ ∈ J)
    (hno : ∀ b ∈ Bt, t₁ * b = b * t₁ → t₂ * b = b * t₂ → b = 1) (hB : Bt ≠ ⊥) :
    (∀ b ∈ Bt, t₁ * b * t₁⁻¹ = b⁻¹) ∨ (∀ b ∈ Bt, t₂ * b * t₂⁻¹ = b⁻¹) := by
  have hrot : ∀ b (hb : b ∈ Bt), ∃ i, φ ⟨b, hBJ hb⟩ = DihedralGroup.r i := by
    intro b hb
    rcases h : φ ⟨b, hBJ hb⟩ with i | i
    · exact ⟨i, rfl⟩
    · exfalso
      have h1 : orderOf (φ ⟨b, hBJ hb⟩) = orderOf b := by
        rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      rw [h, DihedralGroup.orderOf_sr] at h1
      have := hBodd b hb
      rw [← h1] at this
      exact (Nat.not_odd_iff_even.2 even_two) this
  have hinv : ∀ t (ht : t ∈ J) (j : ZMod n), φ ⟨t, ht⟩ = DihedralGroup.sr j →
      ∀ b ∈ Bt, t * b * t⁻¹ = b⁻¹ := by
    intro t ht j hj b hb
    obtain ⟨i, hi⟩ := hrot b hb
    have h1 : φ (⟨t, ht⟩ * ⟨b, hBJ hb⟩ * (⟨t, ht⟩)⁻¹) = φ (⟨b, hBJ hb⟩)⁻¹ := by
      rw [map_mul, map_mul, map_inv, map_inv, hj, hi, DihedralGroup.inv_sr, DihedralGroup.inv_r,
        DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
      congr 1
      ring
    have h2 := congrArg Subtype.val (φ.injective h1)
    simpa using h2
  have hcomm : ∀ t (ht : t ∈ J) (j : ZMod n), φ ⟨t, ht⟩ = DihedralGroup.r j →
      ∀ b ∈ Bt, t * b = b * t := by
    intro t ht j hj b hb
    obtain ⟨i, hi⟩ := hrot b hb
    have h1 : φ (⟨t, ht⟩ * ⟨b, hBJ hb⟩) = φ (⟨b, hBJ hb⟩ * ⟨t, ht⟩) := by
      rw [map_mul, map_mul, hj, hi, DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]
    exact congrArg Subtype.val (φ.injective h1)
  rcases h₁ : φ ⟨t₁, ht₁⟩ with j₁ | j₁
  · rcases h₂ : φ ⟨t₂, ht₂⟩ with j₂ | j₂
    · exfalso
      apply hB
      rw [eq_bot_iff]
      intro b hb
      exact hno b hb (hcomm t₁ ht₁ j₁ h₁ b hb) (hcomm t₂ ht₂ j₂ h₂ b hb)
    · exact Or.inr (hinv t₂ ht₂ j₂ h₂)
  · exact Or.inl (hinv t₁ ht₁ j₁ h₁)

end Helpers

section Helpers24

variable {G : Type*} [Group G]

private theorem inv_of_card_24 [Finite G] {J Bt Wt : Subgroup G} (hBJ : Bt ≤ J) (hWJ : Wt ≤ J)
    (hJ : ∀ j ∈ J, ∃ b ∈ Bt, ∃ w ∈ Wt, b * w = j) (hB3 : Nat.card Bt = 3)
    (hW8 : Nat.card Wt = 8) (hJ24 : Nat.card J = 24)
    (hWcen : ∀ x : G, (∀ w ∈ Wt, x * w * x⁻¹ ∈ Wt) → orderOf x = 3 → ∀ w ∈ Wt, x * w = w * x)
    (hno : ∀ b ∈ Bt, (∀ w ∈ Wt, w * b = b * w) → b = 1) :
    ∃ w ∈ Wt, ∀ b ∈ Bt, w * b * w⁻¹ = b⁻¹ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxB, hx1⟩ : ∃ x ∈ Bt, x ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : Bt = ⊥ := (Subgroup.eq_bot_iff_forall Bt).2 h
    rw [hbot, Subgroup.card_bot] at hB3
    exact absurd hB3 (by norm_num)
  have hx3 : orderOf x = 3 := by
    have hdvd : orderOf x ∣ 3 := hB3 ▸ Subgroup.orderOf_dvd_natCard Bt hxB
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hx1
    · exact h
  have hBz : Bt = zpowers x := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hxB) ?_
    rw [hB3, Nat.card_zpowers, hx3]
  have hBcomm : ∀ a ∈ Bt, ∀ b ∈ Bt, a * b = b * a := by
    intro a ha b hb
    rw [hBz] at ha hb
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ha
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow_self x m n).eq
  by_contra hcon
  push Not at hcon
  have hcen : ∀ w ∈ Wt, w * x * w⁻¹ ∈ Bt → w * x * w⁻¹ = x := by
    intro w hw hwx
    rw [hBz] at hwx
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hwx
    rw [← zpow_mod_orderOf, hx3] at hn
    have hn3 : n % ((3 : ℕ) : ℤ) = 0 ∨ n % ((3 : ℕ) : ℤ) = 1 ∨ n % ((3 : ℕ) : ℤ) = 2 := by omega
    rcases hn3 with h | h | h
    · rw [h, zpow_zero] at hn
      exfalso
      apply hx1
      have h1 : w * x * w⁻¹ = w * 1 * w⁻¹ := by rw [← hn]; group
      exact mul_left_cancel (mul_right_cancel h1)
    · rw [h, zpow_one] at hn
      exact hn.symm
    · exfalso
      rw [h] at hn
      have hx3' : x ^ (3 : ℤ) = 1 := by
        rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, ← hx3, pow_orderOf_eq_one]
      have h2 : x ^ (2 : ℤ) = x⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← zpow_add_one, show (2 : ℤ) + 1 = 3 by norm_num, hx3']
      have hinv : w * x * w⁻¹ = x⁻¹ := by rw [← hn, h2]
      obtain ⟨b, hb, hb'⟩ := hcon w hw
      apply hb'
      rw [hBz] at hb
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hb
      rw [← conj_zpow, hinv, inv_zpow]
  set B' : Subgroup ↥J := Bt.subgroupOf J with hB'
  set W' : Subgroup ↥J := Wt.subgroupOf J with hW'
  have hB'c : Nat.card B' = 3 := by
    rw [hB', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBJ).toEquiv, hB3]
  have hW'c : Nat.card W' = 8 := by
    rw [hW', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWJ).toEquiv, hW8]
  have hB'i : B'.index = 8 := by
    have h := Subgroup.card_mul_index B'
    rw [hB'c, hJ24] at h
    omega
  have hW'i : W'.index = 3 := by
    have h := Subgroup.card_mul_index W'
    rw [hW'c, hJ24] at h
    omega
  have hB'p : IsPGroup 3 B' := IsPGroup.of_card (n := 1) (by rw [hB'c]; norm_num)
  have hW'p : IsPGroup 2 W' := IsPGroup.of_card (n := 3) (by rw [hW'c]; norm_num)
  let P : Sylow 3 ↥J := hB'p.toSylow (by rw [hB'i]; norm_num)
  have hPc : (P : Subgroup ↥J) = B' := hB'p.toSylow_coe _
  have hN : normalizer ((P : Subgroup ↥J) : Set ↥J) ≤ centralizer ((P : Subgroup ↥J) : Set ↥J) := by
    intro j hj
    rw [mem_centralizer_iff]
    intro y hy
    rw [hPc] at hy hj
    have hyB : (y : G) ∈ Bt := hy
    obtain ⟨b, hb, w, hw, hbw⟩ := hJ j j.2
    have hjx : (j : G) * x * (j : G)⁻¹ ∈ Bt := by
      have h1 := (mem_normalizer_iff.1 hj ⟨x, hBJ hxB⟩).1 hxB
      exact h1
    have hwx : w * x * w⁻¹ ∈ Bt := by
      have hw' : w = b⁻¹ * j := by rw [← hbw]; group
      rw [hw', show b⁻¹ * (j : G) * x * (b⁻¹ * j)⁻¹ = b⁻¹ * ((j : G) * x * (j : G)⁻¹) * b by
        group]
      exact Bt.mul_mem (Bt.mul_mem (Bt.inv_mem hb) hjx) hb
    have hwc := hcen w hw hwx
    have hwy : w * (y : G) = (y : G) * w := by
      have hyz : (y : G) ∈ zpowers x := hBz ▸ hyB
      obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hyz
      have hxw : w * x = x * w := by
        calc w * x = w * x * w⁻¹ * w := by group
          _ = x * w := by rw [hwc]
      rw [← hm]
      have hc : Commute w x := hxw
      exact (Commute.zpow_right hc m).eq
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hbw]
    calc (y : G) * (b * w) = b * ((y : G) * w) := by
          rw [← mul_assoc, hBcomm _ hyB _ hb, mul_assoc]
      _ = b * w * y := by rw [← hwy, mul_assoc]
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hN
  set N := (MonoidHom.transferSylow P hN).ker with hNdef
  have hNc : Nat.card N = 8 := by
    have h := hcomp.card_mul_card
    rw [hPc, hB'c, hJ24] at h
    omega
  have hNp : IsPGroup 2 N := IsPGroup.of_card (n := 3) (by rw [hNc]; norm_num)
  let Q : Sylow 2 ↥J := hW'p.toSylow (by rw [hW'i]; norm_num)
  have hQc : (Q : Subgroup ↥J) = W' := hW'p.toSylow_coe _
  have hNQ : N ≤ W' := hQc ▸ hNp.le_sylow_of_normal Q
  have hNW : N = W' := Subgroup.eq_of_le_of_card_ge hNQ (by rw [hNc, hW'c])
  have hW'n : W'.Normal := hNW ▸ MonoidHom.normal_ker _
  have hxW : ∀ w ∈ Wt, x * w * x⁻¹ ∈ Wt := by
    intro w hw
    have h := hW'n.conj_mem ⟨w, hWJ hw⟩ hw ⟨x, hBJ hxB⟩
    exact h
  exact hx1 (hno x hxB fun w hw => (hWcen x hxW hx3 w hw).symm)

end Helpers24

section HelpersPGL

private theorem comm_of_card_eight {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {k : Type} [Field k] [Finite k] [CharP k p] {Wt : Subgroup PGL(Fin 2, k)}
    (hW8 : Nat.card Wt = 8) {t₁ t₂ : PGL(Fin 2, k)} (ht₁ : t₁ ∈ Wt) (ht₂ : t₂ ∈ Wt)
    (h₁ : orderOf t₁ = 2) (h₂ : orderOf t₂ = 2) (hne : t₁ ≠ t₂) (x : PGL(Fin 2, k))
    (hx : ∀ w ∈ Wt, x * w * x⁻¹ ∈ Wt) (hx3 : orderOf x = 3) : ∀ w ∈ Wt, x * w = w * x := by
  have : Finite PGL(Fin 2, k) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hp8 : ¬ p ∣ Nat.card Wt := by
    rw [hW8, show (8 : ℕ) = 2 ^ 3 by norm_num]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 (hp.out.dvd_of_dvd_pow h))
  rcases CFSG.RankThree.PartTwo.KFacts.KP10.pgl_tame_cases Wt hp8 with
    hcyc | ⟨z, ⟨φ⟩⟩ | h | h | h
  · exact absurd (eq_of_orderOf_two_of_isCyclic hcyc ht₁ ht₂ h₁ h₂) hne
  · have hz : z = 4 := by
      have h := Nat.card_congr φ.toEquiv
      rw [hW8, DihedralGroup.nat_card] at h
      omega
    subst hz
    have hx3' : x * x * x = 1 := by
      rw [← pow_three', ← hx3, pow_orderOf_eq_one]
    let s : DihedralGroup 4 → DihedralGroup 4 := fun y =>
      φ ⟨x * (φ.symm y : PGL(Fin 2, k)) * x⁻¹, hx _ (φ.symm y).2⟩
    have hs : ∀ a b, s (a * b) = s a * s b := by
      intro a b
      show φ _ = φ _ * φ _
      rw [← map_mul]
      congr 1
      apply Subtype.ext
      simp only [map_mul, Subgroup.coe_mul]
      group
    have h3 : ∀ a, s (s (s a)) = a := by
      intro a
      apply φ.symm.injective
      simp only [s, MulEquiv.symm_apply_apply]
      apply Subtype.ext
      calc x * (x * (x * ((φ.symm a : ↥Wt) : PGL(Fin 2, k)) * x⁻¹) * x⁻¹) * x⁻¹ =
            (x * x * x) * ((φ.symm a : ↥Wt) : PGL(Fin 2, k)) * (x * x * x)⁻¹ := by group
        _ = ((φ.symm a : ↥Wt) : PGL(Fin 2, k)) := by rw [hx3']; group
    intro w hw
    have hfix := CFSG.RankThree.PartOne.InnerWeyl.dihedral_aut_trivial (Or.inl rfl) s hs h3
      (φ ⟨w, hw⟩)
    simp only [s, MulEquiv.symm_apply_apply] at hfix
    have h1 := congrArg Subtype.val (φ.injective hfix)
    simp only at h1
    calc x * w = x * w * x⁻¹ * x := by group
      _ = w * x := by rw [h1]
  · rw [hW8] at h
    norm_num at h
  · rw [hW8] at h
    norm_num at h
  · rw [hW8] at h
    norm_num at h

end HelpersPGL

namespace L3Frame

variable {Γ : Type} [Group Γ] {p : ℕ} {k : Type} [Field k] (F : L3Frame Γ p k)

theorem sq_mem (g : Γ) : g ^ 2 ∈ F.P := by
  by_cases hg : g ∈ F.P
  · exact F.P.pow_mem hg 2
  · rw [sq]
    exact F.mul_mem_of_not_mem g g hg hg

theorem z_sq : (F.e ^ 2) ^ 2 = 1 := by
  rw [← pow_mul]
  exact F.e_pow_four

theorem orderOf_z : orderOf (F.e ^ 2) = 2 :=
  orderOf_eq_prime F.z_sq F.e_sq_ne

theorem z_inv : (F.e ^ 2)⁻¹ = F.e ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact F.e_pow_four)

theorem r_z : F.r * F.e ^ 2 = F.e ^ 2 * F.r := by
  have h : F.r * F.e ^ 2 * F.r⁻¹ = F.e ^ 2 := by
    rw [← conj_pow, F.r_e, inv_pow, F.z_inv]
  calc F.r * F.e ^ 2 = F.r * F.e ^ 2 * F.r⁻¹ * F.r := by group
    _ = F.e ^ 2 * F.r := by rw [h]

theorem e_mem_C : F.e ∈ F.P ⊓ centralizer ({F.e ^ 2} : Set Γ) :=
  ⟨F.I_le_P F.e_mem, mem_centralizer_singleton_iff.2 (Commute.self_pow F.e 2).eq⟩

theorem r_mem_C : F.r ∈ F.P ⊓ centralizer ({F.e ^ 2} : Set Γ) :=
  ⟨F.I_le_P F.r_mem, mem_centralizer_singleton_iff.2 F.r_z⟩

theorem z_mem_C : F.e ^ 2 ∈ F.P ⊓ centralizer ({F.e ^ 2} : Set Γ) :=
  ⟨F.P.pow_mem (F.I_le_P F.e_mem) 2, mem_centralizer_singleton_iff.2 rfl⟩

theorem z_mem_Zb : F.e ^ 2 ∈ F.Zb :=
  (F.mem_Zb _).2 ⟨F.z_mem_C, fun _ hy => (mem_centralizer_singleton_iff.1 hy.2).symm⟩

theorem mem_P_of_odd {g : Γ} (hg : Odd (orderOf g)) : g ∈ F.P := by
  obtain ⟨m, hm⟩ := hg
  have h : g = (g ^ (m + 1)) ^ 2 := by
    rw [← pow_mul, show (m + 1) * 2 = orderOf g + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [h]
  exact F.sq_mem _

theorem Zb_comm {d y : Γ} (hd : d ∈ F.Zb) (hy : y ∈ F.P ⊓ centralizer ({F.e ^ 2} : Set Γ)) :
    d * y = y * d :=
  ((F.mem_Zb d).1 hd).2 y hy

theorem Zb_le_C : F.Zb ≤ F.P ⊓ centralizer ({F.e ^ 2} : Set Γ) := fun x hx =>
  ((F.mem_Zb x).1 hx).1

theorem not_two_dvd_relIndex [Finite Γ] : ¬ 2 ∣ F.I.relIndex F.P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥F.P) := inferInstance
  have hT : (T : Subgroup ↥F.P) ≤ F.I.subgroupOf F.P := by
    intro t ht
    obtain ⟨n, hn⟩ := T.isPGroup' ⟨t, ht⟩
    rw [mem_subgroupOf]
    refine F.mem_I_of_two t t.2 n ?_
    have h := congrArg (fun x : ↥(T : Subgroup ↥F.P) => ((x : ↥F.P) : Γ)) hn
    simpa using h
  intro h2
  exact T.not_dvd_index (h2.trans (Subgroup.index_dvd_of_le hT))

theorem comm_z_of_mem [Finite Γ] {S : Subgroup Γ} (hS2 : IsPGroup 2 S) (heS : F.e ∈ S)
    (hrS : F.r ∈ S) : ∀ s ∈ S, s * F.e ^ 2 = F.e ^ 2 * s := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := F.I_normal
  set S₀ : Subgroup Γ := S ⊓ F.I with hS₀
  have hS₀2 : IsPGroup 2 ↥S₀ := hS2.to_le inf_le_left
  have heS₀ : F.e ∈ S₀ := ⟨heS, F.e_mem⟩
  have hrS₀ : F.r ∈ S₀ := ⟨hrS, F.r_mem⟩
  have hzS₀ : F.e ^ 2 ∈ S₀ := S₀.pow_mem heS₀ 2
  set Cy : Subgroup Γ := F.I ⊓ centralizer ({F.e, F.r} : Set Γ) with hCy
  have hzCy : F.e ^ 2 ∈ Cy := by
    refine Subgroup.mem_inf.2 ⟨F.I.pow_mem F.e_mem 2, ?_⟩
    rw [mem_centralizer_iff]
    rintro y (rfl | rfl)
    · exact (Commute.self_pow F.e 2).eq
    · exact F.r_z
  have huniq : ∀ c ∈ Cy, orderOf c = 2 → c = F.e ^ 2 := fun c hc hc2 =>
    eq_of_orderOf_two_of_isCyclic F.isCyclic_cent hc hzCy hc2 F.orderOf_z
  have : Nontrivial ↥S₀ := ⟨⟨⟨F.e ^ 2, hzS₀⟩, 1, fun h => F.e_sq_ne (congrArg Subtype.val h)⟩⟩
  have hZnt : Nontrivial ↥(center ↥S₀) := hS₀2.center_nontrivial
  have h2Z : 2 ∣ Nat.card ↥(center ↥S₀) := by
    obtain ⟨n, hn⟩ := (hS₀2.to_subgroup (center ↥S₀)).exists_card_eq
    have h1 : 1 < Nat.card ↥(center ↥S₀) := Finite.one_lt_card
    rw [hn] at h1 ⊢
    rcases n with _ | n
    · simp at h1
    · exact dvd_pow_self 2 (Nat.succ_ne_zero n)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥S₀)) 2 h2Z
  have hcz : ((c : ↥S₀) : Γ) = F.e ^ 2 := by
    refine huniq _ (Subgroup.mem_inf.2 ⟨(c : ↥S₀).2.2, ?_⟩)
      (by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc])
    rw [mem_centralizer_iff]
    rintro y (rfl | rfl)
    · exact congrArg Subtype.val ((mem_center_iff.1 c.2) ⟨F.e, heS₀⟩)
    · exact congrArg Subtype.val ((mem_center_iff.1 c.2) ⟨F.r, hrS₀⟩)
  have hzc : ∀ y ∈ S₀, y * F.e ^ 2 = F.e ^ 2 * y := by
    intro y hy
    rw [← hcz]
    exact congrArg Subtype.val ((mem_center_iff.1 c.2) ⟨y, hy⟩)
  intro s hs
  have hconj : ∀ y ∈ S₀, s⁻¹ * y * s ∈ S₀ := by
    intro y hy
    refine ⟨S.mul_mem (S.mul_mem (S.inv_mem hs) hy.1) hs, ?_⟩
    have h := F.I_normal.conj_mem y hy.2 s⁻¹
    rwa [inv_inv] at h
  have hmem : s * F.e ^ 2 * s⁻¹ ∈ Cy := by
    refine Subgroup.mem_inf.2 ⟨F.I_normal.conj_mem _ (F.I.pow_mem F.e_mem 2) s, ?_⟩
    rw [mem_centralizer_iff]
    have key : ∀ y ∈ S₀, y * (s * F.e ^ 2 * s⁻¹) = s * F.e ^ 2 * s⁻¹ * y := by
      intro y hy
      have h := hzc _ (hconj y hy)
      calc y * (s * F.e ^ 2 * s⁻¹) = s * ((s⁻¹ * y * s) * F.e ^ 2) * s⁻¹ := by group
        _ = s * (F.e ^ 2 * (s⁻¹ * y * s)) * s⁻¹ := by rw [h]
        _ = s * F.e ^ 2 * s⁻¹ * y := by group
    rintro y (rfl | rfl)
    · exact key _ heS₀
    · exact key _ hrS₀
  have h2 : orderOf (s * F.e ^ 2 * s⁻¹) = 2 := by
    have hsc : SemiconjBy s (F.e ^ 2) (s * F.e ^ 2 * s⁻¹) := by
      unfold SemiconjBy
      group
    rw [← hsc.orderOf_eq, F.orderOf_z]
  have h3 := huniq _ hmem h2
  calc s * F.e ^ 2 = s * F.e ^ 2 * s⁻¹ * s := by group
    _ = F.e ^ 2 * s := by rw [h3]

theorem isSylowOf_inf_P [Finite Γ] {A S : Subgroup Γ} (hIA : F.I ≤ A)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S A) (hSz : ∀ s ∈ S, s * F.e ^ 2 = F.e ^ 2 * s) :
    CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ F.P) (F.P ⊓ centralizer ({F.e ^ 2} : Set Γ)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := F.P_normal
  have hSA : S ≤ A := (CFSG.ABGLocalTools.isSylowOf_iff.1 hS).1
  have hAN : A ≤ normalizer ((A ⊓ F.P : Subgroup Γ) : Set Γ) := by
    intro a ha
    rw [mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨hgA, hgP⟩
      exact ⟨A.mul_mem (A.mul_mem ha hgA) (A.inv_mem ha), F.P_normal.conj_mem g hgP a⟩
    · rintro ⟨hgA, hgP⟩
      have hg : g = a⁻¹ * (a * g * a⁻¹) * a := by group
      refine ⟨hg ▸ A.mul_mem (A.mul_mem (A.inv_mem ha) hgA) ha, ?_⟩
      have h := F.P_normal.conj_mem _ hgP a⁻¹
      rwa [inv_inv, ← hg] at h
  have h1 := hS.inf_of_le_normalizer inf_le_left hAN
  have hSAP : S ⊓ (A ⊓ F.P) = S ⊓ F.P := by
    rw [← inf_assoc, inf_eq_left.2 hSA]
  rw [hSAP] at h1
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at h1 ⊢
  obtain ⟨-, hp, hd⟩ := h1
  refine ⟨fun x hx => ⟨hx.2, mem_centralizer_singleton_iff.2 (hSz x hx.1)⟩, hp, ?_⟩
  intro h2
  have hle1 : S ⊓ F.P ≤ F.P ⊓ centralizer ({F.e ^ 2} : Set Γ) :=
    fun x hx => ⟨hx.2, mem_centralizer_singleton_iff.2 (hSz x hx.1)⟩
  have e1 := Subgroup.relIndex_mul_relIndex (S ⊓ F.P) (F.P ⊓ centralizer ({F.e ^ 2} : Set Γ))
    F.P hle1 inf_le_left
  have e2 := Subgroup.relIndex_mul_relIndex (S ⊓ F.P) (A ⊓ F.P) F.P
    (inf_le_inf_right _ hSA) inf_le_right
  have e3 := Subgroup.relIndex_mul_relIndex F.I (A ⊓ F.P) F.P (le_inf hIA F.I_le_P) inf_le_right
  have h2P : 2 ∣ (S ⊓ F.P).relIndex F.P := e1 ▸ h2.mul_right _
  rw [← e2] at h2P
  rcases (Nat.prime_two.dvd_mul).1 h2P with h | h
  · exact hd h
  · exact F.not_two_dvd_relIndex (e3 ▸ h.mul_left _)

theorem exists_inv_rho [Finite Γ] [hp : Fact p.Prime] (hp2 : p ≠ 2) [Finite k] [CharP k p]
    {B W : Subgroup Γ}
    (hBC : B ≤ F.P ⊓ centralizer ({F.e ^ 2} : Set Γ))
    (hW : CFSG.ABGLocalTools.IsSylowOf 2 W (F.P ⊓ centralizer ({F.e ^ 2} : Set Γ)))
    (heW : F.e ∈ W) (hrW : F.r ∈ W) (hBodd : Odd (Nat.card B))
    (hBp : ∀ b : ↥(F.P ⊓ centralizer ({F.e ^ 2} : Set Γ)), (b : Γ) ∈ B → orderOf (F.ρ b) ≠ p)
    (hdec : ∀ g ∈ B ⊔ W, ∃ b ∈ B, ∃ w ∈ W, b * w = g) :
    ∃ u : ↥(F.P ⊓ centralizer ({F.e ^ 2} : Set Γ)), (u : Γ) ∈ W ∧
      ∀ b : ↥(F.P ⊓ centralizer ({F.e ^ 2} : Set Γ)), (b : Γ) ∈ B →
        F.ρ (u * b * u⁻¹) = (F.ρ b)⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite PGL(Fin 2, k) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  set C : Subgroup Γ := F.P ⊓ centralizer ({F.e ^ 2} : Set Γ) with hC
  obtain ⟨hWC, hW2, -⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hW
  set ec : ↥C := ⟨F.e, F.e_mem_C⟩ with hec
  set rc : ↥C := ⟨F.r, F.r_mem_C⟩ with hrc
  obtain ⟨hρe1, hρr1, hρer⟩ := F.ρ_ne F.e_mem_C F.r_mem_C
  have hzZ : ((ec ^ 2 : ↥C) : Γ) ∈ F.Zb := by
    rw [Subgroup.coe_pow]
    exact F.z_mem_Zb
  have hρe2 : orderOf (F.ρ ec) = 2 := by
    refine orderOf_eq_prime ?_ hρe1
    rw [← map_pow]
    exact (F.ρ_eq_one _).2 hzZ
  have hρr2 : orderOf (F.ρ rc) = 2 := by
    refine orderOf_eq_prime ?_ hρr1
    rw [← map_pow]
    refine (F.ρ_eq_one _).2 ?_
    have : ((rc ^ 2 : ↥C) : Γ) = 1 := by rw [Subgroup.coe_pow]; exact F.r_sq
    rw [this]
    exact F.Zb.one_mem
  have hno : ∀ y : PGL(Fin 2, k), Odd (orderOf y) → y * F.ρ ec = F.ρ ec * y →
      y * F.ρ rc = F.ρ rc * y → y = 1 := by
    intro y hy h1 h2
    obtain ⟨n, hn⟩ := F.isPGroup_of_comm F.e_mem_C F.r_mem_C y h1 h2
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hy)) (orderOf_dvd_of_pow_eq_one hn) dvd_rfl)
  set Bt : Subgroup PGL(Fin 2, k) := (B.subgroupOf C).map F.ρ with hBt
  set Wt : Subgroup PGL(Fin 2, k) := (W.subgroupOf C).map F.ρ with hWt
  set Jt : Subgroup PGL(Fin 2, k) := ((B ⊔ W).subgroupOf C).map F.ρ with hJt
  have hBtodd : ∀ y ∈ Bt, Odd (orderOf y) := by
    rintro _ ⟨b, hb, rfl⟩
    refine Odd.of_dvd_nat ?_ (orderOf_map_dvd F.ρ b)
    rw [← Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat hBodd (Subgroup.orderOf_dvd_natCard B hb)
  have hecW : F.ρ ec ∈ Wt := ⟨ec, heW, rfl⟩
  have hrcW : F.ρ rc ∈ Wt := ⟨rc, hrW, rfl⟩
  by_cases hBt1 : Bt = ⊥
  · refine ⟨1, W.one_mem, fun b hb => ?_⟩
    have h1 : F.ρ b = 1 := by
      have : F.ρ b ∈ Bt := ⟨b, hb, rfl⟩
      rwa [hBt1, mem_bot] at this
    rw [one_mul, inv_one, mul_one, h1, inv_one]
  have hBtJ : Bt ≤ Jt := Subgroup.map_mono (fun x hx => mem_sup_left hx)
  have hWtJ : Wt ≤ Jt := Subgroup.map_mono (fun x hx => mem_sup_right hx)
  have hdecJ : ∀ j ∈ Jt, ∃ x ∈ Bt, ∃ y ∈ Wt, x * y = j := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨b, hb, w, hw, hbw⟩ := hdec _ hg
    refine ⟨F.ρ ⟨b, hBC hb⟩, ⟨_, hb, rfl⟩, F.ρ ⟨w, hWC hw⟩, ⟨_, hw, rfl⟩, ?_⟩
    rw [← map_mul]
    congr 1
    exact Subtype.ext hbw
  have hBtc : Odd (Nat.card Bt) := by
    refine Odd.of_dvd_nat hBodd ?_
    refine (Subgroup.card_map_dvd _ _).trans ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv]
  have hWt2 : IsPGroup 2 Wt := (hW2.comap_subtype (K := C)).map F.ρ
  obtain ⟨j, hj⟩ := hWt2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card Bt) (Nat.card Wt) := by
    rw [hj]
    exact Nat.Coprime.pow_right j (Nat.coprime_two_right.2 hBtc)
  have hJc : Nat.card Jt = Nat.card Bt * Nat.card Wt :=
    card_eq_mul_of_decomp hBtJ hWtJ hcop hdecJ
  have hpB : ¬ p ∣ Nat.card Bt := by
    intro h
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Bt) p h
    obtain ⟨b, hb, hby⟩ := y.2
    apply hBp b hb
    rw [hby, ← hy, Subgroup.orderOf_coe]
  have hpJ : ¬ p ∣ Nat.card Jt := by
    rw [hJc, hj]
    intro h
    rcases (hp.out.dvd_mul).1 h with h | h
    · exact hpB h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 (hp.out.dvd_of_dvd_pow h))
  have hW8 : 8 ∣ Nat.card Wt := by
    have hT : CFSG.ABGLocalTools.IsSylowOf 2 (W.subgroupOf C) ⊤ := by
      rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff C, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr hWC, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact hW
    have h := PartTwo.s16c7_isSylowOf_map hT F.ρ
    rw [← MonoidHom.range_eq_map] at h
    rw [h.card_eq]
    have hne : Nat.card F.ρ.range ≠ 0 := Nat.card_pos.ne'
    have h3 : 3 ≤ (Nat.card F.ρ.range).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization hne).1 (by simpa using F.eight_dvd)
    exact dvd_trans (by norm_num : 8 ∣ 2 ^ 3) (Nat.pow_dvd_pow 2 h3)
  have hno' : ∀ y ∈ Bt, F.ρ ec * y = y * F.ρ ec → F.ρ rc * y = y * F.ρ rc → y = 1 :=
    fun y hy h1 h2 => hno y (hBtodd y hy) h1.symm h2.symm
  have hfin : ∀ t ∈ Wt, (∀ y ∈ Bt, t * y * t⁻¹ = y⁻¹) →
      ∃ u : ↥C, (u : Γ) ∈ W ∧ ∀ b : ↥C, (b : Γ) ∈ B → F.ρ (u * b * u⁻¹) = (F.ρ b)⁻¹ := by
    rintro _ ⟨u, hu, rfl⟩ ht
    refine ⟨u, hu, fun b hb => ?_⟩
    rw [map_mul, map_mul, map_inv]
    exact ht _ ⟨b, hb, rfl⟩
  rcases CFSG.RankThree.PartTwo.KFacts.KP10.pgl_tame_cases Jt hpJ with
    hcyc | ⟨n, ⟨φ⟩⟩ | h12 | h24 | h60
  · exfalso
    apply hBt1
    rw [eq_bot_iff]
    intro y hy
    rw [mem_bot]
    have hcomm : ∀ a ∈ Jt, ∀ b ∈ Jt, a * b = b * a := by
      intro a ha b hb
      have := (IsCyclic.commGroup (α := ↥Jt)).mul_comm ⟨a, ha⟩ ⟨b, hb⟩
      exact congrArg Subtype.val this
    exact hno' y hy (hcomm _ (hWtJ hecW) _ (hBtJ hy)) (hcomm _ (hWtJ hrcW) _ (hBtJ hy))
  · rcases inv_of_dihedral φ hBtJ hBtodd (hWtJ hecW) (hWtJ hrcW) hno' hBt1 with h | h
    · exact hfin _ hecW h
    · exact hfin _ hrcW h
  · exfalso
    have : 8 ∣ 12 := h12 ▸ hJc ▸ (hW8.mul_left _)
    norm_num at this
  ·
    have hWdvd : Nat.card Wt ∣ 24 := h24 ▸ hJc ▸ Dvd.intro_left _ rfl
    have hW8' : Nat.card Wt = 8 := by
      rw [hj] at hWdvd hW8 ⊢
      have hj3 : j ≤ 3 := by
        by_contra hj3
        have : 2 ^ 4 ∣ 24 := (Nat.pow_dvd_pow 2 (by omega)).trans hWdvd
        norm_num at this
      have hj3' : 3 ≤ j := by
        by_contra hj3'
        have : 8 ∣ 2 ^ 2 := hW8.trans (Nat.pow_dvd_pow 2 (by omega))
        norm_num at this
      rw [show j = 3 by omega]
      norm_num
    have hB3 : Nat.card Bt = 3 := by
      have h := hJc
      rw [h24, hW8'] at h
      omega
    have hWcen := comm_of_card_eight hp2 hW8' hecW hrcW hρe2 hρr2 hρer
    obtain ⟨t, ht, hinv⟩ := inv_of_card_24 hBtJ hWtJ hdecJ hB3 hW8' h24 hWcen
      (fun y hy h => hno y (hBtodd y hy) (h _ hecW).symm (h _ hrcW).symm)
    exact hfin t ht hinv
  · exfalso
    have : 8 ∣ 60 := h60 ▸ hJc ▸ (hW8.mul_left _)
    norm_num at this

theorem exists_A₀ [Finite Γ] {B : Subgroup Γ} (hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hBodd : Odd (Nat.card B)) (h5 : 5 ∣ Nat.card B) :
    ∃ A₀ : Subgroup Γ, A₀ ≤ B ∧ (∀ b ∈ B, Nat.Coprime (orderOf b) 3 → b ∈ A₀) ∧
      (∀ a ∈ A₀, Nat.Coprime (orderOf a) 3) ∧ Nat.Coprime (Nat.card A₀) 6 ∧
        5 ∣ Nat.card A₀ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set A₀ : Subgroup Γ := closure {b | b ∈ B ∧ Nat.Coprime (orderOf b) 3} with hA₀
  have key : ∀ a ∈ A₀, a ∈ B ∧ Nat.Coprime (orderOf a) 3 := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨B.one_mem, by simp⟩
    | mul x y _ _ hx hy =>
      refine ⟨B.mul_mem hx.1 hy.1, ?_⟩
      exact Nat.Coprime.coprime_dvd_left
        (Commute.orderOf_mul_dvd_mul_orderOf (hBcomm x hx.1 y hy.1))
        (Nat.coprime_mul_iff_left.2 ⟨hx.2, hy.2⟩)
    | inv x _ hx => exact ⟨B.inv_mem hx.1, by rw [orderOf_inv]; exact hx.2⟩
  have hA₀B : A₀ ≤ B := fun a ha => (key a ha).1
  have hodd : Odd (Nat.card A₀) := Odd.of_dvd_nat hBodd (Subgroup.card_dvd_of_le hA₀B)
  have h3 : ¬ 3 ∣ Nat.card A₀ := by
    intro h
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥A₀) 3 h
    have h1 := (key a a.2).2
    rw [Subgroup.orderOf_coe, ha] at h1
    norm_num at h1
  refine ⟨A₀, hA₀B, fun b hb h => subset_closure ⟨hb, h⟩, fun a ha => (key a ha).2, ?_, ?_⟩
  · rw [show (6 : ℕ) = 2 * 3 by norm_num]
    exact Nat.Coprime.mul_right (Nat.coprime_two_right.2 hodd)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm
  · obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 5 h5
    have hbA : (b : Γ) ∈ A₀ :=
      subset_closure ⟨b.2, by rw [Subgroup.orderOf_coe, hb]; norm_num⟩
    have h1 := Subgroup.orderOf_dvd_natCard A₀ hbA
    rwa [Subgroup.orderOf_coe, hb] at h1

theorem conj_mem_A₀ [Finite Γ] {S B A₀ : Subgroup Γ} (hS2 : IsPGroup 2 S)
    (hBab : IsMulCommutative ↥B) (hBodd : Odd (Nat.card B)) (hBP : B ≤ F.P)
    (hperm : (B : Set Γ) * (S : Set Γ) = (S : Set Γ) * (B : Set Γ))
    (hA₀B : A₀ ≤ B) (hA₀mem : ∀ b ∈ B, Nat.Coprime (orderOf b) 3 → b ∈ A₀)
    (hA₀ord : ∀ a ∈ A₀, Nat.Coprime (orderOf a) 3) :
    ∀ s ∈ S, ∀ a ∈ A₀, s * a * s⁻¹ ∈ A₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsolv : Group.IsSolvable ↥(B ⊔ S) := by
    have hBle : B ≤ B ⊔ S := le_sup_left
    have hle : S ≤ B ⊔ S := le_sup_right
    have eA : ↥(B.subgroupOf (B ⊔ S)) ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBle
    have eC : ↥(S.subgroupOf (B ⊔ S)) ≃* ↥S := Subgroup.subgroupOfEquivOfLe hle
    have : Group.IsNilpotent ↥B := inferInstance
    refine CFSG.GroupTheory.WielandtProduct.wielandt_coprime_product (B.subgroupOf (B ⊔ S))
      (S.subgroupOf (B ⊔ S)) (Group.nilpotent_of_mulEquiv eA.symm)
      ((hS2.of_equiv eC.symm).isNilpotent) ?_ ?_
    · rw [Nat.card_congr eA.toEquiv, Nat.card_congr eC.toEquiv]
      obtain ⟨n, hn⟩ := hS2.exists_card_eq
      rw [hn]
      exact (Nat.coprime_two_left.2 hBodd).symm.pow_right n
    · intro g
      obtain ⟨b, hb, s, hs, hbs⟩ := exists_mul_of_permutes hperm (g : Γ) g.2
      exact ⟨⟨b, hBle hb⟩, hb, ⟨s, hle hs⟩, hs, Subtype.ext hbs.symm⟩
  intro s hs a ha
  have hab : a ∈ B := hA₀B ha
  have hodd : Odd (orderOf a) := Odd.of_dvd_nat hBodd (Subgroup.orderOf_dvd_natCard B hab)
  have h6 : Nat.Coprime (orderOf a) 6 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num]
    exact Nat.Coprime.mul_right (Nat.coprime_two_right.2 hodd) (hA₀ord a ha)
  have hconj := CFSG.conj_mem_of_permutes_of_centralizes hBab hBodd hS2 hperm hsolv hab
    (fun R hR _ haR => F.comm_of_coprime_six a (hBP hab) h6 R hR haR) (mem_sup_right hs)
  refine hA₀mem _ hconj ?_
  have hsc : SemiconjBy s a (s * a * s⁻¹) := by
    unfold SemiconjBy
    group
  rw [← hsc.orderOf_eq]
  exact hA₀ord a ha

theorem le_C [Finite Γ] [hp : Fact p.Prime] (hp5 : 5 ≤ p) [Finite k] [CharP k p]
    {W B A₀ : Subgroup Γ}
    (hW : CFSG.ABGLocalTools.IsSylowOf 2 W (F.P ⊓ centralizer ({F.e ^ 2} : Set Γ)))
    (heW : F.e ∈ W) (hrW : F.r ∈ W)
    (hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBodd : Odd (Nat.card B)) (hBP : B ≤ F.P)
    (hA₀B : A₀ ≤ B) (hA₀ne : A₀ ≠ ⊥) (hA₀6 : Nat.Coprime (Nat.card A₀) 6)
    (hWN : ∀ w ∈ W, ∀ a ∈ A₀, w * a * w⁻¹ ∈ A₀)
    (hA₀C : A₀ ≤ F.P ⊓ centralizer ({F.e ^ 2} : Set Γ)) :
    B ≤ F.P ⊓ centralizer ({F.e ^ 2} : Set Γ) := by
  classical
  have hp2 : p ≠ 2 := by omega
  set C : Subgroup Γ := F.P ⊓ centralizer ({F.e ^ 2} : Set Γ) with hC
  obtain ⟨hWC, hW2, -⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hW
  have hBord : ∀ b ∈ B, Odd (orderOf b) := fun b hb =>
    Odd.of_dvd_nat hBodd (Subgroup.orderOf_dvd_natCard B hb)
  have hZ : ∀ d ∈ A₀, d ∈ F.Zb → d ≠ 1 → B ≤ C := fun d hd hdZ hd1 b hb =>
    ⟨hBP hb, mem_centralizer_singleton_iff.2 (F.comm_of_comm_Zb d hdZ hd1 (hBord d (hA₀B hd))
      b (hBP hb) (hBcomm b hb d (hA₀B hd)))⟩
  have hK : ∀ x ∈ A₀, x ∈ F.Kb → x ≠ 1 → Nat.Coprime (orderOf x) (6 * p) → B ≤ C :=
    fun x hx hxK hx1 hxc b hb =>
      ⟨hBP hb, mem_centralizer_singleton_iff.2 (F.comm_of_comm_Kb x hxK hx1 hxc b (hBP hb)
        (hBcomm b hb x (hA₀B hx)))⟩
  have hAp : ∀ a : ↥C, (a : Γ) ∈ A₀ → orderOf (F.ρ a) ≠ p := fun a ha hap =>
    F.not_unip a (Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard A₀ ha)
      (Nat.Coprime.coprime_dvd_right (by norm_num : 3 ∣ 6) hA₀6)) hap
      (hBcomm _ (hA₀B ha) _ (hA₀B (hWN _ heW _ ha)))
      (hBcomm _ (hA₀B ha) _ (hA₀B (hWN _ hrW _ ha)))
  have hWN' : (W : Set Γ) ⊆ normalizer (A₀ : Set Γ) := by
    intro w hw
    rw [SetLike.mem_coe, mem_normalizer_iff]
    intro a
    refine ⟨fun ha => hWN w hw a ha, fun ha => ?_⟩
    have h := hWN w⁻¹ (W.inv_mem hw) _ ha
    rwa [show w⁻¹ * (w * a * w⁻¹) * w⁻¹⁻¹ = a by group] at h
  have hperm : (A₀ : Set Γ) * (W : Set Γ) = (W : Set Γ) * (A₀ : Set Γ) :=
    (Subgroup.set_mul_normalizer_comm (W : Set Γ) A₀ hWN').symm
  have hA₀odd : Odd (Nat.card A₀) :=
    Nat.coprime_two_right.1 (Nat.Coprime.coprime_dvd_right (by norm_num) hA₀6)
  obtain ⟨u, huW, hu⟩ := F.exists_inv_rho hp2 hA₀C hW heW hrW hA₀odd hAp
    (exists_mul_of_permutes hperm)
  have huA : ∀ a ∈ A₀, (u : Γ) * a * (u : Γ)⁻¹ ∈ A₀ := fun a ha => hWN _ huW a ha
  by_cases hex : ∃ a ∈ A₀, a * ((u : Γ) * a * (u : Γ)⁻¹) ≠ 1
  · obtain ⟨a, ha, ha1⟩ := hex
    have hd : a * ((u : Γ) * a * (u : Γ)⁻¹) ∈ A₀ := A₀.mul_mem ha (huA a ha)
    refine hZ _ hd ?_ ha1
    have h1 : F.ρ (⟨a, hA₀C ha⟩ * (u * ⟨a, hA₀C ha⟩ * u⁻¹)) = 1 := by
      rw [map_mul, hu ⟨a, hA₀C ha⟩ ha, mul_inv_cancel]
    exact (F.ρ_eq_one _).1 h1
  push Not at hex
  have hinvA : ∀ a ∈ A₀, (u : Γ) * a * (u : Γ)⁻¹ = a⁻¹ := fun a ha =>
    eq_inv_of_mul_eq_one_right (hex a ha)
  by_cases hρ : ∃ a : Γ, ∃ ha : a ∈ A₀, F.ρ ⟨a, hA₀C ha⟩ ≠ 1
  · obtain ⟨a, ha, haρ⟩ := hρ
    have ha1 : a ≠ 1 := by
      rintro rfl
      exact haρ (map_one F.ρ)
    have haK : a ∈ F.Kb := F.mem_Kb_of_inv ⟨a, hA₀C ha⟩ u (by
      rw [Subgroup.orderOf_mk]
      exact hBord a (hA₀B ha)) (Subtype.ext (hinvA a ha))
    refine hK a ha haK ha1 (Nat.Coprime.mul_right ?_ ?_)
    · exact Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard A₀ ha) hA₀6
    · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
      intro hpa
      have ha0 : orderOf a ≠ 0 := (orderOf_pos_iff.2 (isOfFinOrder_of_finite a)).ne'
      set y := a ^ (orderOf a / p) with hy
      have hyo : orderOf y = p := orderOf_pow_orderOf_div ha0 hpa
      have hyA : y ∈ A₀ := A₀.pow_mem ha _
      have hρy : F.ρ ⟨y, hA₀C hyA⟩ ≠ 1 := by
        intro h1
        have hyZ := (F.ρ_eq_one _).1 h1
        have hc : y * (u : Γ) = (u : Γ) * y := F.Zb_comm hyZ u.2
        have h2 : y = y⁻¹ := by
          rw [← hinvA y hyA, ← hc]
          group
        have h3 : y ^ 2 = 1 := by
          rw [sq]
          nth_rewrite 2 [h2]
          exact mul_inv_cancel y
        have h4 := orderOf_dvd_of_pow_eq_one h3
        rw [hyo] at h4
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h4)
      apply hAp ⟨y, hA₀C hyA⟩ hyA
      refine orderOf_eq_prime ?_ hρy
      rw [← map_pow]
      have : (⟨y, hA₀C hyA⟩ : ↥C) ^ p = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, ← hyo, pow_orderOf_eq_one]
        rfl
      rw [this, map_one]
  · push Not at hρ
    obtain ⟨d, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA₀ne
    exact hZ d d.2 ((F.ρ_eq_one _).1 (hρ d d.2)) (fun h => hd1 (Subtype.ext h))

theorem decomp [Finite Γ] {W B : Subgroup Γ}
    (hBC : B ≤ F.P ⊓ centralizer ({F.e ^ 2} : Set Γ))
    (hWC : W ≤ F.P ⊓ centralizer ({F.e ^ 2} : Set Γ)) (hW2 : IsPGroup 2 W)
    (hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBodd : Odd (Nat.card B))
    (hdec : ∀ g ∈ B ⊔ W, ∃ b ∈ B, ∃ w ∈ W, b * w = g)
    (u : ↥(F.P ⊓ centralizer ({F.e ^ 2} : Set Γ))) (huW : (u : Γ) ∈ W)
    (hu : ∀ b : ↥(F.P ⊓ centralizer ({F.e ^ 2} : Set Γ)), (b : Γ) ∈ B →
      F.ρ (u * b * u⁻¹) = (F.ρ b)⁻¹) :
    (∀ b ∈ B, (u : Γ) * b * (u : Γ)⁻¹ ∈ B) ∧
      (∀ b ∈ B, ∃ x ∈ B, x ∈ F.Zb ∧ ∃ y ∈ B, y ∈ F.Kb ∧ b = x * y) ∧
        (∀ y ∈ B, y ∈ F.Kb → (u : Γ) * y * (u : Γ)⁻¹ = y⁻¹) := by
  classical
  have hCm : ∀ {a b : Γ}, a ∈ F.P ⊓ centralizer ({F.e ^ 2} : Set Γ) →
      b ∈ F.P ⊓ centralizer ({F.e ^ 2} : Set Γ) →
        a * b ∈ F.P ⊓ centralizer ({F.e ^ 2} : Set Γ) := fun ha hb => Subgroup.mul_mem _ ha hb
  have hBord : ∀ b ∈ B, Odd (orderOf b) := fun b hb =>
    Odd.of_dvd_nat hBodd (Subgroup.orderOf_dvd_natCard B hb)
  have hcop : ∀ {a k : ℕ}, Odd a → Nat.Coprime (2 ^ k) a := fun ha =>
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 ha)
  have hnorm : ∀ b ∈ B, (u : Γ) * b * (u : Γ)⁻¹ ∈ B := by
    intro b hb
    have hg : (u : Γ) * b * (u : Γ)⁻¹ ∈ B ⊔ W :=
      (B ⊔ W).mul_mem ((B ⊔ W).mul_mem (mem_sup_right huW) (mem_sup_left hb))
        ((B ⊔ W).inv_mem (mem_sup_right huW))
    obtain ⟨b', hb', w', hw', hbw⟩ := hdec _ hg
    have hζ : w' * (b * b') ∈ F.Zb := by
      refine (F.ρ_eq_one ⟨_, hCm (hWC hw') (hCm (hBC hb) (hBC hb'))⟩).1 ?_
      have h2 := hu ⟨b, hBC hb⟩ hb
      have hg' : u * ⟨b, hBC hb⟩ * u⁻¹ = ⟨b', hBC hb'⟩ * ⟨w', hWC hw'⟩ := Subtype.ext hbw.symm
      rw [hg', map_mul] at h2
      have h3 : F.ρ ⟨w', hWC hw'⟩ = (F.ρ ⟨b', hBC hb'⟩)⁻¹ * (F.ρ ⟨b, hBC hb⟩)⁻¹ := by
        rw [← h2]
        group
      have h4 : (⟨w' * (b * b'), hCm (hWC hw') (hCm (hBC hb) (hBC hb'))⟩ :
          ↥(F.P ⊓ centralizer ({F.e ^ 2} : Set Γ))) =
          ⟨w', hWC hw'⟩ * (⟨b, hBC hb⟩ * ⟨b', hBC hb'⟩) := rfl
      rw [h4, map_mul, map_mul, h3]
      group
    have hw'eq : w' = (w' * (b * b')) * (b * b')⁻¹ := by group
    have hcomm : w' * b' = b' * w' := by
      rw [hw'eq]
      have h1 := F.Zb_comm hζ (hBC hb')
      have h2 : (b * b')⁻¹ * b' = b' * (b * b')⁻¹ :=
        hBcomm _ (B.inv_mem (B.mul_mem hb hb')) _ hb'
      calc w' * (b * b') * (b * b')⁻¹ * b' = w' * (b * b') * ((b * b')⁻¹ * b') := by group
        _ = w' * (b * b') * (b' * (b * b')⁻¹) := by rw [h2]
        _ = (w' * (b * b') * b') * (b * b')⁻¹ := by group
        _ = (b' * (w' * (b * b'))) * (b * b')⁻¹ := by rw [h1]
        _ = b' * (w' * (b * b') * (b * b')⁻¹) := by group
    set m := orderOf b with hm
    have hmo : Odd m := hBord b hb
    have hgm : ((u : Γ) * b * (u : Γ)⁻¹) ^ m = 1 := by
      rw [conj_pow, hm, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
    rw [← hbw, (Commute.mul_pow hcomm.symm m)] at hgm
    have hw'm : w' ^ m = (b' ^ m)⁻¹ := eq_inv_of_mul_eq_one_right hgm
    obtain ⟨n, hn⟩ := hW2 ⟨w', hw'⟩
    have hw'n : w' ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hw'm1 : w' ^ m = 1 := by
      have hBo : Odd (orderOf (w' ^ m)) := by
        rw [hw'm, orderOf_inv]
        exact hBord _ (B.pow_mem hb' m)
      have hpk : (w' ^ m) ^ 2 ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hw'n, one_pow]
      exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (hcop hBo)
        (orderOf_dvd_of_pow_eq_one hpk) dvd_rfl)
    have hw'1 : w' = 1 := orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (hcop hmo)
      (orderOf_dvd_of_pow_eq_one hw'n) (orderOf_dvd_of_pow_eq_one hw'm1))
    rw [← hbw, hw'1, mul_one]
    exact hb'
  have huz : (u : Γ) * F.e ^ 2 = F.e ^ 2 * (u : Γ) := mem_centralizer_singleton_iff.1 u.2.2
  have hinvK : ∀ y ∈ B, y ∈ F.Kb → (u : Γ) * y * (u : Γ)⁻¹ = y⁻¹ := by
    intro y hy hyK
    have hy' := hnorm y hy
    have hyK' := F.conj_mem_Kb (u : Γ) huz y hyK
    have ht : y * ((u : Γ) * y * (u : Γ)⁻¹) ∈ F.Zb := by
      refine (F.ρ_eq_one ⟨_, hCm (hBC hy) (hBC hy')⟩).1 ?_
      have h1 : (⟨y * ((u : Γ) * y * (u : Γ)⁻¹), hCm (hBC hy) (hBC hy')⟩ :
          ↥(F.P ⊓ centralizer ({F.e ^ 2} : Set Γ))) =
          ⟨y, hBC hy⟩ * (u * ⟨y, hBC hy⟩ * u⁻¹) := rfl
      rw [h1, map_mul, hu ⟨y, hBC hy⟩ hy, mul_inv_cancel]
    have h1 := F.eq_one_of_mem_Kb_Zb _ (F.Kb.mul_mem hyK hyK') ht
      (hBord _ (B.mul_mem hy hy'))
    exact eq_inv_of_mul_eq_one_right h1
  refine ⟨hnorm, fun x hx => ?_, hinvK⟩
  set x' := (u : Γ) * x * (u : Γ)⁻¹ with hx'
  have hx'B : x' ∈ B := hnorm x hx
  have hxp : x * x' ∈ F.Zb := by
    refine (F.ρ_eq_one ⟨_, hCm (hBC hx) (hBC hx'B)⟩).1 ?_
    have h1 : (⟨x * x', hCm (hBC hx) (hBC hx'B)⟩ :
          ↥(F.P ⊓ centralizer ({F.e ^ 2} : Set Γ))) =
        ⟨x, hBC hx⟩ * (u * ⟨x, hBC hx⟩ * u⁻¹) := rfl
    rw [h1, map_mul, hu ⟨x, hBC hx⟩ hx, mul_inv_cancel]
  have hux' : (u : Γ) * x' * (u : Γ)⁻¹ = x := by
    have hc := F.Zb_comm hxp u.2
    have h1 : x' = x⁻¹ * (x * x') := by group
    calc (u : Γ) * x' * (u : Γ)⁻¹ = ((u : Γ) * x⁻¹ * (u : Γ)⁻¹) *
          ((u : Γ) * (x * x') * (u : Γ)⁻¹) := by rw [h1]; group
      _ = x'⁻¹ * (x * x') := by
          rw [show (u : Γ) * (x * x') * (u : Γ)⁻¹ = x * x' by rw [← hc]; group]
          rw [hx']
          group
      _ = x := by
          rw [hBcomm x hx x' hx'B]
          group
  have hxm : x * x'⁻¹ ∈ F.Kb := by
    have hxmB : x * x'⁻¹ ∈ B := B.mul_mem hx (B.inv_mem hx'B)
    refine F.mem_Kb_of_inv ⟨_, hBC hxmB⟩ u (by
      rw [Subgroup.orderOf_mk]
      exact hBord _ hxmB) (Subtype.ext ?_)
    show (u : Γ) * (x * x'⁻¹) * (u : Γ)⁻¹ = (x * x'⁻¹)⁻¹
    calc (u : Γ) * (x * x'⁻¹) * (u : Γ)⁻¹ =
          ((u : Γ) * x * (u : Γ)⁻¹) * ((u : Γ) * x' * (u : Γ)⁻¹)⁻¹ := by group
      _ = x' * x⁻¹ := by rw [hux']
      _ = (x * x'⁻¹)⁻¹ := by group
  obtain ⟨j, hj⟩ := hBord x hx
  have hxx : x = (x * x') ^ (j + 1) * (x * x'⁻¹) ^ (j + 1) := by
    have hc : Commute (x * x') (x * x'⁻¹) :=
      hBcomm _ (B.mul_mem hx hx'B) _ (B.mul_mem hx (B.inv_mem hx'B))
    rw [← hc.mul_pow]
    have h1 : x * x' * (x * x'⁻¹) = x ^ 2 := by
      rw [sq]
      calc x * x' * (x * x'⁻¹) = x * (x' * x) * x'⁻¹ := by group
        _ = x * (x * x') * x'⁻¹ := by rw [hBcomm x' hx'B x hx]
        _ = x * x := by group
    rw [h1, ← pow_mul, show 2 * (j + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  exact ⟨(x * x') ^ (j + 1), B.pow_mem (B.mul_mem hx hx'B) _, F.Zb.pow_mem hxp _,
    (x * x'⁻¹) ^ (j + 1), B.pow_mem (B.mul_mem hx (B.inv_mem hx'B)) _, F.Kb.pow_mem hxm _, hxx⟩

theorem inv_of_not_mem [Finite Γ] {a d w : Γ} (hd : d ∈ F.Zb) (hd1 : d ≠ 1)
    (hdo : Odd (orderOf d)) (haP : a ∉ F.P) (had : a * d * a⁻¹ = d⁻¹) (hwP : w ∉ F.P)
    (hwz : w * F.e ^ 2 = F.e ^ 2 * w) : w * d * w⁻¹ = d⁻¹ := by
  have hnorm : ∀ g : Γ, g * d * g⁻¹ = d⁻¹ → ∀ c ∈ F.P ⊓ centralizer ({F.e ^ 2} : Set Γ),
      g * c * g⁻¹ ∈ F.P ⊓ centralizer ({F.e ^ 2} : Set Γ) := by
    intro g hg c hc
    have hcP : g * c * g⁻¹ ∈ F.P := F.P_normal.conj_mem c hc.1 g
    refine ⟨hcP, mem_centralizer_singleton_iff.2 ?_⟩
    refine F.comm_of_comm_Zb d hd hd1 hdo _ hcP ?_
    have hcd : d * c = c * d := F.Zb_comm hd hc
    have h1 : (g * c * g⁻¹) * d⁻¹ = d⁻¹ * (g * c * g⁻¹) := by
      rw [← hg]
      calc g * c * g⁻¹ * (g * d * g⁻¹) = g * (c * d) * g⁻¹ := by group
        _ = g * (d * c) * g⁻¹ := by rw [hcd]
        _ = g * d * g⁻¹ * (g * c * g⁻¹) := by group
    calc (g * c * g⁻¹) * d = d * (d⁻¹ * (g * c * g⁻¹)) * d := by group
      _ = d * ((g * c * g⁻¹) * d⁻¹) * d := by rw [h1]
      _ = d * (g * c * g⁻¹) := by group
  have ha' : a⁻¹ * d * a⁻¹⁻¹ = d⁻¹ := by
    have h : d = a⁻¹ * d⁻¹ * a := by rw [← had]; group
    calc a⁻¹ * d * a⁻¹⁻¹ = (a⁻¹ * d⁻¹ * a)⁻¹ := by group
      _ = d⁻¹ := by rw [← h]
  have hz : a * F.e ^ 2 * a⁻¹ = F.e ^ 2 := by
    have hmemZ : a * F.e ^ 2 * a⁻¹ ∈ F.Zb := by
      refine (F.mem_Zb _).2 ⟨hnorm a had _ F.z_mem_C, fun y hy => ?_⟩
      have hy' := hnorm a⁻¹ ha' y hy
      have hyz : (a⁻¹ * y * a⁻¹⁻¹) * F.e ^ 2 = F.e ^ 2 * (a⁻¹ * y * a⁻¹⁻¹) :=
        mem_centralizer_singleton_iff.1 hy'.2
      calc a * F.e ^ 2 * a⁻¹ * y = a * (F.e ^ 2 * (a⁻¹ * y * a⁻¹⁻¹)) * a⁻¹ := by group
        _ = a * ((a⁻¹ * y * a⁻¹⁻¹) * F.e ^ 2) * a⁻¹ := by rw [hyz]
        _ = y * (a * F.e ^ 2 * a⁻¹) := by group
    have h2 : orderOf (a * F.e ^ 2 * a⁻¹) = 2 := by
      have hsc : SemiconjBy a (F.e ^ 2) (a * F.e ^ 2 * a⁻¹) := by
        unfold SemiconjBy
        group
      rw [← hsc.orderOf_eq, F.orderOf_z]
    exact eq_of_orderOf_two_of_isCyclic F.isCyclic_Zb hmemZ F.z_mem_Zb h2 F.orderOf_z
  have hwa : w⁻¹ * a ∈ F.P ⊓ centralizer ({F.e ^ 2} : Set Γ) := by
    refine ⟨F.mul_mem_of_not_mem _ _ (fun h => hwP (by simpa using F.P.inv_mem h)) haP,
      mem_centralizer_singleton_iff.2 ?_⟩
    have haz : a * F.e ^ 2 = F.e ^ 2 * a := by
      calc a * F.e ^ 2 = a * F.e ^ 2 * a⁻¹ * a := by group
        _ = F.e ^ 2 * a := by rw [hz]
    calc w⁻¹ * a * F.e ^ 2 = w⁻¹ * (F.e ^ 2 * a) := by rw [mul_assoc, haz]
      _ = w⁻¹ * (F.e ^ 2 * w) * w⁻¹ * a := by group
      _ = w⁻¹ * (w * F.e ^ 2) * w⁻¹ * a := by rw [hwz]
      _ = F.e ^ 2 * (w⁻¹ * a) := by group
  have hc := F.Zb_comm hd hwa
  calc w * d * w⁻¹ = w * (d * (w⁻¹ * a)) * a⁻¹ := by group
    _ = w * ((w⁻¹ * a) * d) * a⁻¹ := by rw [hc]
    _ = a * d * a⁻¹ := by group
    _ = d⁻¹ := had

theorem inv_of_inv_prime [Finite Γ] {w : Γ} (hwz : w * F.e ^ 2 = F.e ^ 2 * w) {B : Subgroup Γ}
    (hBodd : ∀ b ∈ B, Odd (orderOf b))
    (hpr : ∀ d ∈ B, d ∈ F.Zb → (orderOf d).Prime → w * d * w⁻¹ = d⁻¹) :
    ∀ d ∈ B, d ∈ F.Zb → w * d * w⁻¹ = d⁻¹ := by
  classical
  have hwz' : w⁻¹ * F.e ^ 2 = F.e ^ 2 * w⁻¹ := by
    calc w⁻¹ * F.e ^ 2 = w⁻¹ * (F.e ^ 2 * w) * w⁻¹ := by group
      _ = w⁻¹ * (w * F.e ^ 2) * w⁻¹ := by rw [hwz]
      _ = F.e ^ 2 * w⁻¹ := by group
  have hC : ∀ g : Γ, g * F.e ^ 2 = F.e ^ 2 * g → ∀ c ∈ F.P ⊓ centralizer ({F.e ^ 2} : Set Γ),
      g * c * g⁻¹ ∈ F.P ⊓ centralizer ({F.e ^ 2} : Set Γ) := by
    intro g hg c hc
    refine ⟨F.P_normal.conj_mem c hc.1 g, mem_centralizer_singleton_iff.2 ?_⟩
    have hcz : c * F.e ^ 2 = F.e ^ 2 * c := mem_centralizer_singleton_iff.1 hc.2
    have hg' : g⁻¹ * F.e ^ 2 = F.e ^ 2 * g⁻¹ := by
      calc g⁻¹ * F.e ^ 2 = g⁻¹ * (F.e ^ 2 * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * F.e ^ 2) * g⁻¹ := by rw [hg]
        _ = F.e ^ 2 * g⁻¹ := by group
    calc g * c * g⁻¹ * F.e ^ 2 = g * c * (g⁻¹ * F.e ^ 2) := by group
      _ = g * (c * F.e ^ 2) * g⁻¹ := by rw [hg']; group
      _ = g * (F.e ^ 2 * c) * g⁻¹ := by rw [hcz]
      _ = (g * F.e ^ 2) * c * g⁻¹ := by group
      _ = F.e ^ 2 * (g * c * g⁻¹) := by rw [hg]; group
  have hZn : ∀ x ∈ F.Zb, w * x * w⁻¹ ∈ F.Zb := by
    intro x hx
    refine (F.mem_Zb _).2 ⟨hC w hwz x (F.Zb_le_C hx), fun y hy => ?_⟩
    have hy' := hC w⁻¹ hwz' y hy
    have hc := F.Zb_comm hx hy'
    calc w * x * w⁻¹ * y = w * (x * (w⁻¹ * y * w⁻¹⁻¹)) * w⁻¹ := by group
      _ = w * ((w⁻¹ * y * w⁻¹⁻¹) * x) * w⁻¹ := by rw [hc]
      _ = y * (w * x * w⁻¹) := by group
  have hw2 : w ^ 2 ∈ F.P ⊓ centralizer ({F.e ^ 2} : Set Γ) := by
    refine ⟨F.sq_mem w, mem_centralizer_singleton_iff.2 ?_⟩
    rw [sq]
    calc w * w * F.e ^ 2 = w * (w * F.e ^ 2) := by group
      _ = F.e ^ 2 * (w * w) := by rw [hwz, ← mul_assoc, hwz, mul_assoc]
  intro d hdB hdZ
  have hwd : w * d * w⁻¹ ∈ zpowers d := by
    have := F.isCyclic_Zb
    have he : zpowers (⟨w * d * w⁻¹, hZn d hdZ⟩ : ↥F.Zb) = zpowers ⟨d, hdZ⟩ := by
      rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
        Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      have hsc : SemiconjBy w d (w * d * w⁻¹) := by
        unfold SemiconjBy
        group
      exact hsc.orderOf_eq.symm
    have hmem : (⟨w * d * w⁻¹, hZn d hdZ⟩ : ↥F.Zb) ∈ zpowers (⟨d, hdZ⟩ : ↥F.Zb) :=
      he ▸ mem_zpowers _
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hmem
    exact mem_zpowers_iff.2 ⟨n, by simpa using congrArg Subtype.val hn⟩
  set y := d * (w * d * w⁻¹) with hy
  have hyd : y ∈ zpowers d := (zpowers d).mul_mem (mem_zpowers d) hwd
  have hyB : y ∈ B := zpowers_le.2 hdB hyd
  have hyZ : y ∈ F.Zb := zpowers_le.2 hdZ hyd
  have hwy : w * y * w⁻¹ = y := by
    have h1 : w * (w * d * w⁻¹) * w⁻¹ = d := by
      have h2 := F.Zb_comm hdZ hw2
      rw [sq] at h2
      calc w * (w * d * w⁻¹) * w⁻¹ = (w * w) * d * (w * w)⁻¹ := by group
        _ = d := by rw [← h2]; group
    calc w * y * w⁻¹ = (w * d * w⁻¹) * (w * (w * d * w⁻¹) * w⁻¹) := by rw [hy]; group
      _ = (w * d * w⁻¹) * d := by rw [h1]
      _ = y := by rw [hy, F.Zb_comm (hZn d hdZ) (F.Zb_le_C hdZ)]
  by_cases hy1 : y = 1
  · exact eq_inv_of_mul_eq_one_right hy1
  exfalso
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (fun h => hy1 (orderOf_eq_one_iff.1 h))
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨y₁, hy₁⟩ := exists_prime_orderOf_dvd_card' (G := ↥(zpowers y)) q
    (by rw [Nat.card_zpowers]; exact hqd)
  have hy₁B : (y₁ : Γ) ∈ B := zpowers_le.2 hyB y₁.2
  have hy₁Z : (y₁ : Γ) ∈ F.Zb := zpowers_le.2 hyZ y₁.2
  have hy₁o : orderOf (y₁ : Γ) = q := by rw [Subgroup.orderOf_coe, hy₁]
  have hfix : w * (y₁ : Γ) * w⁻¹ = y₁ := by
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 y₁.2
    rw [← hn, ← conj_zpow, hwy]
  have hinv := hpr _ hy₁B hy₁Z (hy₁o ▸ hq)
  rw [hfix] at hinv
  have h2 : (y₁ : Γ) ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [hinv]
    exact mul_inv_cancel _
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [hy₁o] at h3
  have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h3
  have := hBodd _ hy₁B
  rw [hy₁o, hq2] at this
  exact (Nat.not_odd_iff_even.2 even_two) this

theorem exists_same_action [Finite Γ] {S : Subgroup Γ} (hS2 : IsPGroup 2 S)
    (hSz : ∀ s ∈ S, s * F.e ^ 2 = F.e ^ 2 * s)
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ F.P) (F.P ⊓ centralizer ({F.e ^ 2} : Set Γ)))
    {v : Γ} (hv : v ∈ S) : ∃ t ∈ S ⊓ F.P, ∀ y ∈ F.Kb, t * y * t⁻¹ = v * y * v⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup Γ := centralizer ({F.e ^ 2} : Set Γ) with hN
  have hmemN : ∀ {g : Γ}, g * F.e ^ 2 = F.e ^ 2 * g → g ∈ N := fun h =>
    mem_centralizer_singleton_iff.2 h
  have hNK : N ≤ normalizer (F.Kb : Set Γ) := by
    intro g hg
    have hgz : g * F.e ^ 2 = F.e ^ 2 * g := mem_centralizer_singleton_iff.1 hg
    have hgz' : g⁻¹ * F.e ^ 2 = F.e ^ 2 * g⁻¹ := by
      calc g⁻¹ * F.e ^ 2 = g⁻¹ * (F.e ^ 2 * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * F.e ^ 2) * g⁻¹ := by rw [hgz]
        _ = F.e ^ 2 * g⁻¹ := by group
    rw [mem_normalizer_iff]
    intro y
    refine ⟨fun hy => F.conj_mem_Kb g hgz y hy, fun hy => ?_⟩
    have h := F.conj_mem_Kb g⁻¹ hgz' _ hy
    rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at h
  let α : ↥N →* MulAut ↥F.Kb := F.Kb.normalizerMonoidHom.comp (Subgroup.inclusion hNK)
  have hα : ∀ (n : ↥N) (y : ↥F.Kb), ((α n y : ↥F.Kb) : Γ) = (n : Γ) * y * (n : Γ)⁻¹ :=
    fun n y => Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
  have hSN : S ≤ N := fun s hs => hmemN (hSz s hs)
  have hCN : F.P ⊓ centralizer ({F.e ^ 2} : Set Γ) ≤ N := inf_le_right
  have hW' : CFSG.ABGLocalTools.IsSylowOf 2 ((S ⊓ F.P).subgroupOf N)
      ((F.P ⊓ centralizer ({F.e ^ 2} : Set Γ)).subgroupOf N) := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff N, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (inf_le_left.trans hSN),
      inf_eq_left.2 hCN]
    exact hSyl
  have hα1 := PartTwo.s16c7_isSylowOf_map hW' α
  have hle1 : ((S ⊓ F.P).subgroupOf N).map α ≤ (S.subgroupOf N).map α :=
    Subgroup.map_mono (fun x hx => hx.1)
  have hle2 : (S.subgroupOf N).map α ≤
      ((F.P ⊓ centralizer ({F.e ^ 2} : Set Γ)).subgroupOf N).map α := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨g, hgC, hg⟩ := F.exists_conj_Kb s (hSz s hs)
    refine ⟨⟨g, hCN hgC⟩, hgC, ?_⟩
    ext y
    rw [hα, hα]
    exact (hg y y.2).symm
  have hS'2 : IsPGroup 2 ((S.subgroupOf N).map α) := (hS2.comap_subtype (K := N)).map α
  have heq := hα1.eq_of_le hle1 hle2 hS'2
  have hv' : α ⟨v, hSN hv⟩ ∈ ((S ⊓ F.P).subgroupOf N).map α := by
    rw [← heq]
    exact ⟨⟨v, hSN hv⟩, hv, rfl⟩
  obtain ⟨t, ht, htα⟩ := hv'
  refine ⟨t, ht, fun y hy => ?_⟩
  have h := congrArg (fun φ : MulAut ↥F.Kb => ((φ ⟨y, hy⟩ : ↥F.Kb) : Γ)) htα
  simp only [hα] at h
  exact h

theorem exists_inv_of_mem [Finite Γ] [hp : Fact p.Prime] (hp5 : 5 ≤ p) [Finite k] [CharP k p]
    {A S B : Subgroup Γ} (hIA : F.I ≤ A)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S A) (heS : F.e ∈ S) (hrS : F.r ∈ S)
    (hBab : IsMulCommutative ↥B) (hBodd : Odd (Nat.card B)) (h3 : 3 ∣ Nat.card B)
    (h5 : 5 ∣ Nat.card B) (hperm : (B : Set Γ) * (S : Set Γ) = (S : Set Γ) * (B : Set Γ))
    (hinv : ∀ d ∈ B, (orderOf d).Prime → (∀ x ∈ F.Kb, d * x = x * d) →
      ∃ a ∈ A, a * d * a⁻¹ = d⁻¹) :
    ∃ s ∈ S, ∀ b ∈ B, s * b * s⁻¹ = b⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  obtain ⟨hSA, hS2, -⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hS
  have hSz := F.comm_z_of_mem hS2 heS hrS
  have hSyl := F.isSylowOf_inf_P hIA hS hSz
  have hWC : S ⊓ F.P ≤ F.P ⊓ centralizer ({F.e ^ 2} : Set Γ) :=
    (CFSG.ABGLocalTools.isSylowOf_iff.1 hSyl).1
  have hW2 : IsPGroup 2 ↥(S ⊓ F.P) := hS2.to_le inf_le_left
  have heW : F.e ∈ S ⊓ F.P := ⟨heS, F.I_le_P F.e_mem⟩
  have hrW : F.r ∈ S ⊓ F.P := ⟨hrS, F.I_le_P F.r_mem⟩
  have hBord : ∀ b ∈ B, Odd (orderOf b) := fun b hb =>
    Odd.of_dvd_nat hBodd (Subgroup.orderOf_dvd_natCard B hb)
  have hBP : B ≤ F.P := fun b hb => F.mem_P_of_odd (hBord b hb)
  have hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨A₀, hA₀B, hA₀mem, hA₀ord, hA₀6, hA₀5⟩ := exists_A₀ hBcomm hBodd h5
  have hSA₀ := F.conj_mem_A₀ hS2 hBab hBodd hBP hperm hA₀B hA₀mem hA₀ord
  have hA₀N : ∀ s ∈ S, s ∈ normalizer (A₀ : Set Γ) := by
    intro s hs
    rw [mem_normalizer_iff]
    intro a
    refine ⟨fun ha => hSA₀ s hs a ha, fun ha => ?_⟩
    have h := hSA₀ s⁻¹ (S.inv_mem hs) _ ha
    rwa [show s⁻¹ * (s * a * s⁻¹) * s⁻¹⁻¹ = a by group] at h
  have hA₀z := F.comm_of_abelian A₀ B hA₀B hBP hBab h3 h5 hA₀6 (hA₀N _ heS) (hA₀N _ hrS)
  have hA₀C : A₀ ≤ F.P ⊓ centralizer ({F.e ^ 2} : Set Γ) := fun a ha =>
    ⟨hBP (hA₀B ha), mem_centralizer_singleton_iff.2 (hA₀z a ha)⟩
  have hA₀ne : A₀ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hA₀5
    norm_num at hA₀5
  have hBC := F.le_C hp5 hSyl heW hrW hBcomm hBodd hBP hA₀B hA₀ne hA₀6
    (fun w hw a ha => hSA₀ w hw.1 a ha) hA₀C
  have hpermW : (B : Set Γ) * ((S ⊓ F.P : Subgroup Γ) : Set Γ) =
      ((S ⊓ F.P : Subgroup Γ) : Set Γ) * (B : Set Γ) := by
    ext g
    constructor
    · rintro ⟨b, hb, w, hw, rfl⟩
      have h : b * w ∈ (B : Set Γ) * (S : Set Γ) := Set.mul_mem_mul hb hw.1
      rw [hperm] at h
      obtain ⟨s, hs, b', hb', he⟩ := h
      have he' : s * b' = b * w := he
      have hsP : s ∈ F.P := by
        have h' : s = b * w * b'⁻¹ := by rw [← he']; group
        rw [h']
        exact F.P.mul_mem (F.P.mul_mem (hBP hb) hw.2) (F.P.inv_mem (hBP hb'))
      exact ⟨s, ⟨hs, hsP⟩, b', hb', he⟩
    · rintro ⟨w, hw, b, hb, rfl⟩
      have h : w * b ∈ (S : Set Γ) * (B : Set Γ) := Set.mul_mem_mul hw.1 hb
      rw [← hperm] at h
      obtain ⟨b', hb', s, hs, he⟩ := h
      have he' : b' * s = w * b := he
      have hsP : s ∈ F.P := by
        have h' : s = b'⁻¹ * (w * b) := by rw [← he']; group
        rw [h']
        exact F.P.mul_mem (F.P.inv_mem (hBP hb')) (F.P.mul_mem hw.2 (hBP hb))
      exact ⟨b', hb', s, ⟨hs, hsP⟩, he⟩
  have hdec := exists_mul_of_permutes hpermW
  have hBp : ∀ b : ↥(F.P ⊓ centralizer ({F.e ^ 2} : Set Γ)), (b : Γ) ∈ B →
      orderOf (F.ρ b) ≠ p := by
    intro b hb hbp
    have hb0 : orderOf (b : Γ) ≠ 0 := (orderOf_pos_iff.2 (isOfFinOrder_of_finite _)).ne'
    obtain ⟨i, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hb0 p hp.out.ne_one
    have hvB : ((b ^ m : ↥(F.P ⊓ centralizer ({F.e ^ 2} : Set Γ))) : Γ) ∈ B := by
      rw [Subgroup.coe_pow]
      exact B.pow_mem hb m
    have hvo : orderOf ((b ^ m : ↥(F.P ⊓ centralizer ({F.e ^ 2} : Set Γ))) : Γ) ∣ p ^ i := by
      rw [Subgroup.coe_pow]
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
    have hvA : ((b ^ m : ↥(F.P ⊓ centralizer ({F.e ^ 2} : Set Γ))) : Γ) ∈ A₀ :=
      hA₀mem _ hvB (Nat.Coprime.coprime_dvd_left hvo (Nat.Coprime.pow_left i
        ((Nat.coprime_primes hp.out Nat.prime_three).2 hp3)))
    have hρv : orderOf (F.ρ (b ^ m)) = p := by
      rw [map_pow, Nat.Coprime.orderOf_pow (by
        rw [hbp]
        exact (Nat.Prime.coprime_iff_not_dvd hp.out).2 hm), hbp]
    exact F.not_unip _ (hA₀ord _ hvA) hρv (hBcomm _ hvB _ (hA₀B (hSA₀ _ heS _ hvA)))
      (hBcomm _ hvB _ (hA₀B (hSA₀ _ hrS _ hvA)))
  obtain ⟨u, huW, hu⟩ := F.exists_inv_rho hp2 hBC hSyl heW hrW hBodd hBp hdec
  obtain ⟨-, hdecB, hinvK⟩ := F.decomp hBC hWC hW2 hBcomm hBodd hdec u huW hu
  by_cases hD : ∀ d ∈ B, d ∈ F.Zb → d = 1
  · refine ⟨u, huW.1, fun b hb => ?_⟩
    obtain ⟨x, hxB, hxZ, y, hyB, hyK, rfl⟩ := hdecB b hb
    rw [hD x hxB hxZ, one_mul]
    exact hinvK y hyB hyK
  push Not at hD
  obtain ⟨d₀, hd₀B, hd₀Z, hd₀1⟩ := hD
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (fun h => hd₀1 (orderOf_eq_one_iff.1 h))
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨d₁, hd₁⟩ := exists_prime_orderOf_dvd_card' (G := ↥(zpowers d₀)) q
    (by rw [Nat.card_zpowers]; exact hqd)
  have hd₁B : (d₁ : Γ) ∈ B := zpowers_le.2 hd₀B d₁.2
  have hd₁Z : (d₁ : Γ) ∈ F.Zb := zpowers_le.2 hd₀Z d₁.2
  have hd₁o : orderOf (d₁ : Γ) = q := by rw [Subgroup.orderOf_coe, hd₁]
  have hd₁1 : (d₁ : Γ) ≠ 1 := fun h => by
    rw [h, orderOf_one] at hd₁o
    exact hq.one_lt.ne hd₁o
  obtain ⟨a, haA, had⟩ := hinv _ hd₁B (hd₁o ▸ hq) (fun x hx => F.Zb_comm hd₁Z (F.Kb_le hx))
  have haP : a ∉ F.P := fun h => F.not_inv_Zb _ hd₁Z hd₁1 (hBord _ hd₁B) a h had
  obtain ⟨v, hvS, hvP⟩ : ∃ v ∈ S, v ∉ F.P := by
    have ha0 : orderOf a ≠ 0 := (orderOf_pos_iff.2 (isOfFinOrder_of_finite a)).ne'
    obtain ⟨i, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd ha0 2 (by norm_num)
    have hmo : Odd m := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hm)
    have ham : a ^ m ∉ F.P := by
      intro h
      apply haP
      obtain ⟨j, hj⟩ := hmo
      have he : a = a ^ m * ((a ^ j) ^ 2)⁻¹ := by
        rw [hj, ← pow_mul, pow_succ, mul_comm 2 j]
        group
      rw [he]
      exact F.P.mul_mem h (F.P.inv_mem (F.sq_mem _))
    have hR : IsPGroup 2 (zpowers (a ^ m)) := IsPGroup.of_card_dvd_pow (n := i) (by
      rw [Nat.card_zpowers]
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one])
    obtain ⟨g, hgA, hg⟩ := IsPGroup.exists_mem_conj_mem_of_card_eq hSA hS.card_eq
      (zpowers_le.2 (A.pow_mem haA m)) hR
    refine ⟨g⁻¹ * a ^ m * g, hg _ (mem_zpowers _), fun h => ham ?_⟩
    have h' := F.P_normal.conj_mem _ h g
    rwa [show g * (g⁻¹ * a ^ m * g) * g⁻¹ = a ^ m by group] at h'
  obtain ⟨t, htW, htv⟩ := F.exists_same_action hS2 hSz hSyl hvS
  set w' := t⁻¹ * v with hw'
  have hw'S : w' ∈ S := S.mul_mem (S.inv_mem htW.1) hvS
  have hw'P : w' ∉ F.P := fun h => hvP (by
    have h' := F.P.mul_mem htW.2 h
    rwa [show t * (t⁻¹ * v) = v by group] at h')
  have hw'K : ∀ y ∈ F.Kb, w' * y * w'⁻¹ = y := by
    intro y hy
    calc w' * y * w'⁻¹ = t⁻¹ * (v * y * v⁻¹) * t := by rw [hw']; group
      _ = t⁻¹ * (t * y * t⁻¹) * t := by rw [htv y hy]
      _ = y := by group
  have hw'z := hSz w' hw'S
  have hw'D := F.inv_of_inv_prime hw'z hBord (fun d hdB hdZ hdp => by
    have hd1 : d ≠ 1 := fun h => by
      rw [h, orderOf_one] at hdp
      exact Nat.not_prime_one hdp
    obtain ⟨a', ha'A, ha'd⟩ := hinv d hdB hdp (fun x hx => F.Zb_comm hdZ (F.Kb_le hx))
    have ha'P : a' ∉ F.P := fun h => F.not_inv_Zb d hdZ hd1 (hBord d hdB) a' h ha'd
    exact F.inv_of_not_mem hdZ hd1 (hBord d hdB) ha'P ha'd hw'P hw'z)
  refine ⟨u * w', S.mul_mem huW.1 hw'S, fun b hb => ?_⟩
  obtain ⟨x, hxB, hxZ, y, hyB, hyK, rfl⟩ := hdecB b hb
  have hux : (u : Γ) * x⁻¹ * (u : Γ)⁻¹ = x⁻¹ := by
    rw [(F.Zb_comm (F.Zb.inv_mem hxZ) u.2).symm]
    group
  calc (u * w') * (x * y) * (u * w')⁻¹ =
        (u : Γ) * (w' * x * w'⁻¹) * (w' * y * w'⁻¹) * (u : Γ)⁻¹ := by group
    _ = ((u : Γ) * x⁻¹ * (u : Γ)⁻¹) * ((u : Γ) * y * (u : Γ)⁻¹) := by
        rw [hw'D x hxB hxZ, hw'K y hyK]
        group
    _ = x⁻¹ * y⁻¹ := by rw [hux, hinvK y hyB hyK]
    _ = (x * y)⁻¹ := by rw [hBcomm _ (B.inv_mem hxB) _ (B.inv_mem hyB), mul_inv_rev]

theorem exists_inv [Finite Γ] [hp : Fact p.Prime] (hp5 : 5 ≤ p) [Finite k] [CharP k p]
    {A S B : Subgroup Γ} (hIA : F.I ≤ A)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S A) (hBab : IsMulCommutative ↥B)
    (hBodd : Odd (Nat.card B)) (h3 : 3 ∣ Nat.card B) (h5 : 5 ∣ Nat.card B)
    (hperm : (B : Set Γ) * (S : Set Γ) = (S : Set Γ) * (B : Set Γ))
    (hinv : ∀ g ∈ F.I, ∀ d ∈ B, (orderOf d).Prime →
      (∀ x ∈ F.Kb, d * (g * x * g⁻¹) = g * x * g⁻¹ * d) → ∃ a ∈ A, a * d * a⁻¹ = d⁻¹) :
    ∃ s ∈ S, ∀ b ∈ B, s * b * s⁻¹ = b⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := F.I_normal
  have hAI : A ≤ normalizer (F.I : Set Γ) := fun a _ =>
    (Subgroup.normalizer_eq_top_iff.2 F.I_normal).symm ▸ Subgroup.mem_top a
  have hSI := hS.inf_of_le_normalizer hIA hAI
  obtain ⟨g, hgI, hg⟩ := IsPGroup.exists_mem_conj_mem_of_card_eq inf_le_right hSI.card_eq
    ((closure_le F.I).2 (by
      rintro x (rfl | rfl)
      · exact F.e_mem
      · exact F.r_mem)) F.isPGroup_D8
  have heS : g⁻¹ * F.e * g ∈ S := (hg _ (subset_closure (Set.mem_insert _ _))).1
  have hrS : g⁻¹ * F.r * g ∈ S :=
    (hg _ (subset_closure (Set.mem_insert_of_mem _ rfl))).1
  let c : Γ →* Γ := (MulAut.conj g).toMonoidHom
  have hc : ∀ x, c x = g * x * g⁻¹ := fun x => rfl
  have hgA : g ∈ A := hIA hgI
  have hcA : A.map c = A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hc]
      exact A.mul_mem (A.mul_mem hgA hy) (A.inv_mem hgA)
    · intro hx
      refine ⟨g⁻¹ * x * g, A.mul_mem (A.mul_mem (A.inv_mem hgA) hx) hgA, ?_⟩
      rw [hc]
      group
  have hcinj : Function.Injective c := (MulAut.conj g).injective
  have hS' : CFSG.ABGLocalTools.IsSylowOf 2 (S.map c) A := by
    have h := PartTwo.s16c7_isSylowOf_map hS c
    rwa [hcA] at h
  have heS' : F.e ∈ S.map c := ⟨_, heS, by rw [hc]; group⟩
  have hrS' : F.r ∈ S.map c := ⟨_, hrS, by rw [hc]; group⟩
  have eB : ↥B ≃* ↥(B.map c) := B.equivMapOfInjective c hcinj
  have hBab' : IsMulCommutative ↥(B.map c) := by
    refine ⟨⟨fun x y => ?_⟩⟩
    apply eB.symm.injective
    rw [map_mul, map_mul]
    exact hBab.is_comm.comm _ _
  have hcard : Nat.card ↥(B.map c) = Nat.card B := (Nat.card_congr eB.toEquiv).symm
  have hperm' : ((B.map c : Subgroup Γ) : Set Γ) * ((S.map c : Subgroup Γ) : Set Γ) =
      ((S.map c : Subgroup Γ) : Set Γ) * ((B.map c : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, hperm, Set.image_mul]
  obtain ⟨s', hs', hs'B⟩ := F.exists_inv_of_mem hp5 hIA hS' heS' hrS' hBab'
    (hcard ▸ hBodd) (hcard ▸ h3) (hcard ▸ h5) hperm' (by
      rintro _ ⟨d, hd, rfl⟩ hdp hdK
      rw [hc] at hdp hdK ⊢
      have hsc : SemiconjBy g d (g * d * g⁻¹) := by
        unfold SemiconjBy
        group
      obtain ⟨a, haA, had⟩ := hinv g⁻¹ (F.I.inv_mem hgI) d hd (hsc.orderOf_eq ▸ hdp) (by
        intro x hx
        have h := hdK x hx
        calc d * (g⁻¹ * x * g⁻¹⁻¹) = g⁻¹ * ((g * d * g⁻¹) * x) * g := by group
          _ = g⁻¹ * (x * (g * d * g⁻¹)) * g := by rw [h]
          _ = g⁻¹ * x * g⁻¹⁻¹ * d := by group)
      refine ⟨g * a * g⁻¹, A.mul_mem (A.mul_mem hgA haA) (A.inv_mem hgA), ?_⟩
      calc g * a * g⁻¹ * (g * d * g⁻¹) * (g * a * g⁻¹)⁻¹ = g * (a * d * a⁻¹) * g⁻¹ := by group
        _ = (g * d * g⁻¹)⁻¹ := by rw [had]; group)
  obtain ⟨s, hs, rfl⟩ := hs'
  refine ⟨s, hs, fun b hb => ?_⟩
  have h := hs'B (c b) ⟨b, hb, rfl⟩
  rw [hc, hc] at h
  have h' : g * (s * b * s⁻¹) * g⁻¹ = g * b⁻¹ * g⁻¹ := by
    calc g * (s * b * s⁻¹) * g⁻¹ = g * s * g⁻¹ * (g * b * g⁻¹) * (g * s * g⁻¹)⁻¹ := by group
      _ = (g * b * g⁻¹)⁻¹ := h
      _ = g * b⁻¹ * g⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h')

end L3Frame

end CFSG.LocalAnalysis.UniquenessCase.UC22

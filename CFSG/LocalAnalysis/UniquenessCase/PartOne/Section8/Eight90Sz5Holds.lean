module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Sz5GLevel
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Sz5CoreK
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Sz5Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

namespace Sz5

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped IsMulCommutative commutatorElement

theorem ringChar_zmod_ne_two {p : ℕ} (hp2 : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  exact hp2

theorem sz5e1_isElementaryAbelian_quot {G : Type} [Group G] {p : ℕ} (X Y : Subgroup G)
    [(Y.subgroupOf X).Normal] (hXp : ∀ x ∈ X, x ^ p = 1) (hXY : ⁅X, X⁆ ≤ Y) :
    IsElementaryAbelian p (↥X ⧸ Y.subgroupOf X) where
  is_comm := ⟨fun x y => by
    induction x using QuotientGroup.induction_on with
    | H a =>
    induction y using QuotientGroup.induction_on with
    | H b =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
    have h : (((a * b)⁻¹ * (b * a) : X) : G) = ⁅(b : G)⁻¹, (a : G)⁻¹⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [h]
    exact hXY (Subgroup.commutator_mem_commutator (X.inv_mem b.2) (X.inv_mem a.2))⟩
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro x
    induction x using QuotientGroup.induction_on with
    | H a =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf, Subgroup.coe_pow,
      hXp _ a.2]
    exact Y.one_mem

theorem sz5e1_normalizer_commutator {G : Type} [Group G] (K X : Subgroup G)
    (hKX : K ≤ normalizer (X : Set G)) : K ≤ normalizer ((⁅X, X⁆ : Subgroup G) : Set G) := by
  intro k hk
  have h := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKX hk)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator, h]

theorem sz5e1_lemma51 {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (K : Subgroup G) (hK : ⁅K, K⁆ = K) (hSz : IsSz (Bar2 K) 3)
    (hrank : ∀ T : Subgroup G, T ≤ K → T ≠ ⊥ → IsPGroup 2 T →
      CFSG.Open.pRank p (normalizer (T : Set G)) ≤ 3)
    (E : Subgroup G) (hEp : ∀ x ∈ E, x ^ p = 1) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hKE : K ≤ normalizer (E : Set G)) : ⁅E, K⁆ = ⊥ := by
  have hKbot : K ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp [Subgroup.mem_bot]
  have : IsElementaryAbelian p (↥E ⧸ (⊥ : Subgroup G).subgroupOf E) :=
    sz5e1_isElementaryAbelian_quot E ⊥ hEp (by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hEc a ha b hb)
  have hfix := sz5e1_fixbound_abelian K E hrank hEc hEp hKE hKbot
  have htriv := sz5e1_module_trivial (hF := ringChar_zmod_ne_two hp2) (CFSG.pCore 2 ↥K)
    (SzSetup.of_subgroup K hK hSz) (chiefRepE (p := p) hKE hKbot) hfix
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro w hw k hk
  exact (chiefRepE_eq_one_iff (p := p) hKE hKbot ⟨k, hk⟩).mp (htriv ⟨k, hk⟩) w hw

theorem sz5e1_strongCentralization {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G),
      ⁅K, K⁆ = K → IsSz (Bar2 K) 3 →
      (∀ T : Subgroup G, T ≤ K → T ≠ ⊥ → IsPGroup 2 T →
        CFSG.Open.pRank p (normalizer (T : Set G)) ≤ 3) →
      ∀ X : Subgroup G, IsPGroup p X → (∀ x ∈ X, x ^ p = 1) → ⁅⁅X, X⁆, X⁆ = ⊥ →
        K ≤ normalizer (X : Set G) → ⁅X, K⁆ = ⊥ := by
  intro G _ _ K hK hSz hrank X hX5 hXexp hXcl hKX
  have hSetup := SzSetup.of_subgroup K hK hSz
  set Z : Subgroup G := ⁅X, X⁆ with hZdef
  have hZX : Z ≤ X := Subgroup.commutator_le.mpr (fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact X.mul_mem (X.mul_mem (X.mul_mem h₁ h₂) (X.inv_mem h₁)) (X.inv_mem h₂))
  have hZc : ∀ z ∈ Z, ∀ x ∈ X, z * x = x * z := by
    intro z hz x hx
    have hmem : ⁅z, x⁆ ∈ ⁅Z, X⁆ := Subgroup.commutator_mem_commutator hz hx
    rw [hXcl, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  have hKZ : K ≤ normalizer (Z : Set G) := sz5e1_normalizer_commutator K X hKX
  have hZn : (Z.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer (by
    rw [Subgroup.le_normalizer_iff]
    intro x hx z hz
    rw [← hZc z hz x hx, mul_inv_cancel_right]
    exact hz)
  have : IsElementaryAbelian p (↥X ⧸ Z.subgroupOf X) :=
    sz5e1_isElementaryAbelian_quot X Z hXexp le_rfl
  have hZE : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb => hZc a ha b (hZX hb)
  have hZK : ⁅Z, K⁆ = ⊥ :=
    sz5e1_lemma51 hp2 K hK hSz hrank Z (fun x hx => hXexp x (hZX hx)) hZE hKZ
  have hfix := sz5e1_fixbound_class_two hp2 K X Z hrank hX5 hXexp hXcl hKX hKZ
  by_cases htriv : ∀ k : ↥K, chiefRepE (p := p) hKX hKZ k = 1
  · have hXKZ : ⁅X, K⁆ ≤ Z := by
      rw [Subgroup.commutator_le]
      intro x hx k hk
      exact (chiefRepE_eq_one_iff (p := p) hKX hKZ ⟨k, hk⟩).mp (htriv ⟨k, hk⟩) x hx
    have hZcen : Z ≤ centralizer (K : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZK
    exact r890_commutator_eq_bot_of_perfect hK (hXKZ.trans hZcen)
  · exfalso
    obtain ⟨k0, hk0⟩ := not_forall.mp htriv
    obtain ⟨B, hB, hBnt, hC⟩ := sz5e1_module_forms (hF := ringChar_zmod_ne_two hp2)
      (CFSG.pCore 2 ↥K) hSetup (chiefRepE (p := p) hKX hKZ) hfix ⟨k0, hk0⟩
    exact sz5e1_class_two_endgame K X Z hX5 hXexp hXcl hZX hZc le_rfl hKX hKZ hZK
      (fun E _ hEp hc hKE => sz5e1_lemma51 hp2 K hK hSz hrank E hEp hc hKE) B hB hBnt hC

end Sz5

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped IsMulCommutative

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

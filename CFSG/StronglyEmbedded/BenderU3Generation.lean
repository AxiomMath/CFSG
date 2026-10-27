module

import CFSG.GH74.Uniqueness.Bender.Unitary
import CFSG.GH74.Uniqueness.Bender.UnitaryIrreducible
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderBasic

public section

namespace CFSG.StronglyEmbedded.BenderCentre

open CFSG.BenderSuzuki
open CFSG.GH74.Uniqueness.Bender
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter)
open scoped commutatorElement

theorem u3NormalizedGenerationStatement_holds :
    ∀ (K : Type) [Group K] [Finite K] (n : ℕ), 2 ≤ n → Nonempty (K ≃* PSU3Model n) →
      ∀ S : Sylow 2 K, ∀ R : Subgroup K, R ≤ (S : Subgroup K) →
        sylowCenter (S : Subgroup K) < R →
        (∀ g ∈ Subgroup.normalizer ((S : Subgroup K) : Set K),
          (∀ z ∈ sylowCenter (S : Subgroup K), g * z = z * g) → ∀ r ∈ R, g * r * g⁻¹ ∈ R) →
        ∀ a : K, a ≠ 1 → a * a = 1 →
          a ∉ Subgroup.normalizer ((S : Subgroup K) : Set K) → R ⊔ Subgroup.zpowers a = ⊤ := by
  intro K _ _ n hn ⟨e⟩ S R hRS hZR hnorm a ha1 ha2 haN
  have h := BenderType.unitary n hn e
  have haB : a ∉ borel (S : Subgroup K) := haN
  have hc := h.benderCore S ha2 haB
  have hZeq : sylowCenter (S : Subgroup K) = rootCenter (S : Subgroup K) := rfl
  rw [hZeq] at hZR hnorm
  have hZne : rootCenter (S : Subgroup K) ≠ ⊥ := by
    intro hbot
    have h1 := hc.card_center
    rw [hbot, Subgroup.card_bot] at h1
    have h2 : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
    omega
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  have hz1' : z ≠ 1 := fun h' => hz1 (Subtype.ext h')
  obtain ⟨hL, -⟩ := h.lemma_3_2_h_unitary S ha2 haB hz hz1'
  have hZM : rootCenter (S : Subgroup K) ≤ R := hZR.le
  have hTLM : ⁅cartan (S : Subgroup K) a, Subgroup.zpowers a⁆ ≤ R ⊔ Subgroup.zpowers a :=
    (le_sup_right.trans hL.le).trans (sup_le_sup_right hZM _)
  let C : Set K := {x | ∃ τ ∈ ⁅cartan (S : Subgroup K) a, Subgroup.zpowers a⁆, ∃ r ∈ R,
    x = τ * r * τ⁻¹}
  have hTLB : ∀ τ ∈ ⁅cartan (S : Subgroup K) a, Subgroup.zpowers a⁆,
      τ ∈ borel (S : Subgroup K) := fun τ hτ =>
    cartan_le_borel _ _ (hc.commutator_cartan_le hτ)
  have hWM : Subgroup.closure C ≤ R ⊔ Subgroup.zpowers a := by
    rw [Subgroup.closure_le]
    rintro _ ⟨τ, hτ, r, hr, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTLM hτ) (Subgroup.mem_sup_left hr))
      (Subgroup.inv_mem _ (hTLM hτ))
  have hWS : Subgroup.closure C ≤ (S : Subgroup K) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨τ, hτ, r, hr, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hTLB τ hτ) r).mp (hRS hr)
  have hRW : R ≤ Subgroup.closure C := fun r hr =>
    Subgroup.subset_closure ⟨1, Subgroup.one_mem _, r, hr, by group⟩
  have hF_comm : ∀ τ ∈ ⁅cartan (S : Subgroup K) a, Subgroup.zpowers a⁆,
      ∀ φ ∈ fixCartan (S : Subgroup K) a, τ * φ = φ * τ := hc.comm_commutator_fixCartan
  have hF_norm : ∀ φ ∈ fixCartan (S : Subgroup K) a, ∀ r ∈ R, φ * r * φ⁻¹ ∈ R := by
    intro φ hφ r hr
    refine hnorm φ (cartan_le_borel _ _ (fixCartan_le_cartan _ _ hφ)) (fun z' hz' => ?_) r hr
    by_cases hz'1 : z' = 1
    · rw [hz'1]
      simp
    · have hmem : φ ∈ cartan (S : Subgroup K) a ⊓ Subgroup.centralizer ({z'} : Set K) := by
        rw [hc.cartan_inf_centralizer_eq hz' hz'1]
        exact hφ
      exact Subgroup.mem_centralizer_singleton_iff.mp hmem.2
  have hconjTL : ∀ τ₀ ∈ ⁅cartan (S : Subgroup K) a, Subgroup.zpowers a⁆,
      ∀ w ∈ Subgroup.closure C, τ₀ * w * τ₀⁻¹ ∈ Subgroup.closure C := by
    intro τ₀ hτ₀ w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨τ, hτ, r, hr, rfl⟩ := hx
      exact Subgroup.subset_closure
        ⟨τ₀ * τ, Subgroup.mul_mem _ hτ₀ hτ, r, hr, by group⟩
    | one => simp
    | mul x y _ _ hx hy =>
      have : τ₀ * (x * y) * τ₀⁻¹ = (τ₀ * x * τ₀⁻¹) * (τ₀ * y * τ₀⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have : τ₀ * x⁻¹ * τ₀⁻¹ = (τ₀ * x * τ₀⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ hx
  have hconjF : ∀ φ ∈ fixCartan (S : Subgroup K) a,
      ∀ w ∈ Subgroup.closure C, φ * w * φ⁻¹ ∈ Subgroup.closure C := by
    intro φ hφ w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨τ, hτ, r, hr, rfl⟩ := hx
      refine Subgroup.subset_closure ⟨τ, hτ, φ * r * φ⁻¹, hF_norm φ hφ r hr, ?_⟩
      have hc' : φ * τ = τ * φ := (hF_comm τ hτ φ hφ).symm
      calc φ * (τ * r * τ⁻¹) * φ⁻¹ = (φ * τ) * r * (φ * τ)⁻¹ := by group
        _ = (τ * φ) * r * (τ * φ)⁻¹ := by rw [hc']
        _ = τ * (φ * r * φ⁻¹) * τ⁻¹ := by group
    | one => simp
    | mul x y _ _ hx hy =>
      have : φ * (x * y) * φ⁻¹ = (φ * x * φ⁻¹) * (φ * y * φ⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have : φ * x⁻¹ * φ⁻¹ = (φ * x * φ⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ hx
  have hinv : ∀ d ∈ cartan (S : Subgroup K) a, ∀ w ∈ Subgroup.closure C,
      d * w * d⁻¹ ∈ Subgroup.closure C := by
    intro d hd w hw
    have hsup : d ∈ ⁅cartan (S : Subgroup K) a, Subgroup.zpowers a⁆ ⊔
        fixCartan (S : Subgroup K) a := hc.cartan_eq_sup ▸ hd
    obtain ⟨τ, hτ, φ, hφ, rfl⟩ := exists_mul_of_mem_sup_of_commute hF_comm hsup
    have : τ * φ * w * (τ * φ)⁻¹ = τ * (φ * w * φ⁻¹) * τ⁻¹ := by group
    rw [this]
    exact hconjTL τ hτ _ (hconjF φ hφ w hw)
  have hZW : rootCenter (S : Subgroup K) ≤ Subgroup.closure C := hZM.trans hRW
  have hSM : (S : Subgroup K) ≤ R ⊔ Subgroup.zpowers a := by
    rcases h.irreducible_unitary S ha2 haB (Subgroup.closure C) hZW hWS hinv with hWZ | hWS'
    · exact absurd (hRW.trans hWZ.le) (not_le_of_gt hZR)
    · exact hWS' ▸ hWM
  have haM : a ∈ R ⊔ Subgroup.zpowers a := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hN : Subgroup.normalClosure ((S : Subgroup K) : Set K) ≤ R ⊔ Subgroup.zpowers a := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    obtain ⟨s, hs, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
    by_cases hcB : c ∈ borel (S : Subgroup K)
    · exact hSM ((Subgroup.mem_normalizer_iff.mp hcB s).mp hs)
    · obtain ⟨p, hp, m, hm, rfl⟩ := hc.bruhat hcB
      have hms : m * s * m⁻¹ ∈ (S : Subgroup K) := (Subgroup.mem_normalizer_iff.mp hm s).mp hs
      have e : p * a * m * s * (p * a * m)⁻¹ = (p * a) * (m * s * m⁻¹) * (p * a)⁻¹ := by group
      have hpa : p * a ∈ R ⊔ Subgroup.zpowers a := Subgroup.mul_mem _ (hSM hp) haM
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hpa (hSM hms)) (Subgroup.inv_mem _ hpa)
  have hsimple : IsSimpleGroup K := h.isSimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.normalClosure ((S : Subgroup K) : Set K)) with hb | ht
  · exfalso
    have hS1 : (S : Subgroup K) = ⊥ := by
      rw [eq_bot_iff, ← hb]
      exact Subgroup.le_normalClosure
    have hcard := hc.card_eq
    rw [hS1, Subgroup.card_bot] at hcard
    have h2 : 1 < (2 ^ n) ^ 3 := Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by omega))
    omega
  · rw [eq_top_iff, ← ht]
    exact hN

end CFSG.StronglyEmbedded.BenderCentre

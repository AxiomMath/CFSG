module

public import CFSG.RankThree.PartOne.S15K.L0cCore
import Mathlib.Algebra.Ring.GeomSum

public section

namespace CFSG.RankThree.PartOne.S15K

open scoped commutatorElement

@[expose] def PSylowSub {U : Type*} [Group U] (p : ℕ) (Y : Subgroup U) : Prop :=
  ∀ P : Subgroup U, P ≤ Y → (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) → (∀ x ∈ P, x ^ p = 1) → P ≠ ⊥ →
    ∃ S : Subgroup U, S ≤ Y ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧ P ≤ Subgroup.normalizer (S : Set U) ∧
      S = ⁅S, P⁆

theorem PSylowSub.toPSylowIn {G : Type} [Group G] {p : ℕ} {Y : Subgroup G} (h : PSylowSub p Y) :
    PSylowIn p Y := fun P hP hc hp hP1 _ => h P hP hc hp hP1

section Map

variable {U U' : Type*} [Group U] [Group U'] {p : ℕ}

theorem exists_comap_of_le_map {Y : Subgroup U} (Θ : U →* U') (hΘ : Function.Injective Θ)
    {P : Subgroup U'} (hP : P ≤ Y.map Θ) : P.comap Θ ≤ Y ∧ (P.comap Θ).map Θ = P := by
  have hPrange : P ≤ Θ.range := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hP hx
    exact ⟨y, rfl⟩
  refine ⟨fun x hx => ?_, Subgroup.map_comap_eq_self hPrange⟩
  obtain ⟨y, hy, hyx⟩ := hP hx
  rw [← hΘ hyx]
  exact hy

theorem PSylowSub.map {Y : Subgroup U} (Θ : U →* U') (hΘ : Function.Injective Θ) (h : PSylowSub p Y) :
    PSylowSub p (Y.map Θ) := by
  intro P hPY hcomm hpow hP1
  obtain ⟨hP'Y, hmapP'⟩ := exists_comap_of_le_map Θ hΘ hPY
  set P' : Subgroup U := P.comap Θ with hP'
  have hcomm' : ∀ x ∈ P', ∀ y ∈ P', x * y = y * x := fun x hx y hy =>
    hΘ (by rw [map_mul, map_mul]; exact hcomm _ hx _ hy)
  have hpow' : ∀ x ∈ P', x ^ p = 1 := fun x hx =>
    hΘ (by rw [map_pow, map_one]; exact hpow _ hx)
  have hP'1 : P' ≠ ⊥ := by
    intro hbot
    apply hP1
    rw [← hmapP', hbot, Subgroup.map_bot]
  obtain ⟨S₀, hS₀Y, hS₀1, hS₀2, hS₀N, hS₀c⟩ := h P' hP'Y hcomm' hpow' hP'1
  refine ⟨S₀.map Θ, Subgroup.map_mono hS₀Y, ?_, ?_, ?_, ?_⟩
  · intro hbot
    exact hS₀1 ((Subgroup.map_eq_bot_iff_of_injective _ hΘ).1 hbot)
  · exact hS₀2.of_surjective (Θ.subgroupMap S₀) (Θ.subgroupMap_surjective S₀)
  · intro x hx
    rw [← hmapP'] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · rintro ⟨s₀, hs₀, rfl⟩
      exact ⟨x' * s₀ * x'⁻¹, (Subgroup.mem_normalizer_iff.1 (hS₀N hx') s₀).1 hs₀, by simp⟩
    · rintro ⟨t, ht, hts⟩
      have h1 : x'⁻¹ * t * x' ∈ S₀ := by
        have := (Subgroup.mem_normalizer_iff.1 (hS₀N hx') (x'⁻¹ * t * x')).2
        exact this (by simpa [mul_assoc] using ht)
      refine ⟨x'⁻¹ * t * x', h1, ?_⟩
      rw [map_mul, map_mul, map_inv, hts]
      group
  · calc S₀.map Θ = (⁅S₀, P'⁆).map Θ := by rw [← hS₀c]
      _ = ⁅S₀.map Θ, P'.map Θ⁆ := Subgroup.map_commutator _ _ _
      _ = ⁅S₀.map Θ, P⁆ := by rw [hmapP']

theorem PSylowSub.of_map {Y : Subgroup U} (Θ : U →* U') (hΘ : Function.Injective Θ)
    (h : PSylowSub p (Y.map Θ)) : PSylowSub p Y := by
  intro P hPY hcomm hpow hP1
  have hPmap : P.map Θ ≤ Y.map Θ := Subgroup.map_mono hPY
  obtain ⟨S', hS'Y, hS'1, hS'2, hS'N, hS'c⟩ := h (P.map Θ) hPmap
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hcomm _ hx _ hy])
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hpow _ hx, map_one])
    (fun hbot => hP1 ((Subgroup.map_eq_bot_iff_of_injective _ hΘ).1 hbot))
  obtain ⟨hSY, hmapS⟩ := exists_comap_of_le_map Θ hΘ hS'Y
  set S : Subgroup U := S'.comap Θ with hS
  refine ⟨S, hSY, ?_, ?_, ?_, ?_⟩
  · intro hbot
    apply hS'1
    rw [← hmapS, hbot, Subgroup.map_bot]
  · exact hS'2.of_injective (Θ.subgroupComap S') (fun a b hab => Subtype.ext (hΘ (congrArg Subtype.val hab)))
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro s
    have hxN := Subgroup.mem_normalizer_iff.1 (hS'N ⟨x, hx, rfl⟩) (Θ s)
    show Θ s ∈ S' ↔ Θ (x * s * x⁻¹) ∈ S'
    rw [map_mul, map_mul, map_inv]
    exact hxN
  · apply Subgroup.map_injective hΘ
    calc S.map Θ = S' := hmapS
      _ = ⁅S', P.map Θ⁆ := hS'c
      _ = ⁅S.map Θ, P.map Θ⁆ := by rw [hmapS]
      _ = (⁅S, P⁆).map Θ := (Subgroup.map_commutator _ _ _).symm

theorem PSylowSub.of_mulEquiv {Λ : Type*} [Group Λ] {Y : Subgroup U} (e : Λ ≃* ↥Y)
    (h : PSylowSub p (⊤ : Subgroup Λ)) : PSylowSub p Y := by
  have hinj : Function.Injective (Y.subtype.comp e.toMonoidHom) :=
    Subtype.val_injective.comp e.injective
  have hrange : (⊤ : Subgroup Λ).map (Y.subtype.comp e.toMonoidHom) = Y := by
    rw [← MonoidHom.range_eq_map]
    ext y
    constructor
    · rintro ⟨l, rfl⟩
      exact (e l).2
    · intro hy
      exact ⟨e.symm ⟨y, hy⟩, by simp⟩
  rw [← hrange]
  exact h.map _ hinj

theorem PSylowSub.top_of {Y : Subgroup U} (h : PSylowSub p Y) : PSylowSub p (⊤ : Subgroup ↥Y) := by
  refine PSylowSub.of_map Y.subtype Subtype.val_injective ?_
  rw [Subgroup.map_top, Subgroup.range_subtype]
  exact h

end Map

section Le

variable {U : Type*} [Group U] {p : ℕ}

theorem PSylowSub.of_le {Y Y' : Subgroup U} (h : PSylowSub p Y) (hle : Y' ≤ Y)
    (h2 : ∀ x ∈ Y, ∀ k : ℕ, x ^ (2 ^ k) = 1 → x ∈ Y') : PSylowSub p Y' := by
  intro P hPY' hcomm hpow hP1
  obtain ⟨S, hSY, hS1, hS2, hSN, hSc⟩ := h P (hPY'.trans hle) hcomm hpow hP1
  refine ⟨S, fun s hs => ?_, hS1, hS2, hSN, hSc⟩
  obtain ⟨k, hk⟩ := hS2 ⟨s, hs⟩
  exact h2 s (hSY hs) k (by simpa using congrArg Subtype.val hk)

end Le

theorem false_of_dvd_pow_add_one {q p d : ℕ} (hp5 : 5 ≤ p) (hq : 0 < q) (hpq : p ∣ q - 1)
    (hpd : p ∣ q ^ d + 1) : False := by
  have h1 : p ∣ q ^ d - 1 := hpq.trans (by simpa using Nat.sub_dvd_pow_sub_pow q 1 d)
  have hpos : 1 ≤ q ^ d := Nat.one_le_pow _ _ hq
  have h2 : p ∣ 2 := by
    have := Nat.dvd_sub hpd h1
    have e : q ^ d + 1 - (q ^ d - 1) = 2 := by omega
    rwa [e] at this
  have := Nat.le_of_dvd (by norm_num) h2
  omega

section Scaling

variable {Λ : Type*} [Group Λ] {E : Type*} [Field E] [CharP E 2]

theorem exists_good_of_scaling (τ : Multiplicative E →* Λ) {P : Subgroup Λ}
    (hτ : τ (Multiplicative.ofAdd 1) ≠ 1)
    (hscale : ∀ h ∈ P, ∃ c : E, c ≠ 0 ∧ ∀ x : E,
      h * τ (Multiplicative.ofAdd x) = τ (Multiplicative.ofAdd (c * x)) * h)
    (hmove : ∃ g ∈ P, ∃ c : E, c ≠ 1 ∧ ∀ x : E,
      g * τ (Multiplicative.ofAdd x) = τ (Multiplicative.ofAdd (c * x)) * g) :
    ∃ S : Subgroup Λ, S = τ.range ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧ P ≤ Subgroup.normalizer (S : Set Λ) ∧
      S = ⁅S, P⁆ := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hmem : ∀ x : E, τ (Multiplicative.ofAdd x) ∈ τ.range := fun x => ⟨_, rfl⟩
  have hconj : ∀ h ∈ P, ∀ c : E, (∀ x : E, h * τ (Multiplicative.ofAdd x) =
      τ (Multiplicative.ofAdd (c * x)) * h) → ∀ x : E,
      h * τ (Multiplicative.ofAdd x) * h⁻¹ = τ (Multiplicative.ofAdd (c * x)) := by
    intro h _ c hc x
    rw [hc x]
    group
  have hnorm : ∀ h ∈ P, h ∈ Subgroup.normalizer ((τ.range : Subgroup Λ) : Set Λ) := by
    intro h hh
    obtain ⟨c, hc0, hc⟩ := hscale h hh
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · rintro ⟨y, rfl⟩
      have : y = Multiplicative.ofAdd (Multiplicative.toAdd y) := rfl
      rw [this, hconj h hh c hc]
      exact hmem _
    · rintro ⟨z, hz⟩
      have hz' : z = Multiplicative.ofAdd (Multiplicative.toAdd z) := rfl
      refine ⟨Multiplicative.ofAdd (c⁻¹ * Multiplicative.toAdd z), ?_⟩
      have h1 := hconj h hh c hc (c⁻¹ * Multiplicative.toAdd z)
      rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul, ← hz', hz] at h1
      have h2' : h * s * h⁻¹ = h * τ (Multiplicative.ofAdd (c⁻¹ * Multiplicative.toAdd z)) * h⁻¹ := by
        rw [h1]
      exact (mul_left_cancel (mul_right_cancel h2')).symm
  refine ⟨τ.range, rfl, ?_, ?_, hnorm, ?_⟩
  · intro hbot
    have := hmem 1
    rw [hbot, Subgroup.mem_bot] at this
    exact hτ this
  · intro s
    refine ⟨1, ?_⟩
    obtain ⟨y, hy⟩ := s.2
    apply Subtype.ext
    rw [pow_one, pow_two, Subgroup.coe_mul, Subgroup.coe_one, ← hy, ← map_mul]
    have : y * y = 1 := by
      have : y * y = Multiplicative.ofAdd (Multiplicative.toAdd y + Multiplicative.toAdd y) := rfl
      rw [this, ← two_mul, h2, zero_mul]
      rfl
    rw [this, map_one]
  · apply le_antisymm
    · obtain ⟨g, hgP, c, hc1, hc⟩ := hmove
      rintro _ ⟨y, rfl⟩
      set a := Multiplicative.toAdd y with ha
      have hy : y = Multiplicative.ofAdd a := rfl
      have hne : (1 - c) ≠ 0 := sub_ne_zero.2 (Ne.symm hc1)
      have hcomm : ⁅τ (Multiplicative.ofAdd ((1 - c)⁻¹ * a)), g⁆ = τ y := by
        rw [commutatorElement_def]
        have h1 := hconj g hgP c hc (-((1 - c)⁻¹ * a))
        have hinv : (τ (Multiplicative.ofAdd ((1 - c)⁻¹ * a)))⁻¹ =
            τ (Multiplicative.ofAdd (-((1 - c)⁻¹ * a))) := by
          rw [inv_eq_iff_mul_eq_one, ← map_mul]
          have : Multiplicative.ofAdd ((1 - c)⁻¹ * a) * Multiplicative.ofAdd (-((1 - c)⁻¹ * a)) = 1 := by
            rw [← ofAdd_add, add_neg_cancel]
            rfl
          rw [this, map_one]
        rw [hinv]
        calc τ (Multiplicative.ofAdd ((1 - c)⁻¹ * a)) * g *
              τ (Multiplicative.ofAdd (-((1 - c)⁻¹ * a))) * g⁻¹
            = τ (Multiplicative.ofAdd ((1 - c)⁻¹ * a)) *
                (g * τ (Multiplicative.ofAdd (-((1 - c)⁻¹ * a))) * g⁻¹) := by group
          _ = τ (Multiplicative.ofAdd ((1 - c)⁻¹ * a)) *
                τ (Multiplicative.ofAdd (c * -((1 - c)⁻¹ * a))) := by rw [h1]
          _ = τ (Multiplicative.ofAdd ((1 - c)⁻¹ * a + c * -((1 - c)⁻¹ * a))) := by
            rw [← map_mul τ, ← ofAdd_add]
          _ = τ y := by
            rw [hy]
            congr 2
            field_simp
            ring
      rw [← hcomm]
      exact Subgroup.commutator_mem_commutator (hmem _) hgP
    · exact Subgroup.le_normalizer_iff_commutator_le_left.1 (fun h hh => hnorm h hh)

end Scaling

section Transport

variable {G : Type} [Group G] {Γ : Type*} [Group Γ] {p : ℕ}

theorem psylowIn_of_transport {I : Subgroup G} (ψ : ↥I →* Γ) (hψ : Function.Injective ψ) {U : Type*}
    [Group U] (ρ : U →* Γ) {F : Subgroup U} {Q : Subgroup G}
    (hQ : ∀ x : G, x ∈ Q ↔ ∃ hx : x ∈ I, ψ ⟨x, hx⟩ ∈ F.map ρ) (hFB : F.map ρ ≤ ψ.range)
    (hρ : ∀ u ∈ F, ρ u = 1 → u = 1) (h : PSylowSub p F) : PSylowIn p Q := by
  let ρF : ↥F →* Γ := ρ.comp F.subtype
  have hρF : ∀ u : ↥F, ρF u ∈ ψ.range := fun u => hFB ⟨u, u.2, rfl⟩
  let θ : ↥F →* ↥ψ.range := ρF.codRestrict ψ.range hρF
  let ψe : ↥I ≃* ↥ψ.range := MonoidHom.ofInjective hψ
  let Θ : ↥F →* G := I.subtype.comp (ψe.symm.toMonoidHom.comp θ)
  have hθ : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : ρ (u : U) = 1 := congrArg Subtype.val hu
    exact Subtype.ext (hρ _ u.2 h1)
  have hΘ : Function.Injective Θ := Subtype.val_injective.comp (ψe.symm.injective.comp hθ)
  have hrange : (⊤ : Subgroup ↥F).map Θ = Q := by
    rw [← MonoidHom.range_eq_map]
    ext x
    rw [hQ x]
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨(ψe.symm (θ u)).2, ?_⟩
      have h1 : ψ (ψe.symm (θ u)) = ρ (u : U) := by
        have := congrArg Subtype.val (ψe.apply_symm_apply (θ u))
        exact this
      show ψ (ψe.symm (θ u)) ∈ F.map ρ
      rw [h1]
      exact ⟨u, u.2, rfl⟩
    · rintro ⟨hx, u, hu, hux⟩
      refine ⟨⟨u, hu⟩, ?_⟩
      have h1 : θ ⟨u, hu⟩ = ψe ⟨x, hx⟩ := Subtype.ext hux
      show ((ψe.symm (θ ⟨u, hu⟩) : ↥I) : G) = x
      rw [h1, ψe.symm_apply_apply]
  have hF : PSylowSub p (⊤ : Subgroup ↥F) := h.top_of
  have := hF.map Θ hΘ
  rw [hrange] at this
  exact this.toPSylowIn

end Transport

end CFSG.RankThree.PartOne.S15K

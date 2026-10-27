module

public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

open scoped commutatorElement

namespace CFSG.Quasithin

namespace QA19

theorem comm_mem_centralizer_of_central {L : Type*} [Group L] {A : Subgroup L}
    (hA : A ≤ Subgroup.center L) {z x y : L} (hx : x * z * x⁻¹ * z⁻¹ ∈ A)
    (hy : y * z * y⁻¹ * z⁻¹ ∈ A) :
    x * y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer ({z} : Set L) := by
  have conj_central : ∀ (g c w : L), (∀ h : L, h * c = c * h) →
      g * (c * w) * g⁻¹ = c * (g * w * g⁻¹) := fun g c w hc => by
    calc g * (c * w) * g⁻¹ = (g * c) * w * g⁻¹ := by group
      _ = (c * g) * w * g⁻¹ := by rw [hc g]
      _ = c * (g * w * g⁻¹) := by group
  have conj_central_inv : ∀ (g c w : L), (∀ h : L, h * c = c * h) →
      g⁻¹ * (c * w) * g = c * (g⁻¹ * w * g) := fun g c w hc => by
    have := conj_central g⁻¹ c w hc
    simpa using this
  set a := x * z * x⁻¹ * z⁻¹ with ha
  set b := y * z * y⁻¹ * z⁻¹ with hb
  have hac : ∀ g : L, g * a = a * g := fun g => Subgroup.mem_center_iff.mp (hA hx) g
  have hbc : ∀ g : L, g * b = b * g := fun g => Subgroup.mem_center_iff.mp (hA hy) g
  have hacinv : ∀ g : L, g * a⁻¹ = a⁻¹ * g := fun g => by
    have := hac g
    calc g * a⁻¹ = a⁻¹ * (a * g) * a⁻¹ := by group
      _ = a⁻¹ * (g * a) * a⁻¹ := by rw [this]
      _ = a⁻¹ * g := by group
  have hbcinv : ∀ g : L, g * b⁻¹ = b⁻¹ * g := fun g => by
    have := hbc g
    calc g * b⁻¹ = b⁻¹ * (b * g) * b⁻¹ := by group
      _ = b⁻¹ * (g * b) * b⁻¹ := by rw [this]
      _ = b⁻¹ * g := by group
  have hxz : x * z * x⁻¹ = a * z := by rw [ha]; group
  have hyz : y * z * y⁻¹ = b * z := by rw [hb]; group
  have hy' : y⁻¹ * z * y = b⁻¹ * z := by
    have h1 : y⁻¹ * (b * z) * y = b * (y⁻¹ * z * y) := conj_central_inv y b z hbc
    have h2 : y⁻¹ * (b * z) * y = z := by rw [← hyz]; group
    rw [h2] at h1
    exact eq_inv_mul_of_mul_eq h1.symm
  have hx' : x⁻¹ * z * x = a⁻¹ * z := by
    have h1 : x⁻¹ * (a * z) * x = a * (x⁻¹ * z * x) := conj_central_inv x a z hac
    have h2 : x⁻¹ * (a * z) * x = z := by rw [← hxz]; group
    rw [h2] at h1
    exact eq_inv_mul_of_mul_eq h1.symm
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hc : x * y * x⁻¹ * y⁻¹ * z * (x * y * x⁻¹ * y⁻¹)⁻¹ = z := by
    calc x * y * x⁻¹ * y⁻¹ * z * (x * y * x⁻¹ * y⁻¹)⁻¹
        = x * (y * (x⁻¹ * (y⁻¹ * z * y) * x) * y⁻¹) * x⁻¹ := by group
      _ = x * (y * (x⁻¹ * (b⁻¹ * z) * x) * y⁻¹) * x⁻¹ := by rw [hy']
      _ = x * (y * (b⁻¹ * (x⁻¹ * z * x)) * y⁻¹) * x⁻¹ := by
          rw [conj_central_inv x b⁻¹ z hbcinv]
      _ = x * (y * (b⁻¹ * (a⁻¹ * z)) * y⁻¹) * x⁻¹ := by rw [hx']
      _ = x * (b⁻¹ * (a⁻¹ * (y * z * y⁻¹))) * x⁻¹ := by
          rw [conj_central y b⁻¹ (a⁻¹ * z) hbcinv, conj_central y a⁻¹ z hacinv]
      _ = x * (b⁻¹ * (a⁻¹ * (b * z))) * x⁻¹ := by rw [hyz]
      _ = x * (a⁻¹ * z) * x⁻¹ := by
          have : b⁻¹ * (a⁻¹ * (b * z)) = a⁻¹ * z := by
            calc b⁻¹ * (a⁻¹ * (b * z)) = b⁻¹ * (a⁻¹ * b) * z := by group
              _ = b⁻¹ * (b * a⁻¹) * z := by rw [hbc a⁻¹]
              _ = a⁻¹ * z := by group
          rw [this]
      _ = a⁻¹ * (x * z * x⁻¹) := conj_central x a⁻¹ z hacinv
      _ = z := by rw [hxz]; group
  exact (mul_inv_eq_iff_eq_mul.mp hc)

theorem commutator_centralizer_le_map {L X : Type*} [Group L] [Group X] (π : L →* X)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center L) (z : L) :
    ⁅Subgroup.centralizer ({π z} : Set X), Subgroup.centralizer ({π z} : Set X)⁆ ≤
      (Subgroup.centralizer ({z} : Set L)).map π := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨x, rfl⟩ := hπ g₁
  obtain ⟨y, rfl⟩ := hπ g₂
  have hx : x * z * x⁻¹ * z⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    have := Subgroup.mem_centralizer_singleton_iff.mp hg₁
    rw [this]; group
  have hy : y * z * y⁻¹ * z⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    have := Subgroup.mem_centralizer_singleton_iff.mp hg₂
    rw [this]; group
  refine ⟨x * y * x⁻¹ * y⁻¹, comm_mem_centralizer_of_central hker hx hy, ?_⟩
  simp [commutatorElement_def]

theorem perfect_le_of_index_two {A : Type*} [Group A] {D : Subgroup A} (hD : D.index = 2)
    {U : Subgroup A} (hU : ⁅U, U⁆ = U) : U ≤ D := by
  have hn : D.Normal := Subgroup.normal_of_index_eq_two hD
  have hcard : Nat.card (A ⧸ D) = 2 := by rw [← Subgroup.index_eq_card, hD]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic (A ⧸ D) := isCyclic_of_prime_card hcard
  have hcomm : ∀ a b : A ⧸ D, a * b = b * a := fun a b => IsMulCommutative.is_comm.comm a b
  rw [← hU]
  refine Subgroup.commutator_le.mpr fun u₁ _ u₂ _ => ?_
  rw [← QuotientGroup.eq_one_iff]
  have : (QuotientGroup.mk' D) ⁅u₁, u₂⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm _ _)
  exact this

theorem card_dvd_of_perfect_normalized
    {L X : Type*} [Group L] [Group X] (π : L →* X) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center L) (z : L)
    (C : Subgroup X) (hC : C = Subgroup.centralizer ({π z} : Set X))
    (O : Subgroup ↥C) [O.Normal] (D : Subgroup (↥C ⧸ O))
    (hDperf : ⁅D, D⁆ = D) (hDidx : D.index = 2)
    {M : Type*} [Group M] [IsSimpleGroup M] (ψ : D →* M) (hψ : Function.Surjective ψ)
    (hψker : (Nat.card ψ.ker).Prime)
    (K : Subgroup L) (hKperf : ⁅K, K⁆ = K) (hKz : K ≤ Subgroup.centralizer ({z} : Set L))
    (hKnorm : ∀ q ∈ Subgroup.centralizer ({z} : Set L), ∀ k ∈ K, q * k * q⁻¹ ∈ K)
    (hKO : ∃ k ∈ K, π k ∉ O.map C.subtype) :
    Nat.card M ∣ Nat.card K := by
  classical
  set ρ : ↥C →* ↥C ⧸ O := QuotientGroup.mk' O with hρ
  have hρs : Function.Surjective ρ := QuotientGroup.mk'_surjective O
  set Kb : Subgroup X := K.map π with hKb
  have hKbC : Kb ≤ C := by
    rintro _ ⟨k, hk, rfl⟩
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp (hKz hk)
    rw [← map_mul, ← map_mul, this]
  set KC : Subgroup ↥C := Kb.subgroupOf C with hKC
  set U : Subgroup (↥C ⧸ O) := KC.map ρ with hU
  have hKbperf : ⁅Kb, Kb⁆ = Kb := by rw [hKb, ← Subgroup.map_commutator, hKperf]
  have hKCperf : ⁅KC, KC⁆ = KC := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, hKC, Subgroup.map_subgroupOf_eq_of_le hKbC, hKbperf]
  have hUperf : ⁅U, U⁆ = U := by rw [hU, ← Subgroup.map_commutator, hKCperf]
  have hUD : U ≤ D := perfect_le_of_index_two hDidx hUperf
  have hcomm : ⁅C, C⁆ ≤ (Subgroup.centralizer ({z} : Set L)).map π := by
    rw [hC]
    exact commutator_centralizer_le_map π hπ hker z
  set Bq : Subgroup ↥C := ((Subgroup.centralizer ({z} : Set L)).map π).subgroupOf C with hBq
  have hCC : ⁅(⊤ : Subgroup ↥C), ⊤⁆ ≤ Bq := by
    rw [hBq, Subgroup.subgroupOf, ← Subgroup.map_le_iff_le_comap, Subgroup.map_commutator,
      Subgroup.map_top, Subgroup.range_subtype]
    exact hcomm
  have hDle : D ≤ Bq.map ρ := by
    calc D = ⁅D, D⁆ := hDperf.symm
      _ ≤ ⁅(⊤ : Subgroup (↥C ⧸ O)), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = Subgroup.map ρ ⁅(⊤ : Subgroup ↥C), ⊤⁆ := by
          rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective ρ hρs]
      _ ≤ Bq.map ρ := Subgroup.map_mono hCC
  have hNorm : (U.subgroupOf D).Normal := by
    refine ⟨fun u hu d => ?_⟩
    obtain ⟨b, hb, hbd⟩ := hDle d.2
    have hu' : (u : ↥C ⧸ O) ∈ U := hu
    obtain ⟨c, hc, hcu⟩ := hu'
    have hbcb : b * c * b⁻¹ ∈ KC := by
      have hb' : (b : X) ∈ (Subgroup.centralizer ({z} : Set L)).map π := hb
      have hc' : (c : X) ∈ Kb := hc
      obtain ⟨q, hq, hqb⟩ := hb'
      obtain ⟨k, hk, hkc⟩ := hc'
      show ((b * c * b⁻¹ : ↥C) : X) ∈ Kb
      refine ⟨q * k * q⁻¹, hKnorm q hq k hk, ?_⟩
      simp [map_mul, map_inv, hqb, hkc]
    show ((d * u * d⁻¹ : ↥D) : ↥C ⧸ O) ∈ U
    have : ((d * u * d⁻¹ : ↥D) : ↥C ⧸ O) = ρ (b * c * b⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hbd, hcu]
    rw [this]
    exact Subgroup.mem_map_of_mem _ hbcb
  have hmapN : ((U.subgroupOf D).map ψ).Normal := Subgroup.Normal.map hNorm ψ hψ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((U.subgroupOf D).map ψ) with h0 | h1
  · exfalso
    have hle : U.subgroupOf D ≤ ψ.ker := (Subgroup.map_eq_bot_iff _).mp h0
    have : Fact (Nat.Prime (Nat.card ψ.ker)) := ⟨hψker⟩
    have hcyc : IsCyclic ψ.ker := isCyclic_of_prime_card rfl
    have hcomm' : ∀ a ∈ U.subgroupOf D, ∀ b ∈ U.subgroupOf D, a * b = b * a := by
      intro a ha b hb
      have := IsMulCommutative.is_comm.comm (⟨a, hle ha⟩ : ψ.ker) ⟨b, hle hb⟩
      exact congrArg Subtype.val this
    have hperf : ⁅U.subgroupOf D, U.subgroupOf D⁆ = U.subgroupOf D := by
      apply Subgroup.map_injective D.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hUD, hUperf]
    have hbot : U.subgroupOf D = ⊥ := by
      rw [eq_bot_iff]
      calc U.subgroupOf D = ⁅U.subgroupOf D, U.subgroupOf D⁆ := hperf.symm
        _ ≤ ⊥ := Subgroup.commutator_le.mpr fun a ha b hb => by
            rw [Subgroup.mem_bot]
            exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm' a ha b hb)
    have hUbot : U = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      have : (⟨u, hUD hu⟩ : ↥D) ∈ U.subgroupOf D := hu
      rw [hbot, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val this
    obtain ⟨k, hk, hkO⟩ := hKO
    apply hkO
    have hkb : π k ∈ Kb := Subgroup.mem_map_of_mem π hk
    have hkC : (⟨π k, hKbC hkb⟩ : ↥C) ∈ KC := hkb
    have : ρ ⟨π k, hKbC hkb⟩ ∈ U := Subgroup.mem_map_of_mem ρ hkC
    rw [hUbot, Subgroup.mem_bot] at this
    exact ⟨⟨π k, hKbC hkb⟩, (QuotientGroup.eq_one_iff _).mp this, rfl⟩
  · have h2 : Nat.card M ∣ Nat.card (U.subgroupOf D) := by
      have := Subgroup.card_map_dvd (H := U.subgroupOf D) ψ
      rwa [h1, Subgroup.card_top] at this
    have h3 : Nat.card (U.subgroupOf D) = Nat.card U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUD).toEquiv
    have h4 : Nat.card U ∣ Nat.card KC := Subgroup.card_map_dvd (H := KC) ρ
    have h5 : Nat.card KC = Nat.card Kb :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKbC).toEquiv
    have h6 : Nat.card Kb ∣ Nat.card K := Subgroup.card_map_dvd (H := K) π
    rw [h3] at h2
    rw [h5] at h4
    exact h2.trans (h4.trans h6)

end QA19

end CFSG.Quasithin

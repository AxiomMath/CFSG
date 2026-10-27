module

public import CFSG.Quasithin.Background.F7TwoInvSz
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.E2

open CFSG.GH74.Uniqueness.Bender
open scoped commutatorElement

private theorem three_le_card_of_mem {G : Type*} [Group G] {H : Subgroup G} [Finite H] {a b : G}
    (ha : a ∈ H) (hb : b ∈ H) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) : 3 ≤ Nat.card H := by
  classical
  have : Fintype H := Fintype.ofFinite H
  have h1 : (1 : H) ∉ ({⟨a, ha⟩, ⟨b, hb⟩} : Finset H) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => ha1 (congrArg Subtype.val h).symm, fun h => hb1 (congrArg Subtype.val h).symm⟩
  have h2 : (⟨a, ha⟩ : H) ∉ ({⟨b, hb⟩} : Finset H) := by
    simp only [Finset.mem_singleton]
    exact fun h => hab (congrArg Subtype.val h)
  have hs : ({1, ⟨a, ha⟩, ⟨b, hb⟩} : Finset H).card = 3 := by
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_singleton]
  rw [← hs, Nat.card_eq_fintype_card]
  exact Finset.card_le_univ _

private theorem eq_of_mem_of_card_eq_four {G : Type*} [Group G] {H H' : Subgroup G} [Finite H]
    (hle : H' ≤ H) (h4 : Nat.card H = 4) {a b : G} (ha : a ∈ H') (hb : b ∈ H') (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : a ≠ b) : H' = H := by
  have : Finite H' := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have h3 := three_le_card_of_mem ha hb ha1 hb1 hab
  have hdvd : Nat.card H' ∣ Nat.card H := Subgroup.card_dvd_of_le hle
  rw [h4] at hdvd
  have hle4 : Nat.card H' ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hc : Nat.card H' = 4 := by
    rcases (show Nat.card H' = 3 ∨ Nat.card H' = 4 by omega) with h | h
    · rw [h] at hdvd
      norm_num at hdvd
    · exact h
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [h4, hc])

variable {K P : Type} [Group K] [Group P] [Finite K] [Finite P]

theorem kgSz8_of_cover (hZ : Subgroup.center K ≠ ⊥)
    (hSz : IsSz 3 (K ⧸ Subgroup.center K)) (π : P →* K ⧸ Subgroup.center K) (φ : P →* K)
    (hφ : Function.Surjective φ) (hπφ : ∀ p, (φ p : K ⧸ Subgroup.center K) = π p)
    (h4 : Nat.card π.ker = 4) {x t₁ t₂ : P} (hx : x * x = 1) (hπx : π x ≠ 1)
    (ht₁ : π t₁ * π x = π x * π t₁) (ht₂ : π t₂ * π x = π x * π t₂) (hc₁ : ⁅t₁, x⁆ ≠ 1)
    (hc₂ : ⁅t₂, x⁆ ≠ 1) (hc : ⁅t₁, x⁆ ≠ ⁅t₂, x⁆) :
    (∀ y : K ⧸ Subgroup.center K, orderOf y = 2 →
      ∃ z : K, orderOf z = 2 ∧ (z : K ⧸ Subgroup.center K) = y) ∧
    ∀ S : Sylow 2 K,
      (Subgroup.center ↥(S : Subgroup K)).map (S : Subgroup K).subtype = Subgroup.center K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, -, hB⟩ := CFSG.Quasithin.F7Two.benderType_of_suzukiModel hSz
  have hπx2 : π x * π x = 1 := by rw [← map_mul, hx, map_one]
  have hconj : ∀ y : K ⧸ Subgroup.center K, y * y = 1 → y ≠ 1 →
      ∃ k : K, (k : K ⧸ Subgroup.center K) * π x * (k : K ⧸ Subgroup.center K)⁻¹ = y := by
    intro y hy hy1
    obtain ⟨g, hg⟩ := isConj_iff.mp (hB.lemma_3_4_a hπx2 hπx hy hy1)
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    exact ⟨k, hg⟩
  refine ⟨fun y hy => ?_, fun S => ?_⟩
  ·
    have hy2 : y * y = 1 := by rw [← sq, ← hy, pow_orderOf_eq_one]
    have hy1 : y ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hy
      exact absurd hy (by norm_num)
    obtain ⟨k, hk⟩ := hconj y hy2 hy1
    have hmk : ((k * φ x * k⁻¹ : K) : K ⧸ Subgroup.center K) = y := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hπφ, hk]
    refine ⟨k * φ x * k⁻¹, orderOf_eq_prime ?_ ?_, hmk⟩
    · rw [sq, show k * φ x * k⁻¹ * (k * φ x * k⁻¹) = k * (φ x * φ x) * k⁻¹ by group, ← map_mul,
        hx, map_one, mul_one, mul_inv_cancel]
    · intro h
      apply hy1
      rw [← hmk, h, QuotientGroup.mk_one]
  have hZker : ∀ p ∈ π.ker, φ p ∈ Subgroup.center K := fun p hp => by
    rw [← QuotientGroup.eq_one_iff, hπφ]
    exact hp
  have hZimg : ∀ z ∈ Subgroup.center K, ∃ p ∈ π.ker, φ p = z := fun z hz => by
    obtain ⟨p, rfl⟩ := hφ z
    refine ⟨p, ?_, rfl⟩
    rw [MonoidHom.mem_ker, ← hπφ]
    exact (QuotientGroup.eq_one_iff _).mpr hz
  have hZ2 : IsPGroup 2 (Subgroup.center K) := by
    intro z
    obtain ⟨p, hp, hpz⟩ := hZimg z z.2
    refine ⟨2, Subtype.ext ?_⟩
    have hp4 : (⟨p, hp⟩ : π.ker) ^ Nat.card π.ker = 1 := pow_card_eq_one'
    rw [h4] at hp4
    have hp4' : p ^ 4 = 1 := congrArg Subtype.val hp4
    rw [Subgroup.coe_pow, ← hpz, ← map_pow, show 2 ^ 2 = 4 from rfl, hp4', map_one,
      OneMemClass.coe_one]
  have hZS : Subgroup.center K ≤ (S : Subgroup K) := hZ2.le_sylow_of_normal S
  have hcore : ∀ s ∈ (S : Subgroup K), (∀ t ∈ (S : Subgroup K), t * s = s * t) →
      orderOf (s : K ⧸ Subgroup.center K) = 2 → False := by
    intro s hsS hsc hs2
    set y := (s : K ⧸ Subgroup.center K) with hydef
    have hy2 : y * y = 1 := by rw [← sq, ← hs2, pow_orderOf_eq_one]
    have hy1 : y ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hs2
      exact absurd hs2 (by norm_num)
    let Sb : Sylow 2 (K ⧸ Subgroup.center K) :=
      S.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center K))
    have hySb : y ∈ (Sb : Subgroup (K ⧸ Subgroup.center K)) := by
      rw [Sylow.coe_mapSurjective]
      exact ⟨s, hsS, rfl⟩
    obtain ⟨tB, hcB⟩ := hB.exists_benderCore Sb
    have hcent : Subgroup.centralizer {y} = (Sb : Subgroup (K ⧸ Subgroup.center K)) :=
      hcB.centralizer_eq_of_e_one (hcB.mem_rootCenter_of_mul_self hySb hy2) hy1
    obtain ⟨k, hk⟩ := hconj y hy2 hy1
    have hmemS : ∀ t : P, π t * π x = π x * π t → k * φ t * k⁻¹ ∈ (S : Subgroup K) := by
      intro t ht
      have hcen : ((k * φ t * k⁻¹ : K) : K ⧸ Subgroup.center K) ∈ Subgroup.centralizer {y} := by
        rw [Subgroup.mem_centralizer_singleton_iff, ← hk, QuotientGroup.mk_mul,
          QuotientGroup.mk_mul, QuotientGroup.mk_inv, hπφ]
        set kb := (k : K ⧸ Subgroup.center K)
        calc kb * π t * kb⁻¹ * (kb * π x * kb⁻¹) = kb * (π t * π x) * kb⁻¹ := by group
          _ = kb * (π x * π t) * kb⁻¹ := by rw [ht]
          _ = kb * π x * kb⁻¹ * (kb * π t * kb⁻¹) := by group
      rw [hcent, Sylow.coe_mapSurjective] at hcen
      obtain ⟨u, huS, hu⟩ := hcen
      have hz : u⁻¹ * (k * φ t * k⁻¹) ∈ Subgroup.center K := QuotientGroup.eq.mp hu
      have := mul_mem huS (hZS hz)
      rwa [mul_inv_cancel_left] at this
    have hkill : ∀ t : P, π t * π x = π x * π t → φ ⁅t, x⁆ = 1 := by
      intro t ht
      have h1 := hsc _ (hmemS t ht)
      have h2 : φ t * (k⁻¹ * s * k) = k⁻¹ * s * k * φ t := by
        calc φ t * (k⁻¹ * s * k) = k⁻¹ * (k * φ t * k⁻¹ * s) * k := by group
          _ = k⁻¹ * (s * (k * φ t * k⁻¹)) * k := by rw [h1]
          _ = k⁻¹ * s * k * φ t := by group
      have hz : (φ x)⁻¹ * (k⁻¹ * s * k) ∈ Subgroup.center K := by
        refine QuotientGroup.eq.mp ?_
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hπφ, ← hydef,
          ← hk]
        group
      have hzt := Subgroup.mem_center_iff.mp hz (φ t)
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      calc φ t * φ x = φ t * (k⁻¹ * s * k) * ((φ x)⁻¹ * (k⁻¹ * s * k))⁻¹ := by group
        _ = k⁻¹ * s * k * φ t * ((φ x)⁻¹ * (k⁻¹ * s * k))⁻¹ := by rw [h2]
        _ = φ x * (φ t * ((φ x)⁻¹ * (k⁻¹ * s * k))) * ((φ x)⁻¹ * (k⁻¹ * s * k))⁻¹ := by
          rw [hzt]; group
        _ = φ x * φ t := by group
    have hcπ : ∀ t : P, π t * π x = π x * π t → ⁅t, x⁆ ∈ π.ker := fun t ht => by
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact ht
    have hH : φ.ker ⊓ π.ker = π.ker :=
      eq_of_mem_of_card_eq_four inf_le_right h4 ⟨hkill t₁ ht₁, hcπ t₁ ht₁⟩
        ⟨hkill t₂ ht₂, hcπ t₂ ht₂⟩ hc₁ hc₂ hc
    apply hZ
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨p, hp, rfl⟩ := hZimg z hz
    rw [← hH] at hp
    exact hp.1
  apply le_antisymm
  · rintro _ ⟨s, hs, rfl⟩
    by_contra hsZ
    have hsc : ∀ t ∈ (S : Subgroup K), t * (s : K) = (s : K) * t := fun t ht =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hs ⟨t, ht⟩)
    set y := ((s : K) : K ⧸ Subgroup.center K) with hydef
    have hy1 : y ≠ 1 := fun h => hsZ ((QuotientGroup.eq_one_iff _).mp h)
    obtain ⟨k₀, hk₀⟩ := IsPGroup.iff_orderOf.mp S.isPGroup' s
    have hdvd : orderOf y ∣ 2 ^ k₀ := by
      rw [← hk₀, ← Subgroup.orderOf_coe]
      exact orderOf_map_dvd (QuotientGroup.mk' (Subgroup.center K)) (s : K)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hj
      exact hy1 hj
    have h2dvd : 2 ∣ orderOf y := by
      rw [hj]
      exact dvd_pow_self 2 hj0
    refine hcore ((s : K) ^ (orderOf y / 2)) (pow_mem s.2 _) (fun t ht => ?_) ?_
    · exact Commute.pow_right (hsc t ht) _
    · rw [QuotientGroup.mk_pow, ← hydef]
      exact orderOf_pow_orderOf_div (orderOf_pos y).ne' h2dvd
  · intro z hz
    exact ⟨⟨z, hZS hz⟩,
      Subgroup.mem_center_iff.mpr fun t => Subtype.ext (Subgroup.mem_center_iff.mp hz t), rfl⟩

end CFSG.Quasithin.E2

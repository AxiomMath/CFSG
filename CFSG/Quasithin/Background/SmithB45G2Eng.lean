module

public import CFSG.Quasithin.Background.SmithB45G2Out
public import CFSG.Quasithin.Background.SmithB42G2FOff
public import CFSG.Quasithin.Background.SmithB42G2FRank

public section

namespace CFSG.Quasithin.B45G2

open CFSG.QuasithinUnique.Setup.X7b CFSG.Quasithin.B42G2F
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Counting

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

theorem card_sq_mul_card_fixed_lt (A : Subgroup (M ≃ₗ[ZMod 2] M)) (t : M ≃ₗ[ZMod 2] M)
    (ht : t ∈ A) (hA : Nat.card A ^ 2 < 2 ^ dispRank t) :
    Nat.card A ^ 2 * Nat.card {m : M // ∀ a ∈ A, a m = m} < Nat.card M := by
  have : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  set D : M →ₗ[ZMod 2] M := t.toLinearMap - 1 with hD
  have h1 : Nat.card M = 2 ^ Module.finrank (ZMod 2) M := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h2 : Nat.card (LinearMap.ker D) = 2 ^ Module.finrank (ZMod 2) (LinearMap.ker D) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h3 := LinearMap.finrank_range_add_finrank_ker D
  have hC : Nat.card {m : M // ∀ a ∈ A, a m = m} ≤ Nat.card (LinearMap.ker D) := by
    refine Nat.card_le_card_of_injective (fun m => ⟨m.1, ?_⟩) ?_
    · show t m.1 - m.1 = 0
      rw [m.2 t ht, sub_self]
    · intro a b h
      exact Subtype.ext (congrArg (fun x => x.1) h)
  have hpos : 0 < Nat.card (LinearMap.ker D) := Nat.card_pos
  calc Nat.card A ^ 2 * Nat.card {m : M // ∀ a ∈ A, a m = m}
      ≤ Nat.card A ^ 2 * Nat.card (LinearMap.ker D) := Nat.mul_le_mul_left _ hC
    _ < 2 ^ dispRank t * Nat.card (LinearMap.ker D) := Nat.mul_lt_mul_of_pos_right hA hpos
    _ = Nat.card M := by rw [h1, h2, ← pow_add, dispRank, h3]

end Counting

section G2

open CFSG.Open CFSG.Quasithin.Explicit CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Quasithin.SmithCurtis.Chev CFSG.ComponentClassification.UnbalancedCatalog

variable {K : Type} [Field K] [Fintype K] [CharP K 2]
variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

theorem g2_card_sq_mul_card_fixed_lt {f : ℕ} (hK : Fintype.card K = 2 ^ f) (hf : 2 ≤ f)
    (π : ↥(cayleyGroup K) →* (M ≃ₗ[ZMod 2] M)) (hπ : Function.Injective π)
    (hntM : Nontrivial M)
    (hirr : ∀ U : Submodule (ZMod 2) M, (∀ g, ∀ u ∈ U, π g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hdisp : ∀ z : ↥(cayleyGroup K), z * z = 1 → z ≠ 1 → 5 * f ≤ dispRank (π z))
    (hinner : ∀ Γ : Subgroup ↥(cayleyGroup K), Γ ≠ ⊥ → (∀ γ ∈ Γ, γ * γ = 1) →
      (∀ γ ∈ Γ, ∀ δ ∈ Γ, γ * δ = δ * γ) →
      Nat.card Γ ^ 2 * Nat.card {m : M // ∀ γ ∈ Γ, π γ m = m} < Nat.card M)
    (A : Subgroup (M ≃ₗ[ZMod 2] M)) (hnorm : ∀ a ∈ A, ∀ x, ∃ y, a * π x * a⁻¹ = π y)
    (hAe : CFSG.IsElementaryAbelian 2 A) (hA1 : A ≠ ⊥) :
    Nat.card A ^ 2 * Nat.card {m : M // ∀ a ∈ A, a m = m} < Nat.card M := by
  classical
  have : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  have hKn : Nat.card K = 2 ^ f := by rw [Nat.card_eq_fintype_card, hK]
  have := hAe
  have hsq : ∀ a ∈ A, a * a = 1 := fun a ha => by
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a ha
    rwa [_root_.sq] at this
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := A)).comm ⟨a, ha⟩ ⟨b, hb⟩)
  by_cases hin : ∀ a ∈ A, ∃ g, π g = a
  · set Γ := A.comap π with hΓ
    have hmap : Γ.map π = A := by
      refine le_antisymm (Subgroup.map_comap_le _ _) fun a ha => ?_
      obtain ⟨g, rfl⟩ := hin a ha
      exact ⟨g, ha, rfl⟩
    have hcardΓ : Nat.card Γ = Nat.card A := by
      rw [← Subgroup.card_map_of_injective hπ, hmap]
    have hΓ1 : ∀ γ ∈ Γ, γ * γ = 1 := fun γ hγ =>
      hπ (by rw [map_mul, map_one]; exact hsq _ hγ)
    have hΓc : ∀ γ ∈ Γ, ∀ δ ∈ Γ, γ * δ = δ * γ := fun γ hγ δ hδ =>
      hπ (by rw [map_mul, map_mul]; exact hcomm _ hγ _ hδ)
    have hΓne : Γ ≠ ⊥ := by
      intro h0
      apply hA1
      rw [← hmap, h0, Subgroup.map_bot]
    have hfix : Nat.card {m : M // ∀ a ∈ A, a m = m} =
        Nat.card {m : M // ∀ γ ∈ Γ, π γ m = m} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun m => ?_)
      constructor
      · intro h γ hγ
        exact h _ hγ
      · intro h a ha
        obtain ⟨g, rfl⟩ := hin a ha
        exact h g ha
    rw [← hcardΓ, hfix]
    exact hinner Γ hΓne hΓ1 hΓc
  push Not at hin
  obtain ⟨a, ha, hout⟩ := hin
  obtain ⟨ψ, -, hsurj, hker⟩ := CFSG.Quasithin.B42G2Id.exists_adjointGroup_hom_cayleyGroup hKn hf
  have hZC : Subgroup.center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  have hinjψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, hZC]
  set πC := π.comp ψ with hπCdef
  have hπC : Function.Injective πC := hπ.comp hinjψ
  have hnormC : ∀ a ∈ A, ∀ x, ∃ y, a * πC x * a⁻¹ = πC y := fun a ha x => by
    obtain ⟨y, hy⟩ := hnorm a ha (ψ x)
    obtain ⟨y', rfl⟩ := hsurj y
    exact ⟨y', hy⟩
  have hirrC : ∀ U : Submodule (ZMod 2) M, (∀ g, ∀ u ∈ U, πC g u ∈ U) → U = ⊥ ∨ U = ⊤ :=
    fun U hU => hirr U fun g u hu => by
      obtain ⟨g', rfl⟩ := hsurj g
      exact hU g' u hu
  obtain ⟨-, Θ, -, -, hΘker, hΘinv⟩ := even_G2_exact_automorphism_normal_form hf K hKn
  have hΘker' : Θ.ker = inner (adjointGroup .G2 K) := hΘker
  have hinv : ∀ x y : K ≃+* K, x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 → x = y := by
    intro x y hx hy hx1 hy1
    have h1 : ∀ k, x (x k) = k := fun k => congrArg (fun σ : K ≃+* K => σ k) hx
    have h2 : ∀ k, y (y k) = k := fun k => congrArg (fun σ : K ≃+* K => σ k) hy
    have h1' : ∃ k, x k ≠ k := by
      by_contra h
      push Not at h
      exact hx1 (RingEquiv.ext h)
    have h2' : ∃ k, y k ≠ k := by
      by_contra h
      push Not at h
      exact hy1 (RingEquiv.ext h)
    exact CFSG.Quasithin.B42G2.ringEquiv_involution_unique hKn hf h1 h2 h1' h2'
  have hcard := card_le_two_mul hπC hnormC hZC hntM hirrC hsq Θ hΘker' hinv
  have hinner' : ∀ z : adjointGroup .G2 K, z * z = 1 → z ≠ 1 → 5 * f ≤ dispRank (πC z) :=
    fun z hz hz1 => hdisp (ψ z) (by rw [← map_mul, hz, map_one])
      (fun h => hz1 (hinjψ (h.trans (map_one ψ).symm)))
  have hout' : ¬ ∃ g, πC g = a := by
    rintro ⟨g, hg⟩
    exact hout (ψ g) hg
  set α := normAut πC hπC A hnormC ⟨a, ha⟩ with hαdef
  have hαinner : α ∉ inner (adjointGroup .G2 K) := fun h =>
    hout' (mem_range_of_normAut_mem_inner hπC hnormC hZC hntM hirrC hsq ⟨a, ha⟩ h)
  have hαα : α ^ 2 = 1 := by
    rw [hαdef, ← map_pow]
    have : (⟨a, ha⟩ : A) ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one, _root_.sq]
      exact hsq a ha)
    rw [this, map_one]
  have hα1 : α ≠ 1 := fun h => hαinner (h ▸ Subgroup.one_mem _)
  have hord : orderOf α = 2 := orderOf_eq_prime hαα hα1
  set Γ := A.comap πC with hΓ
  have hΓfix : ∀ g ∈ Γ, α g = g := by
    intro g hg
    apply hπC
    rw [hαdef, π_normAut]
    change a * πC g * a⁻¹ = πC g
    rw [hcomm a ha _ hg, mul_inv_cancel_right]
  have hΓ1 : ∀ g ∈ Γ, g * g = 1 := fun g hg =>
    hπC (by rw [map_mul, map_one]; exact hsq _ hg)
  have hΓc : ∀ g ∈ Γ, ∀ h ∈ Γ, g * h = h * g := fun g hg h hh =>
    hπC (by rw [map_mul, map_mul]; exact hcomm _ hg _ hh)
  have hΓsq := card_sq_le_of_outer_fixed hf hKn α hord hαinner hΓfix hΓ1 hΓc
  have hpowle : ∀ {m n : ℕ}, m ≤ n → 2 ^ m ≤ 2 ^ n := fun h =>
    Nat.pow_le_pow_right (by norm_num) h
  by_cases hΓbot : Γ = ⊥
  ·
    have h1 : Nat.card Γ = 1 := by rw [hΓbot, Subgroup.card_bot]
    have hA2 : Nat.card A ≤ 2 := by rw [h1] at hcard; omega
    have hΘα : Θ α ≠ 1 := fun h => hαinner (by
      rw [← hΘker']
      exact MonoidHom.mem_ker.mpr h)
    obtain ⟨c₀, hc₀⟩ : ∃ c, Θ α c ≠ c := by
      by_contra h
      push Not at h
      exact hΘα (RingEquiv.ext h)
    have hδ : ∀ c, Θ α c = c ^ 2 ^ (f / 2) := by
      rcases hΘinv α hαα with h | ⟨-, h, -⟩
      · exact absurd h hΘα
      · exact h
    rcases even_G2_involution_inner_or_canonical_field hf K hKn α hord with h | ⟨-, hcan⟩
    · exact absurd h hαinner
    obtain ⟨β, ψ', hβ, hψ', -⟩ := hcan (Θ α).toRingHom hδ
    obtain ⟨g, hgg, hg1⟩ := exists_involution_of_entrywise α β ψ' (Θ α).toRingHom hβ hψ' hc₀
    have h1' := hinner' _ hgg hg1
    have h2 : πC (α g * g⁻¹) = a * (πC g * a⁻¹ * (πC g)⁻¹) := by
      rw [map_mul, map_inv, hαdef, π_normAut]
      group
    rw [h2] at h1'
    have h3 := dispRank_mul_le a (πC g * a⁻¹ * (πC g)⁻¹)
    rw [dispRank_conj, dispRank_inv_of_mul_self (hsq a ha)] at h3
    refine card_sq_mul_card_fixed_lt A a ha ?_
    calc Nat.card A ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left hA2 2
      _ < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ dispRank a := hpowle (by omega)
  · obtain ⟨⟨z, hzΓ⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hΓbot
    have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
    have h2 := hinner' z (hΓ1 z hzΓ) hz1'
    refine card_sq_mul_card_fixed_lt A (πC z) hzΓ ?_
    calc Nat.card A ^ 2 ≤ (2 * Nat.card Γ) ^ 2 := Nat.pow_le_pow_left hcard 2
      _ = 4 * Nat.card Γ ^ 2 := by ring
      _ ≤ 4 * 2 ^ (3 * f) := Nat.mul_le_mul_left _ hΓsq
      _ = 2 ^ (3 * f + 2) := by rw [pow_add]; ring
      _ < 2 ^ (5 * f) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      _ ≤ 2 ^ dispRank (πC z) := hpowle h2

end G2

end CFSG.Quasithin.B45G2

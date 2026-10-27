module

public import CFSG.Quasithin.Background.SmithB45G2Eng
public import CFSG.Quasithin.Background.SmithB45G2Quad
public import CFSG.Quasithin.Background.SmithB45G2Dich
public import CFSG.Quasithin.Background.SmithB42G2FMain

public section

namespace CFSG.Quasithin.B45G2

open CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.B42G2Ten
  CFSG.Quasithin.B42G2F
open CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.X7b

section Counting

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

omit [Finite M] in
theorem neg_eq_self_zmod2 (v : M) : -v = v := by
  have h : (2 : ZMod 2) • v = 0 := by rw [show (2 : ZMod 2) = 0 from rfl, zero_smul]
  rw [two_smul] at h
  exact neg_eq_of_add_eq_zero_right h

theorem card_eq_two_pow_mul_ker (t : M ≃ₗ[ZMod 2] M) :
    Nat.card M = 2 ^ dispRank t * Nat.card (LinearMap.ker (t.toLinearMap - 1)) := by
  have : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  have h1 : Nat.card M = 2 ^ Module.finrank (ZMod 2) M := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h2 : Nat.card (LinearMap.ker (t.toLinearMap - 1)) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.ker (t.toLinearMap - 1)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [h1, h2, ← pow_add, dispRank, LinearMap.finrank_range_add_finrank_ker]

theorem card_sq_mul_card_fixedG_lt {G : Type} [Group G] (π : G →* (M ≃ₗ[ZMod 2] M))
    (hπ : Function.Injective π) (Γ : Subgroup G) {z : G} (hz : z ∈ Γ)
    (h : Nat.card Γ ^ 2 < 2 ^ dispRank (π z)) :
    Nat.card Γ ^ 2 * Nat.card {m : M // ∀ γ ∈ Γ, π γ m = m} < Nat.card M := by
  have hc : Nat.card (Γ.map π) = Nat.card Γ := Subgroup.card_map_of_injective hπ
  have hfix : Nat.card {m : M // ∀ a ∈ Γ.map π, a m = m} =
      Nat.card {m : M // ∀ γ ∈ Γ, π γ m = m} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun m => ⟨fun h γ hγ => h _ ⟨γ, hγ, rfl⟩,
      fun h a ha => by obtain ⟨γ, hγ, rfl⟩ := ha; exact h γ hγ⟩)
  have := card_sq_mul_card_fixed_lt (Γ.map π) (π z) ⟨z, hz, rfl⟩ (by rw [hc]; exact h)
  rwa [hc, hfix] at this

theorem fixed_eq_of_card_le {G : Type} [Group G] (π : G →* (M ≃ₗ[ZMod 2] M)) (Γ : Subgroup G)
    {e : ℕ} (hcard : Nat.card M ≤ 2 ^ e * Nat.card {m : M // ∀ γ ∈ Γ, π γ m = m})
    {z : G} (hz : z ∈ Γ) (hdz : e ≤ dispRank (π z)) {m : M} (hm : π z m = m) :
    ∀ γ ∈ Γ, π γ m = m := by
  classical
  set C := {m : M // ∀ γ ∈ Γ, π γ m = m}
  set Kz := LinearMap.ker ((π z).toLinearMap - 1)
  have hinc : Function.Injective (fun c : C => (⟨c.1, by
      show (π z) c.1 - c.1 = 0
      rw [c.2 z hz, sub_self]⟩ : Kz)) := fun a b h =>
    Subtype.ext (congrArg (fun k : Kz => (k : M)) h)
  have h1 := card_eq_two_pow_mul_ker (π z)
  have hge : Nat.card Kz ≤ Nat.card C := by
    have h2 : 2 ^ e * Nat.card Kz ≤ 2 ^ e * Nat.card C := by
      calc 2 ^ e * Nat.card Kz ≤ 2 ^ dispRank (π z) * Nat.card Kz :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hdz)
        _ = Nat.card M := h1.symm
        _ ≤ 2 ^ e * Nat.card C := hcard
    exact Nat.le_of_mul_le_mul_left h2 (by positivity)
  have hbij : Function.Bijective (fun c : C => (⟨c.1, by
      show (π z) c.1 - c.1 = 0
      rw [c.2 z hz, sub_self]⟩ : Kz)) :=
    (Function.Injective.bijective_of_nat_card_le hinc hge)
  obtain ⟨c, hc⟩ := hbij.2 ⟨m, by show (π z) m - m = 0; rw [hm, sub_self]⟩
  have : c.1 = m := congrArg Subtype.val hc
  rw [← this]
  exact c.2

end Counting

section Main

variable {K : Type} [Field K] [Fintype K] [CharP K 2]
variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

theorem lie_inner_lt {f : ℕ} (hK : Fintype.card K = 2 ^ f) (hf : 1 ≤ f)
    (π : ↥(cayleyGroup K) →* (M ≃ₗ[ZMod 2] M)) (hπ : Function.Injective π)
    (hdisp : ∀ z : ↥(cayleyGroup K), z * z = 1 → z ≠ 1 → 6 * f ≤ dispRank (π z))
    (hquad : ∀ x y : ↥(cayleyGroup K),
      ((π x).toLinearMap - 1) * ((π y).toLinearMap - 1) = 0 →
        (repLie x - 1) * (repLie y - 1) = 0)
    (Γ : Subgroup ↥(cayleyGroup K)) (hΓne : Γ ≠ ⊥) (hΓ1 : ∀ γ ∈ Γ, γ * γ = 1)
    (hΓc : ∀ γ ∈ Γ, ∀ δ ∈ Γ, γ * δ = δ * γ) :
    Nat.card Γ ^ 2 * Nat.card {m : M // ∀ γ ∈ Γ, π γ m = m} < Nat.card M := by
  classical
  have hKn : Nat.card K = 2 ^ f := by rw [Nat.card_eq_fintype_card, hK]
  have hcube := CFSG.Quasithin.B42G2.card_le_cube hKn hf hΓ1 hΓc
  rw [hKn, ← pow_mul] at hcube
  obtain ⟨⟨z, hzΓ⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hΓne
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hdz := hdisp z (hΓ1 z hzΓ) hz1'
  rcases lt_or_eq_of_le hcube with hlt | heq
  · refine card_sq_mul_card_fixedG_lt π hπ Γ hzΓ ?_
    calc Nat.card Γ ^ 2 < (2 ^ (f * 3)) ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
      _ = 2 ^ (6 * f) := by rw [← pow_mul]; ring_nf
      _ ≤ 2 ^ dispRank (π z) := Nat.pow_le_pow_right (by norm_num) hdz
  · by_contra hge
    push Not at hge
    rw [heq, ← pow_mul, show f * 3 * 2 = 6 * f by ring] at hge
    have hq : ∀ γ ∈ Γ, ∀ δ ∈ Γ,
        ((π γ).toLinearMap - 1) * ((π δ).toLinearMap - 1) = 0 := by
      intro γ hγ δ hδ
      refine LinearMap.ext fun m => ?_
      change (π γ) ((π δ) m - m) - ((π δ) m - m) = 0
      by_cases hδ1 : δ = 1
      · rw [hδ1, map_one]
        simp
      have hu : π δ ((π δ) m - m) = (π δ) m - m := by
        have h2 : π δ (π δ m) = m := by
          rw [← LinearEquiv.mul_apply, ← map_mul, hΓ1 δ hδ, map_one]
          rfl
        rw [map_sub, h2, sub_eq_add_neg, sub_eq_add_neg, neg_eq_self_zmod2, neg_eq_self_zmod2,
          add_comm]
      have := fixed_eq_of_card_le π Γ hge hδ (hdisp δ (hΓ1 δ hδ) hδ1) hu γ hγ
      rw [this, sub_self]
    have hcard : Nat.card K ^ 3 ≤ Nat.card Γ := by rw [hKn, heq, ← pow_mul, mul_comm]
    obtain ⟨x, hx, y, hy, hne⟩ := exists_not_quadratic_repLie hKn hf hΓ1 hΓc hcard
    exact hne (hquad x y (hq x hx y hy))

theorem exists_natural_of_twoF {f : ℕ} (hK : Fintype.card K = 2 ^ f) (hf : 2 ≤ f)
    (π : ↥(cayleyGroup K) →* (M ≃ₗ[ZMod 2] M)) (hπ : Function.Injective π) (hnt : Nontrivial M)
    (hirr : ∀ U : Submodule (ZMod 2) M, (∀ g, ∀ u ∈ U, π g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (A : Subgroup (M ≃ₗ[ZMod 2] M)) (hnorm : ∀ a ∈ A, ∀ x, ∃ y, a * π x * a⁻¹ = π y)
    (hAe : CFSG.IsElementaryAbelian 2 A) (hA1 : A ≠ ⊥)
    (hoff : Nat.card M ≤ Nat.card A ^ 2 * Nat.card {m : M // ∀ a ∈ A, a m = m}) :
    ∃ φ : M ≃+ (Ix3 → K), ∀ g w, φ (π g w) = g2Act g (φ w) := by
  classical
  have hKn : Nat.card K = 2 ^ f := by rw [Nat.card_eq_fintype_card, hK]
  let ρ : Representation (ZMod 2) ↥(cayleyGroup K) M :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := M)).comp π
  have : Fact ρ.IsIrreducible :=
    ⟨(CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mpr ⟨hnt, hirr⟩⟩
  have hρnt : ∃ g, ρ g ≠ 1 := by
    refine ⟨CFSG.Quasithin.Vol2.Ch11.G2Q8.tL (1 : K), fun h => tL_one_ne_one (hπ ?_)⟩
    rw [map_one]
    exact LinearEquiv.toLinearMap_injective (h.trans rfl)
  have hρ : ∀ g, ρ g = (π g).toLinearMap := fun g => rfl
  have hcontra : ∀ (hinner : ∀ Γ : Subgroup ↥(cayleyGroup K), Γ ≠ ⊥ → (∀ γ ∈ Γ, γ * γ = 1) →
      (∀ γ ∈ Γ, ∀ δ ∈ Γ, γ * δ = δ * γ) →
      Nat.card Γ ^ 2 * Nat.card {m : M // ∀ γ ∈ Γ, π γ m = m} < Nat.card M)
      (hdisp : ∀ z : ↥(cayleyGroup K), z * z = 1 → z ≠ 1 → 5 * f ≤ dispRank (π z)), False :=
    fun hinner hdisp => absurd hoff (not_le.mpr
      (g2_card_sq_mul_card_fixed_lt hK hf π hπ hnt hirr hdisp hinner A hnorm hAe hA1))
  rcases natural_or_large_or_lie (ρ := ρ) hK (by omega) hρnt with ⟨φ, hφ⟩ | hbig | ⟨hdisp, hq⟩
  · exact ⟨φ, fun g w => hφ g w⟩
  · exfalso
    refine hcontra (fun Γ hΓne hΓ1 hΓc => ?_) (fun z hz hz1 => le_trans (by omega) (hbig z hz hz1))
    obtain ⟨⟨z, hzΓ⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hΓne
    have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
    refine card_sq_mul_card_fixedG_lt π hπ Γ hzΓ ?_
    have hcube := CFSG.Quasithin.B42G2.card_le_cube hKn (by omega) hΓ1 hΓc
    rw [hKn, ← pow_mul] at hcube
    calc Nat.card Γ ^ 2 ≤ (2 ^ (f * 3)) ^ 2 := Nat.pow_le_pow_left hcube 2
      _ = 2 ^ (6 * f) := by rw [← pow_mul]; ring_nf
      _ < 2 ^ (6 * f + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      _ ≤ 2 ^ dispRank (π z) := Nat.pow_le_pow_right (by norm_num) (hbig z (hΓ1 z hzΓ) hz1')
  · exfalso
    refine hcontra (fun Γ hΓne hΓ1 hΓc => lie_inner_lt hK (by omega) π hπ hdisp
      (fun x y h => hq x y (by rw [hρ, hρ]; exact h)) Γ hΓne hΓ1 hΓc)
      (fun z hz hz1 => le_trans (by omega) (hdisp z hz hz1))

end Main

end CFSG.Quasithin.B45G2

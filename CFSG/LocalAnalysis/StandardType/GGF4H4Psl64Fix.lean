module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

public section

namespace CFSG.StandardType

private lemma ggF4H4Psl64_res13 (d : Fin 7) (h : 4 ^ (d : ℕ) ≡ 1 [MOD 13]) :
    (d : ℕ) = 0 ∨ (d : ℕ) = 6 := by
  revert d h
  decide +kernel

private lemma ggF4H4Psl64_res17 (d : Fin 7) (h : 4 ^ 6 ≡ 4 ^ (d : ℕ) [MOD 17]) :
    (d : ℕ) = 2 ∨ (d : ℕ) = 6 := by
  revert d h
  decide +kernel

private lemma ggF4H4Psl64_coe_pow_eq_one {F V : Type*} [Field F] [AddCommMonoid V] [Module F V]
    (g : V ≃ₗ[F] V) {n : ℕ} (hg : g ^ n = 1) : (g : V →ₗ[F] V) ^ n = 1 := by
  have h := map_pow
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := F) (M := V)) g n
  rw [hg] at h
  show (g : V →ₗ[F] V) ^ n = LinearMap.id
  exact h.symm

private lemma ggF4H4Psl64_card_modEq_lm {F W : Type*} [Field F] [Finite F]
    [AddCommGroup W] [Module F W] [Module.Finite F W] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (f : Module.End F W) (hf : f ^ ℓ = 1) :
    Nat.card F ^ Module.finrank F W ≡
      Nat.card F ^ Module.finrank F (LinearMap.ker (f - 1)) [MOD ℓ] := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  letI : Fintype F := Fintype.ofFinite F
  haveI : Finite W := Module.finite_of_finite F
  letI : Fintype W := Fintype.ofFinite W
  let φ : Function.End W := (f : W → W)
  have hf' : φ ^ ℓ = 1 := by
    funext w
    change (⇑f)^[ℓ] w = id w
    rw [← Module.End.coe_pow, hf]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := W) (f := φ)
    (p := ℓ) (n := 1) (by simpa using hf')
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hmod
  have hfix : Nat.card φ.fixedPoints =
      Nat.card (LinearMap.ker (f - 1)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun w => by
      rw [Function.mem_fixedPoints_iff, LinearMap.mem_ker, LinearMap.sub_apply]
      change f w = w ↔ f w - w = 0
      rw [sub_eq_zero])
  rw [hfix] at hmod
  rw [← Module.natCard_eq_pow_finrank (K := F) (V := W),
    ← Module.natCard_eq_pow_finrank (K := F) (V := LinearMap.ker (f - 1))]
  exact hmod

theorem ggF4H4Psl64_card_modEq {F W : Type*} [Field F] [Finite F] [AddCommGroup W] [Module F W]
    [Module.Finite F W] {ℓ : ℕ} (hℓ : ℓ.Prime) (g : W ≃ₗ[F] W) (hg : g ^ ℓ = 1) :
    Nat.card F ^ Module.finrank F W ≡
      Nat.card F ^ Module.finrank F (LinearMap.ker ((g : W →ₗ[F] W) - 1)) [MOD ℓ] :=
  ggF4H4Psl64_card_modEq_lm (F := F) (W := W) hℓ (g : W →ₗ[F] W)
    (ggF4H4Psl64_coe_pow_eq_one g hg)

theorem ggF4H4Psl64_invariant_bot_or_top {F V : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    [AddCommGroup V] [Module F V] [Module.Finite F V] (hV : Module.finrank F V = 6)
    (a : V ≃ₗ[F] V) (ha : a ^ 13 = 1) (ha1 : a ≠ 1) (U : Submodule F V)
    (hU : ∀ u ∈ U, a u ∈ U) : U = ⊥ ∨ U = ⊤ := by
  classical
  set K : Submodule F V := LinearMap.ker ((a : V →ₗ[F] V) - 1) with hK
  have ha_lm : (a : V →ₗ[F] V) ^ 13 = 1 := ggF4H4Psl64_coe_pow_eq_one a ha
  have hmod : 4 ^ 6 ≡ 4 ^ Module.finrank F K [MOD 13] := by
    have h := ggF4H4Psl64_card_modEq (F := F) (W := V) (ℓ := 13) (by decide +kernel) a ha
    rw [hF, hV] at h
    simpa [hK] using h
  have he : Module.finrank F K = 0 ∨ Module.finrank F K = 6 := by
    have hle : Module.finrank F K ≤ 6 := by
      have h := Submodule.finrank_le K
      rwa [hV] at h
    have hmod' : 4 ^ ((⟨Module.finrank F K, by omega⟩ : Fin 7) : ℕ) ≡ 1 [MOD 13] :=
      hmod.symm.trans (by decide +kernel : 4 ^ 6 ≡ 1 [MOD 13])
    rcases ggF4H4Psl64_res13 ⟨Module.finrank F K, by omega⟩ hmod' with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hKbot : K = ⊥ := by
    rcases he with h0 | h6
    · exact Submodule.finrank_eq_zero.1 h0
    · exfalso
      have htop : K = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h6, hV])
      have ha1' : a = 1 := by
        ext v
        have hv : v ∈ K := by rw [htop]; exact Submodule.mem_top
        have h : (a : V →ₗ[F] V) v - v = 0 := hv
        exact sub_eq_zero.1 h
      exact ha1 ha1'
  let aU : U →ₗ[F] U := (a : V →ₗ[F] V).restrict hU
  have haU : aU ^ 13 = 1 := by
    ext x
    rw [Module.End.coe_pow]
    have hsem : Function.Semiconj (Subtype.val : U → V) aU (a : V → V) := fun x => rfl
    rw [hsem.iterate_right 13 x]
    rw [← LinearEquiv.coe_pow, ha]
    rfl
  have hkerU : LinearMap.ker (aU - 1) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx_eq : aU x = x := by
      have h : aU x - x = 0 := hx
      exact sub_eq_zero.1 h
    have hxV : (x : V) ∈ K := by
      rw [hK, LinearMap.mem_ker]
      change (a : V →ₗ[F] V) (x : V) - (x : V) = 0
      have h1 : ((aU x : U) : V) = (a : V →ₗ[F] V) (x : V) := by
        change ((((a : V →ₗ[F] V).restrict hU) x : U) : V) =
          (a : V →ₗ[F] V) (x : V)
        simp
      rw [← h1, hx_eq, sub_self]
    rw [hKbot] at hxV
    exact Subtype.ext (by simpa using hxV)
  have hmodU : 4 ^ Module.finrank F U ≡ 4 ^ 0 [MOD 13] := by
    have h := ggF4H4Psl64_card_modEq_lm (F := F) (W := U) (ℓ := 13)
      (by decide +kernel) aU haU
    rw [hF, hkerU, finrank_bot] at h
    simpa using h
  have hd : Module.finrank F U < 7 := by
    have h := Submodule.finrank_le U
    rw [hV] at h
    omega
  have hmodU' : 4 ^ ((⟨Module.finrank F U, hd⟩ : Fin 7) : ℕ) ≡ 1 [MOD 13] := by
    simpa using hmodU
  rcases ggF4H4Psl64_res13 ⟨Module.finrank F U, hd⟩ hmodU' with h0 | h6
  · exact Or.inl (Submodule.finrank_eq_zero.1 h0)
  · have h6' : Module.finrank F U = 6 := h6
    exact Or.inr (Submodule.eq_top_of_finrank_eq (by rw [h6', hV]))

theorem ggF4H4Psl64_fixed_finrank_two {F V : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    [AddCommGroup V] [Module F V] [Module.Finite F V] (hV : Module.finrank F V = 6)
    (b : V ≃ₗ[F] V) (hb : b ^ 17 = 1) (hb1 : b ≠ 1) :
    Module.finrank F (LinearMap.ker ((b : V →ₗ[F] V) - 1)) = 2 := by
  classical
  set K : Submodule F V := LinearMap.ker ((b : V →ₗ[F] V) - 1) with hK
  have hmod : 4 ^ 6 ≡ 4 ^ Module.finrank F K [MOD 17] := by
    have h := ggF4H4Psl64_card_modEq (F := F) (W := V) (ℓ := 17) (by decide +kernel) b hb
    rw [hF, hV] at h
    simpa [hK] using h
  have he : Module.finrank F K = 2 ∨ Module.finrank F K = 6 := by
    have hle : Module.finrank F K ≤ 6 := by
      have h := Submodule.finrank_le K
      rwa [hV] at h
    rcases ggF4H4Psl64_res17 ⟨Module.finrank F K, by omega⟩ hmod with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases he with h2 | h6
  · simpa [hK] using h2
  · exfalso
    have htop : K = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h6, hV])
    have hb1' : b = 1 := by
      ext v
      have hv : v ∈ K := by rw [htop]; exact Submodule.mem_top
      have h : (b : V →ₗ[F] V) v - v = 0 := hv
      exact sub_eq_zero.1 h
    exact hb1 hb1'

end CFSG.StandardType

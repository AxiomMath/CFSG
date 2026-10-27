module

public import CFSG.SignalizerFunctorTheorem.NonLocal.E6Heis
public import CFSG.SignalizerFunctorTheorem.NonLocal.TwistedClosing
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalizedStatements

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley (subfieldRootGroupImage
  twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic
  finite_field_automorphism_fixed_field_cardinality)
open CFSG.SignalizerFunctorTheorem.CatalogBridge

namespace CFSG.SignalizerFunctorTheorem.NonLocal

theorem exists_pow_ne_self {k : Type} [Field k] [Finite k] {ℓ : ℕ} (hℓ : 1 < ℓ)
    (hk : Nat.card k = ℓ ^ 2) : ∃ u : k, u ^ ℓ ≠ u := by
  classical
  by_contra h
  push Not at h
  have := Fintype.ofFinite k
  have hcard : Fintype.card k = ℓ ^ 2 := by rw [← Nat.card_eq_fintype_card, hk]
  have hdeg : (Polynomial.X ^ ℓ - Polynomial.X : Polynomial k).natDegree = ℓ :=
    FiniteField.X_pow_card_sub_X_natDegree_eq k hℓ
  have hne : (Polynomial.X ^ ℓ - Polynomial.X : Polynomial k) ≠ 0 := fun h0 => by
    rw [h0, Polynomial.natDegree_zero] at hdeg
    omega
  have hsub : (Finset.univ : Finset k).val ⊆
      (Polynomial.X ^ ℓ - Polynomial.X : Polynomial k).roots := fun u _ => by
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, h u, sub_self]
  have := Polynomial.card_le_degree_of_subset_roots hsub
  rw [Finset.card_univ, hcard, hdeg] at this
  nlinarith

theorem pow_pow_add_mul_eq_aux {k : Type*} [Field k] [Finite k] {ℓ m : ℕ}
    (hk : Nat.card k = ℓ ^ m) (a b : ℕ) (c : k) : c ^ ℓ ^ (m * a + b) = c ^ ℓ ^ b := by
  have : Fintype k := Fintype.ofFinite k
  have hq : Fintype.card k = ℓ ^ m := by rw [← Nat.card_eq_fintype_card, hk]
  have he : ℓ ^ (m * a + b) = (ℓ ^ m) ^ a * ℓ ^ b := by rw [pow_add, pow_mul]
  rw [he, pow_mul, ← hq, FiniteField.pow_card_pow]

theorem subfieldNonLocalizedTwistedE6Small :
    SubfieldNonLocalizedTwistedE6Small := by
  intro ℓ d p hℓ hd hp hp3 hℓ23 hd1 K _ _ hK κ σ σ₀ hκ hσ hσ₀
  classical
  subst hd1
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ
    (Nat.mul_pos (Nat.mul_pos (by norm_num) hd) hp.pos) hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨fr, hfr, -⟩ := finite_field_automorphism_fixed_field_cardinality hℓ
    (Nat.mul_pos (Nat.mul_pos (by norm_num) hd) hp.pos) hK
  obtain ⟨ε, hε⟩ : ∃ ε : K ≃+* K, ∀ c, ε c = c ^ ℓ ^ (1 * (p + 1)) :=
    ⟨fr ^ (1 * (p + 1)), fun c => ringAut_pow_apply_of_frobenius hfr (1 * (p + 1)) c⟩
  obtain ⟨-, hk, hJC, -, -, hsJ, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer hℓ hd
      (by omega : 3 ≤ p) hpodd K hK κ hκ σ hσ σ₀ hσ₀ ε hε
  have : Finite (fixSubfield κ) := Subtype.finite
  have : CharP (fixSubfield κ) ℓ :=
    (RingHom.charP_iff (fixSubfield κ).subtype (fixSubfield κ).subtype.injective ℓ).mpr
      ‹CharP K ℓ›
  set C := graphFixedRootGroup TwistTag.E6 K σ.toRingHom with hCdef
  set J := subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀ with hJdef
  have hk2 : Nat.card (fixSubfield κ) = ℓ ^ 2 := by rw [hk]
  have hσ₀k : ∀ c : fixSubfield κ, σ₀.toRingHom c = c ^ ℓ := fun c =>
    Subtype.ext (by rw [SubmonoidClass.coe_pow]; simpa using hσ₀ c)
  have hsimple : IsSimpleGroup (J.subgroupOf C) :=
    (Subgroup.subgroupOfEquivOfLe hJC).isSimpleGroup
  have hσι : ∀ c : fixSubfield κ, σ.toRingHom ((fixSubfield κ).subtype c) =
      (fixSubfield κ).subtype (σ₀.toRingHom c) := fun c => by
    have hpe : 1 * p = 2 * 1 * (p / 2) + 1 := by
      have h2 := Nat.div_add_mod p 2
      have h3 : p % 2 = 1 := Nat.odd_iff.1 hpodd
      omega
    have hk' : Nat.card (fixSubfield κ) = ℓ ^ (2 * 1) := by rw [hk2]
    have h1 := pow_pow_add_mul_eq_aux (ℓ := ℓ) (m := 2 * 1) (k := fixSubfield κ) hk' (p / 2) 1 c
    rw [← hpe] at h1
    have h2 := congrArg Subtype.val h1
    rw [SubmonoidClass.coe_pow, SubmonoidClass.coe_pow] at h2
    change σ (c : K) = ((σ₀ c : fixSubfield κ) : K)
    rw [hσ, hσ₀]
    simpa using h2
  have hσ₀2 : ∀ c : fixSubfield κ, σ₀.toRingHom (σ₀.toRingHom c) = c := fun c => by
    rw [hσ₀k, hσ₀k, ← pow_mul]
    have hmem : (c : K) ∈ fixSubfield κ := c.2
    have h1 : (c : K) ^ ℓ ^ (2 * 1) = c := by rw [← hκ]; exact hmem
    refine Subtype.ext ?_
    rw [SubmonoidClass.coe_pow]
    have := h1
    rw [show ℓ ^ (2 * 1) = ℓ * ℓ by ring] at this
    rw [show ℓ * ℓ = ℓ * ℓ from rfl]
    exact this
  have hne : ∃ u : fixSubfield κ, σ₀.toRingHom u ≠ u := by
    obtain ⟨u, hu⟩ := exists_pow_ne_self (k := fixSubfield κ) hℓ.one_lt hk2
    exact ⟨u, fun h => hu (by rw [← hσ₀k u]; exact h)⟩
  have hcases : 78 < Nat.card (fixSubfield κ) ^ 3 ∨
      ((2 : fixSubfield κ) = 0 ∧ 78 < 2 * Nat.card (fixSubfield κ) ^ 3) := by
    rw [hk2]
    rcases hℓ23 with rfl | rfl
    · right
      exact ⟨CharTwo.two_eq_zero, by norm_num⟩
    · left
      norm_num
  have h78 : TwistTag.E6.tag.rank + TwistTag.E6.tag.rootCount = 78 := by decide
  exact nonLocalized_twisted_of_no_small_action TwistTag.E6 ℓ (fixSubfield κ).subtype
    σ.toRingHom σ₀.toRingHom σ₀.surjective hσι hsimple
    (fun Λ _ hΛ π hπ => no_small_faithful_action_E6 σ₀.toRingHom hσ₀2 hne hcases
      (by rw [h78] at hΛ; exact hΛ) π hπ)

end CFSG.SignalizerFunctorTheorem.NonLocal

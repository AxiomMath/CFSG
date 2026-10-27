module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

public section

namespace CFSG.Quasithin.H13.L827X.LBFourier

open scoped Classical

variable {p : ℕ} {F : Type*} [Field F] {E : Type*} [AddCommGroup E] [Module (ZMod p) E]

private instance instNeZeroOfFactPrime [Fact p.Prime] : NeZero p :=
  ⟨(Fact.out : p.Prime).ne_zero⟩

@[expose] noncomputable def chi (ζ : F) (f : Module.Dual (ZMod p) E) (x : E) : F :=
  ζ ^ (f x).val

@[expose] noncomputable def idem {M : Type*} [AddCommGroup M] [Module F M] [Fintype E] (ζ : F)
    (ρ : E → Module.End F M) (f : Module.Dual (ZMod p) E) : Module.End F M :=
  ((Fintype.card E : F))⁻¹ • ∑ x : E, (chi ζ f x)⁻¹ • ρ x

private theorem pow_mod_eq {ζ : F} (hζ : IsPrimitiveRoot ζ p) (n : ℕ) :
    ζ ^ (n % p) = ζ ^ n := by
  rw [hζ.eq_orderOf, pow_mod_orderOf]

theorem chi_add [Fact p.Prime] {ζ : F} (hζ : IsPrimitiveRoot ζ p) (f : Module.Dual (ZMod p) E)
    (x y : E) : chi ζ f (x + y) = chi ζ f x * chi ζ f y := by
  unfold chi
  rw [map_add, ZMod.val_add, pow_mod_eq hζ, pow_add]

theorem chi_zero (ζ : F) (f : Module.Dual (ZMod p) E) : chi ζ f 0 = 1 := by
  simp [chi]

theorem chi_dual_zero (ζ : F) (x : E) : chi ζ (0 : Module.Dual (ZMod p) E) x = 1 := by
  simp [chi]

theorem chi_add_left [Fact p.Prime] {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (f g : Module.Dual (ZMod p) E) (x : E) :
    chi ζ (f + g) x = chi ζ f x * chi ζ g x := by
  unfold chi
  rw [LinearMap.add_apply, ZMod.val_add, pow_mod_eq hζ, pow_add]

theorem chi_neg_inv [Fact p.Prime] {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (f : Module.Dual (ZMod p) E) (x : E) : chi ζ f (-x) = (chi ζ f x)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_right
  rw [← chi_add hζ, add_neg_cancel, chi_zero]

theorem chi_neg_dual [Fact p.Prime] {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (f : Module.Dual (ZMod p) E) (x : E) : chi ζ (-f) x = (chi ζ f x)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_right
  rw [← chi_add_left hζ, add_neg_cancel, chi_dual_zero]

theorem chi_sub_dual [Fact p.Prime] {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (f g : Module.Dual (ZMod p) E) (x : E) :
    chi ζ (g - f) x = (chi ζ f x)⁻¹ * chi ζ g x := by
  rw [sub_eq_add_neg, chi_add_left hζ, chi_neg_dual hζ]
  exact mul_comm _ _

theorem chi_inv_sub [Fact p.Prime] {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (f : Module.Dual (ZMod p) E) (y z : E) :
    (chi ζ f (z - y))⁻¹ = chi ζ f y * (chi ζ f z)⁻¹ := by
  rw [← chi_neg_inv hζ f (z - y), show -(z - y) = y + -z by abel, chi_add hζ,
    chi_neg_inv hζ f z]

noncomputable instance instFintypeDual [Fact p.Prime] [Fintype E] :
    Fintype (Module.Dual (ZMod p) E) := by
  haveI : Finite (Module.Dual (ZMod p) E) :=
    Finite.of_injective (fun f : Module.Dual (ZMod p) E => (f : E → ZMod p))
      LinearMap.coe_injective
  exact Fintype.ofFinite _

theorem sum_chi_left [Fact p.Prime] [Fintype E] {ζ : F} (hζ : IsPrimitiveRoot ζ p) (x : E) :
    ∑ f : Module.Dual (ZMod p) E, chi ζ f x =
      if x = 0 then (Fintype.card (Module.Dual (ZMod p) E) : F) else 0 := by
  by_cases hx : x = 0
  · subst hx
    simp [chi_zero]
  · rw [if_neg hx]
    obtain ⟨f₀, hf₀⟩ := Module.Projective.exists_dual_eq_one (ZMod p) hx
    have hshift : ∑ f : Module.Dual (ZMod p) E, chi ζ (f + f₀) x
        = ∑ f : Module.Dual (ZMod p) E, chi ζ f x :=
      Equiv.sum_comp (Equiv.addRight f₀) (fun f => chi ζ f x)
    have hζ₀ : chi ζ f₀ x = ζ := by
      unfold chi
      rw [hf₀, ZMod.val_one, pow_one]
    have key : (∑ f : Module.Dual (ZMod p) E, chi ζ f x) * chi ζ f₀ x
        = ∑ f : Module.Dual (ZMod p) E, chi ζ f x := by
      rw [Finset.sum_mul]
      simp only [← chi_add_left hζ]
      exact hshift
    rw [hζ₀] at key
    have h1 : (∑ f : Module.Dual (ZMod p) E, chi ζ f x) * (ζ - 1) = 0 := by
      rw [mul_sub, mul_one, key, sub_self]
    have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
    exact (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr (hζ.ne_one hp1))

theorem sum_chi_right [Fact p.Prime] [Fintype E] {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (f : Module.Dual (ZMod p) E) :
    ∑ x : E, chi ζ f x = if f = 0 then (Fintype.card E : F) else 0 := by
  by_cases hf : f = 0
  · subst hf
    simp [chi_dual_zero]
  · rw [if_neg hf]
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : E, f x₀ ≠ 0 := by
      by_contra h
      simp only [not_exists, ne_eq, not_not] at h
      exact hf (LinearMap.ext fun x => by simpa using h x)
    have hshift : ∑ x : E, chi ζ f (x + x₀) = ∑ x : E, chi ζ f x :=
      Equiv.sum_comp (Equiv.addRight x₀) (fun x => chi ζ f x)
    have key : (∑ x : E, chi ζ f x) * chi ζ f x₀ = ∑ x : E, chi ζ f x := by
      rw [Finset.sum_mul]
      simp only [chi_add hζ] at hshift
      exact hshift
    have hne : chi ζ f x₀ ≠ 1 := by
      intro h
      have h' : ζ ^ (f x₀).val = 1 := h
      have hdvd : p ∣ (f x₀).val := (hζ.pow_eq_one_iff_dvd _).mp h'
      have hv : (f x₀).val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _)
      exact hx₀ ((ZMod.val_eq_zero _).mp hv)
    have h1 : (∑ x : E, chi ζ f x) * (chi ζ f x₀ - 1) = 0 := by
      rw [mul_sub, mul_one, key, sub_self]
    exact (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr hne)

theorem idem_eq_sum {M : Type*} [AddCommGroup M] [Module F M] [Fintype E] (ζ : F)
    (ρ : E → Module.End F M) (f : Module.Dual (ZMod p) E) :
    idem ζ ρ f = ((Fintype.card E : F))⁻¹ • ∑ x : E, (chi ζ f x)⁻¹ • ρ x :=
  rfl

theorem rho_mul_idem [Fact p.Prime] [Fintype E] {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {M : Type*} [AddCommGroup M] [Module F M] (ρ : E → Module.End F M)
    (hρadd : ∀ x y : E, ρ (x + y) = ρ x * ρ y) (f : Module.Dual (ZMod p) E) (y : E) :
    ρ y * idem ζ ρ f = chi ζ f y • idem ζ ρ f := by
  have hA : ∑ x : E, (chi ζ f x)⁻¹ • ρ (y + x) = ∑ z : E, (chi ζ f (z - y))⁻¹ • ρ z :=
    Fintype.sum_equiv (Equiv.addLeft y) _ _ fun x => by simp
  have hB : ∀ z : E, (chi ζ f (z - y))⁻¹ • ρ z = chi ζ f y • ((chi ζ f z)⁻¹ • ρ z) := by
    intro z
    rw [chi_inv_sub hζ f y z, mul_smul]
  rw [idem_eq_sum ζ ρ f, mul_smul_comm, Finset.mul_sum]
  simp only [mul_smul_comm, ← hρadd]
  rw [hA]
  simp only [hB, ← Finset.smul_sum]
  rw [smul_comm]

theorem card_eq_sq [Fact p.Prime] [Fintype E] (hE : Module.finrank (ZMod p) E = 2) :
    Fintype.card E = p ^ 2 := by
  haveI : Module.Finite (ZMod p) E := Module.finite_of_finrank_pos (by rw [hE]; norm_num)
  have e : Fintype.card E = Fintype.card (ZMod p) ^ Module.finrank (ZMod p) E :=
    Module.card_eq_pow_finrank
  rw [e, hE, ZMod.card]

theorem card_cast_ne_zero [Fact p.Prime] [Fintype E] (hpF : (p : F) ≠ 0)
    (hE : Module.finrank (ZMod p) E = 2) : (Fintype.card E : F) ≠ 0 := by
  rw [card_eq_sq hE]
  push_cast
  exact pow_ne_zero _ hpF

theorem idem_mul_idem [Fact p.Prime] [Fintype E] {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hpF : (p : F) ≠ 0) (hE : Module.finrank (ZMod p) E = 2)
    {M : Type*} [AddCommGroup M] [Module F M] (ρ : E → Module.End F M)
    (hρadd : ∀ x y : E, ρ (x + y) = ρ x * ρ y) (f g : Module.Dual (ZMod p) E) :
    idem ζ ρ f * idem ζ ρ g = if f = g then idem ζ ρ f else 0 := by
  have hcard : (Fintype.card E : F) ≠ 0 := card_cast_ne_zero hpF hE
  have hsum : (∑ x : E, (chi ζ f x)⁻¹ • ρ x) * idem ζ ρ g
      = (∑ x : E, (chi ζ f x)⁻¹ * chi ζ g x) • idem ζ ρ g := by
    rw [Finset.sum_mul, Finset.sum_smul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [smul_mul_assoc, rho_mul_idem hζ ρ hρadd g x, smul_smul]
  have hsub : ∑ x : E, (chi ζ f x)⁻¹ * chi ζ g x
      = if f = g then (Fintype.card E : F) else 0 := by
    simp only [← chi_sub_dual hζ f g]
    rw [sum_chi_right hζ (g - f)]
    by_cases hfg : f = g
    · subst hfg
      simp
    · have hgf : ¬ (g - f = 0) := fun h => hfg (sub_eq_zero.mp h).symm
      rw [if_neg hfg, if_neg hgf]
  calc idem ζ ρ f * idem ζ ρ g
      = ((Fintype.card E : F))⁻¹ • ((∑ x : E, (chi ζ f x)⁻¹ • ρ x) * idem ζ ρ g) := by
        rw [idem_eq_sum ζ ρ f, smul_mul_assoc]
    _ = ((Fintype.card E : F))⁻¹ • ((∑ x : E, (chi ζ f x)⁻¹ * chi ζ g x) • idem ζ ρ g) := by
        rw [hsum]
    _ = ((Fintype.card E : F))⁻¹ • ((if f = g then (Fintype.card E : F) else 0) • idem ζ ρ g) := by
        rw [hsub]
    _ = if f = g then idem ζ ρ f else 0 := by
        by_cases hfg : f = g
        · subst hfg
          rw [if_pos rfl, if_pos rfl, smul_smul, inv_mul_cancel₀ hcard, one_smul]
        · simp [hfg]

theorem sum_idem [Fact p.Prime] [Fintype E] {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (hpF : (p : F) ≠ 0) (hE : Module.finrank (ZMod p) E = 2)
    {M : Type*} [AddCommGroup M] [Module F M] (ρ : E → Module.End F M) (hρ0 : ρ 0 = 1) :
    ∑ f : Module.Dual (ZMod p) E, idem ζ ρ f = 1 := by
  have hcard : (Fintype.card E : F) ≠ 0 := card_cast_ne_zero hpF hE
  have hdual : Fintype.card (Module.Dual (ZMod p) E) = Fintype.card E := by
    haveI : Module.Finite (ZMod p) E := Module.finite_of_finrank_pos (by rw [hE]; norm_num)
    have e1 : Fintype.card (Module.Dual (ZMod p) E)
        = Fintype.card (ZMod p) ^ Module.finrank (ZMod p) (Module.Dual (ZMod p) E) :=
      Module.card_eq_pow_finrank
    have e2 : Fintype.card E = Fintype.card (ZMod p) ^ Module.finrank (ZMod p) E :=
      Module.card_eq_pow_finrank
    rw [e1, Subspace.dual_finrank_eq, ← e2]
  have hx : ∀ x : E, ∑ f : Module.Dual (ZMod p) E, (chi ζ f x)⁻¹ • ρ x
      = (if x = 0 then (Fintype.card E : F) else 0) • ρ x := by
    intro x
    rw [← Finset.sum_smul]
    congr 1
    have h1 : ∑ f : Module.Dual (ZMod p) E, (chi ζ f x)⁻¹
        = ∑ f : Module.Dual (ZMod p) E, chi ζ f x := by
      simp only [← chi_neg_dual hζ]
      exact Equiv.sum_comp (Equiv.neg (Module.Dual (ZMod p) E)) (fun f => chi ζ f x)
    rw [h1, sum_chi_left hζ x, hdual]
  simp only [idem_eq_sum]
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp only [hx]
  have hfin : ∑ x : E, (if x = 0 then (Fintype.card E : F) else 0) • ρ x
      = (Fintype.card E : F) • ρ 0 := by
    simp [ite_smul]
  rw [hfin, hρ0, smul_smul, inv_mul_cancel₀ hcard, one_smul]

end CFSG.Quasithin.H13.L827X.LBFourier

end

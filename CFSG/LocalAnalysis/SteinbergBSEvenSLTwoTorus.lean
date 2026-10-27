module

public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Tactic.ComputeDegree

public section

namespace CFSG.LocalAnalysis.SteinbergBS

open Polynomial

section NonsplitField

variable {k : Type*} [Field k]

theorem irreducible_X_sq_sub_X_sub_C [CharP k 2] {a : k} (ha : ∀ b : k, b ^ 2 + b ≠ a) :
    Irreducible (X ^ 2 - X - C a : k[X]) := by
  have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
  refine irreducible_of_degree_le_three_of_not_isRoot ?_ fun b hb => ha b ?_
  · have h : (X ^ 2 - X - C a : k[X]).natDegree = 2 := by compute_degree!
    rw [h]
    decide
  · simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C] at hb
    linear_combination hb + b * h2

variable (a : k) [Fact (Irreducible (X ^ 2 - X - C a : k[X]))]

local notation "E" => AdjoinRoot (X ^ 2 - X - C a : k[X])
local notation "θ" => AdjoinRoot.root (X ^ 2 - X - C a : k[X])

theorem nonsplit_root_sq : θ ^ 2 = θ + algebraMap k E a := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 - X - C a : k[X])
  simp only [eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C] at h
  rw [AdjoinRoot.algebraMap_eq]
  linear_combination h

theorem nonsplit_finrank : Module.finrank k E = 2 := by
  have hf : (X ^ 2 - X - C a : k[X]) ≠ 0 := (Fact.out : Irreducible _).ne_zero
  rw [(AdjoinRoot.powerBasis hf).finrank, AdjoinRoot.powerBasis_dim]
  compute_degree!

instance nonsplit_moduleFinite : Module.Finite k E :=
  (AdjoinRoot.powerBasis (Fact.out : Irreducible (X ^ 2 - X - C a : k[X])).ne_zero).finite

theorem nonsplit_coords_injective {x y x' y' : k}
    (h : algebraMap k E x + algebraMap k E y * θ = algebraMap k E x' + algebraMap k E y' * θ) :
    x = x' ∧ y = y' := by
  have hirr : Irreducible (X ^ 2 - X - C a : k[X]) := Fact.out
  by_cases hy : y = y'
  · subst hy
    exact ⟨(algebraMap k E).injective (by simpa using h), rfl⟩
  · exfalso
    have hyy : y' - y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
    set c := (x - x') / (y' - y) with hc
    have hθ : θ = algebraMap k E c := by
      have h1 : algebraMap k E (y' - y) * θ = algebraMap k E (x - x') := by
        rw [map_sub, map_sub]
        linear_combination -h
      rw [hc, map_div₀, ← h1, mul_div_cancel_left₀ _ ((_root_.map_ne_zero _).2 hyy)]
    have hroot : algebraMap k E (c ^ 2 - c - a) = 0 := by
      rw [map_sub, map_sub, map_pow, ← hθ, nonsplit_root_sq]
      ring
    have hc0 : c ^ 2 - c - a = 0 := (_root_.map_eq_zero _).1 hroot
    have hdeg : (X ^ 2 - X - C a : k[X]).natDegree = 2 := by compute_degree!
    have h1 := Polynomial.degree_eq_one_of_irreducible_of_root hirr (x := c)
      (by simp [IsRoot, hc0])
    rw [Polynomial.degree_eq_natDegree hirr.ne_zero, hdeg] at h1
    exact absurd h1 (by decide)

variable [Fintype k]

instance nonsplit_finite : Finite E := Module.finite_of_finite k

theorem nonsplit_natCard : Nat.card E = Fintype.card k ^ 2 := by
  rw [Module.natCard_eq_pow_finrank (K := k), nonsplit_finrank, Nat.card_eq_fintype_card]

theorem nonsplit_coords_surjective (z : E) :
    ∃ x y : k, algebraMap k E x + algebraMap k E y * θ = z := by
  classical
  let := Fintype.ofFinite E
  have hbij : Function.Bijective
      (fun p : k × k => algebraMap k E p.1 + algebraMap k E p.2 * θ) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun p q h => ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := nonsplit_coords_injective a h
      exact Prod.ext h1 h2
    · rw [Fintype.card_prod, ← Nat.card_eq_fintype_card (α := E), nonsplit_natCard, sq]
  obtain ⟨⟨x, y⟩, hxy⟩ := hbij.2 z
  exact ⟨x, y, hxy⟩

variable [CharP k 2]

theorem nonsplit_frobenius (x y : k) :
    (algebraMap k E x + algebraMap k E y * θ) ^ Fintype.card k =
      algebraMap k E x + algebraMap k E y * θ ^ Fintype.card k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP E 2 := charP_of_injective_algebraMap (algebraMap k E).injective 2
  obtain ⟨n, -, hn⟩ := FiniteField.card k 2
  rw [hn, add_pow_char_pow, mul_pow, ← map_pow, ← map_pow, ← hn, FiniteField.pow_card,
    FiniteField.pow_card]

theorem nonsplit_root_pow_card : θ ^ Fintype.card k = θ + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP E 2 := charP_of_injective_algebraMap (algebraMap k E).injective 2
  have h2E : (2 : E) = 0 := CharP.cast_eq_zero E 2
  have hθ := nonsplit_root_sq a
  obtain ⟨n, -, hn⟩ := FiniteField.card k 2
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  have hroot : (θ ^ Fintype.card k) ^ 2 - θ ^ Fintype.card k - algebraMap k E a = 0 := by
    have h0 : (θ ^ 2 - θ - algebraMap k E a) ^ Fintype.card k = 0 := by
      rw [hθ]
      ring_nf
      exact zero_pow (by omega)
    rw [hn, sub_pow_char_pow, sub_pow_char_pow, ← hn, ← map_pow, FiniteField.pow_card,
      ← pow_mul, mul_comm, pow_mul] at h0
    exact h0
  have hfac : (θ ^ Fintype.card k - θ) * (θ ^ Fintype.card k - (θ + 1)) = 0 := by
    linear_combination hroot + hθ + (θ + algebraMap k E a - θ ^ Fintype.card k * θ) * h2E
  rcases mul_eq_zero.1 hfac with h | h
  · exfalso
    classical
    let := Fintype.ofFinite E
    have hfix : ∀ z : E, z ^ Fintype.card k = z := by
      intro z
      obtain ⟨x, y, rfl⟩ := nonsplit_coords_surjective a z
      rw [nonsplit_frobenius, sub_eq_zero.1 h]
    have hne : (X ^ Fintype.card k - X : E[X]) ≠ 0 :=
      FiniteField.X_pow_card_sub_X_ne_zero E hq
    have hle := Polynomial.card_le_degree_of_subset_roots (p := (X ^ Fintype.card k - X : E[X]))
      (Z := Finset.univ) (fun z _ => (mem_roots hne).2 (by simp [hfix z]))
    rw [FiniteField.X_pow_card_sub_X_natDegree_eq E hq, Finset.card_univ,
      ← Nat.card_eq_fintype_card, nonsplit_natCard] at hle
    nlinarith
  · exact sub_eq_zero.1 h

theorem nonsplit_norm (x y : k) :
    (algebraMap k E x + algebraMap k E y * θ) ^ (Fintype.card k + 1) =
      algebraMap k E (x ^ 2 + x * y + a * y ^ 2) := by
  have : CharP E 2 := charP_of_injective_algebraMap (algebraMap k E).injective 2
  have h2E : (2 : E) = 0 := CharP.cast_eq_zero E 2
  have hθ := nonsplit_root_sq a
  rw [pow_succ (algebraMap k E x + algebraMap k E y * θ) (Fintype.card k), nonsplit_frobenius,
    nonsplit_root_pow_card, map_add, map_add, map_mul, map_mul, map_pow, map_pow]
  linear_combination (algebraMap k E y) ^ 2 * hθ +
    (algebraMap k E x * algebraMap k E y * θ + (algebraMap k E y) ^ 2 * θ) * h2E

end NonsplitField

section NonsplitTorus

variable {k : Type*} [Field k]
@[expose] def nonsplitTorus [CharP k 2] (a : k) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) k) where
  carrier := {g | ∃ x y : k, x ^ 2 + x * y + a * y ^ 2 = 1 ∧
    (g : Matrix (Fin 2) (Fin 2) k) = !![x, a * y; y, x + y]}
  mul_mem' := by
    rintro g h ⟨x, y, hxy, hg⟩ ⟨x', y', hxy', hh⟩
    have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
    refine ⟨x * x' + a * y * y', x * y' + y * x' + y * y', ?_, ?_⟩
    · linear_combination (x' ^ 2 + x' * y' + a * y' ^ 2) * hxy + hxy' +
        (-a * y ^ 2 * (x' ^ 2 + x' * y' + a * y' ^ 2) - a * y' ^ 2 * (x ^ 2 + x * y + a * y ^ 2) +
          2 * a ^ 2 * y ^ 2 * y' ^ 2 + a * (x * y' + y * x' + y * y') ^ 2) * h2
    · rw [Matrix.SpecialLinearGroup.coe_mul, hg, hh, Matrix.mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> ring
  one_mem' := ⟨1, 0, by ring, by simp [Matrix.one_fin_two]⟩
  inv_mem' := by
    rintro g ⟨x, y, hxy, hg⟩
    have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
    refine ⟨x + y, y, by linear_combination hxy + (x * y + y ^ 2) * h2, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_inv, hg, Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · linear_combination (-(a * y)) * h2
    · linear_combination (-y) * h2
    · linear_combination (-y) * h2

variable [CharP k 2] (a : k) [Fact (Irreducible (X ^ 2 - X - C a : k[X]))]

local notation "E" => AdjoinRoot (X ^ 2 - X - C a : k[X])
local notation "θ" => AdjoinRoot.root (X ^ 2 - X - C a : k[X])

noncomputable def nonsplitTorusToField : nonsplitTorus a →* E where
  toFun g := algebraMap k E ((g : Matrix (Fin 2) (Fin 2) k) 0 0) +
    algebraMap k E ((g : Matrix (Fin 2) (Fin 2) k) 1 0) * θ
  map_one' := by simp
  map_mul' := by
    rintro ⟨g, x, y, hxy, hg⟩ ⟨h, x', y', hxy', hh⟩
    have hθ := nonsplit_root_sq a
    change algebraMap k E (((g * h : Matrix.SpecialLinearGroup (Fin 2) k) :
        Matrix (Fin 2) (Fin 2) k) 0 0) +
      algebraMap k E (((g * h : Matrix.SpecialLinearGroup (Fin 2) k) :
        Matrix (Fin 2) (Fin 2) k) 1 0) * θ =
      (algebraMap k E ((g : Matrix (Fin 2) (Fin 2) k) 0 0) +
        algebraMap k E ((g : Matrix (Fin 2) (Fin 2) k) 1 0) * θ) *
      (algebraMap k E ((h : Matrix (Fin 2) (Fin 2) k) 0 0) +
        algebraMap k E ((h : Matrix (Fin 2) (Fin 2) k) 1 0) * θ)
    rw [Matrix.SpecialLinearGroup.coe_mul, hg, hh, Matrix.mul_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, map_add, map_mul]
    linear_combination (-(algebraMap k E y * algebraMap k E y')) * hθ

theorem nonsplitTorusToField_apply {g : nonsplitTorus a} {x y : k}
    (hg : ((g : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![x, a * y; y, x + y]) :
    nonsplitTorusToField a g = algebraMap k E x + algebraMap k E y * θ := by
  change algebraMap k E (((g : Matrix.SpecialLinearGroup (Fin 2) k) :
      Matrix (Fin 2) (Fin 2) k) 0 0) +
    algebraMap k E (((g : Matrix.SpecialLinearGroup (Fin 2) k) :
      Matrix (Fin 2) (Fin 2) k) 1 0) * θ = _
  rw [hg]
  simp

theorem nonsplitTorusToField_injective : Function.Injective (nonsplitTorusToField a) := by
  rintro ⟨g, x, y, hxy, hg⟩ ⟨h, x', y', hxy', hh⟩ hgh
  rw [nonsplitTorusToField_apply a hg, nonsplitTorusToField_apply a hh] at hgh
  obtain ⟨rfl, rfl⟩ := nonsplit_coords_injective a hgh
  exact Subtype.ext (Subtype.ext (hg.trans hh.symm))

variable [Fintype k]

theorem nonsplitTorusToField_pow (g : nonsplitTorus a) :
    nonsplitTorusToField a g ^ (Fintype.card k + 1) = 1 := by
  obtain ⟨g, x, y, hxy, hg⟩ := g
  rw [nonsplitTorusToField_apply a hg, nonsplit_norm, hxy, map_one]

theorem natCard_nonsplitTorus : Nat.card (nonsplitTorus a) = Fintype.card k + 1 := by
  classical
  have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  have hbij : Function.Bijective (fun g : nonsplitTorus a =>
      (⟨nonsplitTorusToField a g, nonsplitTorusToField_pow a g⟩ :
        {z : E // z ^ (Fintype.card k + 1) = 1})) := by
    refine ⟨fun g h hgh => nonsplitTorusToField_injective a (congrArg Subtype.val hgh), ?_⟩
    rintro ⟨z, hz⟩
    obtain ⟨x, y, rfl⟩ := nonsplit_coords_surjective a z
    have hN : x ^ 2 + x * y + a * y ^ 2 = 1 := by
      rw [nonsplit_norm, ← map_one (algebraMap k E)] at hz
      exact (algebraMap k E).injective hz
    have hdet : (!![x, a * y; y, x + y] : Matrix (Fin 2) (Fin 2) k).det = 1 := by
      rw [Matrix.det_fin_two_of]
      linear_combination hN - a * y ^ 2 * h2
    refine ⟨⟨⟨!![x, a * y; y, x + y], hdet⟩, x, y, hN, rfl⟩, ?_⟩
    exact Subtype.ext (nonsplitTorusToField_apply a (g := ⟨⟨_, hdet⟩, x, y, hN, rfl⟩) rfl)
  rw [Nat.card_eq_of_bijective _ hbij]
  let := Fintype.ofFinite E
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Eˣ)
  have hcardU : Nat.card Eˣ = (Fintype.card k + 1) * (Fintype.card k - 1) := by
    rw [Nat.card_units, nonsplit_natCard]
    obtain ⟨r, hr⟩ : ∃ r, Fintype.card k = r + 1 := ⟨Fintype.card k - 1, by omega⟩
    rw [hr, Nat.add_sub_cancel, show (r + 1) ^ 2 = (r + 1 + 1) * r + 1 by ring,
      Nat.add_sub_cancel]
  have hord : orderOf (g ^ (Fintype.card k - 1)) = Fintype.card k + 1 := by
    rw [orderOf_pow_of_dvd (by omega) (by rw [hg, hcardU]; exact dvd_mul_left _ _), hg,
      hcardU, Nat.mul_div_cancel _ (by omega)]
  have hprim : IsPrimitiveRoot (((g ^ (Fintype.card k - 1) : Eˣ)) : E) (Fintype.card k + 1) := by
    rw [← hord, ← orderOf_units]
    exact IsPrimitiveRoot.orderOf _
  calc Nat.card {z : E // z ^ (Fintype.card k + 1) = 1} =
        (nthRootsFinset (Fintype.card k + 1) (1 : E)).card := by
        rw [← Nat.card_eq_finsetCard]
        exact Nat.card_congr (Equiv.subtypeEquivRight fun z =>
          (mem_nthRootsFinset (by omega) (1 : E)).symm)
    _ = Fintype.card k + 1 := hprim.card_nthRootsFinset

theorem isCyclic_nonsplitTorus : IsCyclic (nonsplitTorus a) :=
  isCyclic_of_injective_ringHom (nonsplitTorusToField a) (nonsplitTorusToField_injective a)

theorem mem_nonsplitTorus_iff (g : Matrix.SpecialLinearGroup (Fin 2) k) :
    g ∈ nonsplitTorus a ↔ ∃ x y : k,
      (algebraMap k E x + algebraMap k E y * θ) ^ (Fintype.card k + 1) = 1 ∧
        (g : Matrix (Fin 2) (Fin 2) k) = !![x, a * y; y, x + y] := by
  change (∃ x y : k, x ^ 2 + x * y + a * y ^ 2 = 1 ∧
    (g : Matrix (Fin 2) (Fin 2) k) = !![x, a * y; y, x + y]) ↔ _
  refine exists₂_congr fun x y => and_congr_left' ?_
  rw [nonsplit_norm, ← map_one (algebraMap k E), (algebraMap k E).injective.eq_iff]

end NonsplitTorus

theorem even_sl2_nonsplit_cyclic_sylow {k : Type*} [Field k] [Fintype k] {e : ℕ} (he : 1 ≤ e)
    (hk : Fintype.card k = 2 ^ e) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) k) = 2 ^ e * (2 ^ e - 1) * (2 ^ e + 1) ∧
      (∃ T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) k), IsCyclic T ∧
        Nat.card T = 2 ^ e + 1) ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ 2 ^ e + 1 →
        ∀ P : Sylow p (Matrix.SpecialLinearGroup (Fin 2) k),
          IsCyclic P ∧ Nat.card P = p ^ (2 ^ e + 1).factorization p) ∧
      (∃ a : k, ∀ b : k, b ^ 2 + b ≠ a) ∧
      ∀ a : k, (∀ b : k, b ^ 2 + b ≠ a) →
        IsField (AdjoinRoot (X ^ 2 - X - C a : k[X])) ∧
        AdjoinRoot.root (X ^ 2 - X - C a : k[X]) ^ 2 =
          AdjoinRoot.root (X ^ 2 - X - C a : k[X]) + algebraMap k _ a ∧
        Nat.card (AdjoinRoot (X ^ 2 - X - C a : k[X])) = (2 ^ e) ^ 2 ∧
        AdjoinRoot.root (X ^ 2 - X - C a : k[X]) ^ 2 ^ e =
          AdjoinRoot.root (X ^ 2 - X - C a : k[X]) + 1 ∧
        ∃ T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) k),
          (∀ g, g ∈ T ↔ ∃ x y : k, (algebraMap k (AdjoinRoot (X ^ 2 - X - C a : k[X])) x +
              algebraMap k _ y * AdjoinRoot.root (X ^ 2 - X - C a : k[X])) ^ (2 ^ e + 1) = 1 ∧
            (g : Matrix (Fin 2) (Fin 2) k) = !![x, a * y; y, x + y]) ∧
          IsCyclic T ∧ Nat.card T = 2 ^ e + 1 := by
  classical
  have : CharP k 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two he
      (by rw [Nat.card_eq_fintype_card, hk])
  have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have hq2 : 2 ≤ 2 ^ e := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) k) =
      2 ^ e * (2 ^ e - 1) * (2 ^ e + 1) := by
    rw [Matrix.card_SL_field 2, Fin.prod_univ_two, hk]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    obtain ⟨r, hr⟩ : ∃ r, 2 ^ e = r + 2 := ⟨2 ^ e - 2, by omega⟩
    rw [hr, show (r + 2) ^ 2 - 1 = (r + 1) * (r + 3) by
        rw [show (r + 2) ^ 2 = (r + 1) * (r + 3) + 1 by ring, Nat.add_sub_cancel],
      show (r + 2) ^ 2 - (r + 2) = (r + 1) * (r + 2) by
        rw [show (r + 2) ^ 2 = (r + 1) * (r + 2) + (r + 2) by ring, Nat.add_sub_cancel],
      show r + 2 - 1 = r + 1 by omega,
      show (r + 1) * (r + 3) * ((r + 1) * (r + 2)) = (r + 1) * ((r + 2) * (r + 1) * (r + 3))
        by ring, Nat.mul_div_cancel_left _ (by omega)]
  have hex : ∃ a : k, ∀ b : k, b ^ 2 + b ≠ a := by
    by_contra h
    push Not at h
    have hinj := (Finite.injective_iff_surjective (f := fun b : k => b ^ 2 + b)).2 h
    have h01 : (0 : k) = 1 := hinj (by
      change (0 : k) ^ 2 + 0 = 1 ^ 2 + 1
      linear_combination -h2)
    exact zero_ne_one h01
  have htorus : ∀ a : k, (∀ b : k, b ^ 2 + b ≠ a) →
      IsField (AdjoinRoot (X ^ 2 - X - C a : k[X])) ∧
      AdjoinRoot.root (X ^ 2 - X - C a : k[X]) ^ 2 =
        AdjoinRoot.root (X ^ 2 - X - C a : k[X]) + algebraMap k _ a ∧
      Nat.card (AdjoinRoot (X ^ 2 - X - C a : k[X])) = (2 ^ e) ^ 2 ∧
      AdjoinRoot.root (X ^ 2 - X - C a : k[X]) ^ 2 ^ e =
        AdjoinRoot.root (X ^ 2 - X - C a : k[X]) + 1 ∧
      ∃ T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) k),
        (∀ g, g ∈ T ↔ ∃ x y : k, (algebraMap k (AdjoinRoot (X ^ 2 - X - C a : k[X])) x +
            algebraMap k _ y * AdjoinRoot.root (X ^ 2 - X - C a : k[X])) ^ (2 ^ e + 1) = 1 ∧
          (g : Matrix (Fin 2) (Fin 2) k) = !![x, a * y; y, x + y]) ∧
        IsCyclic T ∧ Nat.card T = 2 ^ e + 1 := by
    intro a ha
    have : Fact (Irreducible (X ^ 2 - X - C a : k[X])) := ⟨irreducible_X_sq_sub_X_sub_C ha⟩
    refine ⟨Field.toIsField _, nonsplit_root_sq a, by rw [nonsplit_natCard, hk], ?_,
      nonsplitTorus a, ?_, isCyclic_nonsplitTorus a, by rw [natCard_nonsplitTorus, hk]⟩
    · rw [← hk]
      exact nonsplit_root_pow_card a
    · intro g
      rw [← hk]
      exact mem_nonsplitTorus_iff a g
  obtain ⟨a₀, ha₀⟩ := hex
  have hT : ∃ T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) k), IsCyclic T ∧
      Nat.card T = 2 ^ e + 1 := by
    obtain ⟨-, -, -, -, T, -, hTcyc, hTcard⟩ := htorus a₀ ha₀
    exact ⟨T, hTcyc, hTcard⟩
  refine ⟨hSL, hT, ?_, ⟨a₀, ha₀⟩, htorus⟩
  intro p hp hp2 hpq P
  have := Fact.mk hp
  obtain ⟨T, hTcyc, hTcard⟩ := hT
  have hp2' : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  have hpq' : ¬ p ∣ 2 ^ e := fun h => hp2' (hp.dvd_of_dvd_pow h)
  have hpq1 : ¬ p ∣ 2 ^ e - 1 := fun h => by
    have h3 : p ∣ (2 ^ e + 1) - (2 ^ e - 1) := Nat.dvd_sub hpq h
    rw [show (2 ^ e + 1) - (2 ^ e - 1) = 2 by omega] at h3
    exact hp2' h3
  have hfac : (Nat.card (Matrix.SpecialLinearGroup (Fin 2) k)).factorization p =
      (2 ^ e + 1).factorization p := by
    rw [hSL, Nat.factorization_mul (Nat.mul_ne_zero (by positivity) (by omega)) (by omega),
      Nat.factorization_mul (by positivity) (by omega)]
    simp only [Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hpq',
      Nat.factorization_eq_zero_of_not_dvd hpq1, zero_add]
  have hPcard : Nat.card P = p ^ (2 ^ e + 1).factorization p := by
    rw [P.card_eq_multiplicity, hfac]
  obtain ⟨Q₀⟩ := (inferInstance : Nonempty (Sylow p T))
  have hQcard : Nat.card ((Q₀ : Subgroup T).map T.subtype) = p ^ (2 ^ e + 1).factorization p := by
    rw [Subgroup.card_map_of_injective T.subtype_injective, Q₀.card_eq_multiplicity, hTcard]
  obtain ⟨P', hP'⟩ := (Q₀.isPGroup'.map T.subtype).exists_le_sylow
  have hQP' : (Q₀ : Subgroup T).map T.subtype = P' := Subgroup.eq_of_le_of_card_ge hP'
    (by rw [P'.card_eq_multiplicity, hfac, hQcard])
  have hP'T : (P' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) k)) ≤ T := by
    rw [← hQP']
    exact Subgroup.map_subtype_le _
  have hP'cyc : IsCyclic P' :=
    isCyclic_of_injective (Subgroup.inclusion hP'T) (Subgroup.inclusion_injective hP'T)
  exact ⟨isCyclic_of_injective (Sylow.equiv P P').toMonoidHom (Sylow.equiv P P').injective,
    hPcard⟩

end CFSG.LocalAnalysis.SteinbergBS

module

public import CFSG.Quasithin.Background.G6Natural
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.ModC

open Equiv Equiv.Perm CFSG.Quasithin.G6

section Base

variable {n : ℕ}

@[expose] def ev (n : ℕ) (l : List ℕ) : PermMod n :=
  Multiplicative.ofAdd (fun i => if (i : ℕ) ∈ l then (1 : ZMod 2) else 0)

@[expose] def wt (x : PermMod n) : ℕ := (Finset.univ.filter fun i => Multiplicative.toAdd x i ≠ 0).card

theorem wt_permAct (σ : Perm (Fin n)) (x : PermMod n) : wt (permAct n σ x) = wt x := by
  unfold wt
  refine Finset.card_bij (fun i _ => σ⁻¹ i) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    simpa [permAct_apply] using hi
  · intro i _ j _ h
    exact σ⁻¹.injective h
  · intro j hj
    refine ⟨σ j, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    simpa [permAct_apply] using hj

theorem sum_permAct (σ : Perm (Fin n)) (x : PermMod n) :
    ∑ i, Multiplicative.toAdd (permAct n σ x) i = ∑ i, Multiplicative.toAdd x i := by
  simp only [permAct_apply]
  exact Equiv.sum_comp σ⁻¹ (fun i => Multiplicative.toAdd x i)

@[expose] def V4 (z v : PermMod n) : Finset (PermMod n) := {1, z, v, z * v}

@[expose] def join3F (z v : PermMod n) (g : Perm (Fin n)) : Finset (PermMod n) :=
  ((V4 z v) ×ˢ (V4 z v) ×ˢ (V4 z v)).image fun p =>
    p.1 * permAct n g p.2.1 * permAct n (g ^ 2) p.2.2

end Base

section Transport

variable {n : ℕ}

theorem V4_conj (τ : Perm (Fin n)) (z v : PermMod n) :
    V4 (permAct n τ z) (permAct n τ v) = (V4 z v).image (permAct n τ) := by
  ext y
  simp only [V4, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨1, Or.inl rfl, map_one _⟩
    · exact ⟨z, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨v, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
    · exact ⟨z * v, Or.inr (Or.inr (Or.inr rfl)), map_mul _ _ _⟩
  · rintro ⟨q, hq, rfl⟩
    rcases hq with rfl | rfl | rfl | rfl
    · exact Or.inl (map_one _)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (map_mul _ _ _)))

theorem permAct_inv_apply_self (τ : Perm (Fin n)) (y : PermMod n) :
    permAct n τ⁻¹ (permAct n τ y) = y := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

theorem permAct_inv_apply_self' (τ : Perm (Fin n)) (y : PermMod n) :
    permAct n τ (permAct n τ⁻¹ y) = y := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem permAct_conj_apply (τ g : Perm (Fin n)) (y : PermMod n) :
    permAct n (τ * g * τ⁻¹) (permAct n τ y) = permAct n τ (permAct n g y) := by
  rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, permAct_inv_apply_self]

theorem permAct_conj_inv_apply (τ s : Perm (Fin n)) (y : PermMod n) :
    permAct n (τ⁻¹ * s * τ) y = permAct n τ⁻¹ (permAct n s (permAct n τ y)) := by
  rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]

theorem join3F_conj (τ g : Perm (Fin n)) (z v : PermMod n) :
    join3F (permAct n τ z) (permAct n τ v) (τ * g * τ⁻¹) =
      (join3F z v g).image (permAct n τ) := by
  have hpow : (τ * g * τ⁻¹) ^ 2 = τ * g ^ 2 * τ⁻¹ := by
    rw [sq, sq]; group
  ext y
  simp only [join3F, V4_conj, Finset.mem_image, Finset.mem_product, hpow]
  constructor
  · rintro ⟨⟨p1, p2, p3⟩, ⟨⟨q1, hq1, rfl⟩, ⟨q2, hq2, rfl⟩, ⟨q3, hq3, rfl⟩⟩, rfl⟩
    refine ⟨q1 * permAct n g q2 * permAct n (g ^ 2) q3, ⟨(q1, q2, q3), ⟨hq1, hq2, hq3⟩, rfl⟩, ?_⟩
    simp only [permAct_conj_apply]
    simp only [map_mul]
  · rintro ⟨y', ⟨⟨q1, q2, q3⟩, ⟨hq1, hq2, hq3⟩, rfl⟩, rfl⟩
    refine ⟨(permAct n τ q1, permAct n τ q2, permAct n τ q3),
      ⟨⟨q1, hq1, rfl⟩, ⟨q2, hq2, rfl⟩, ⟨q3, hq3, rfl⟩⟩, ?_⟩
    simp only [permAct_conj_apply]
    simp only [map_mul]

theorem card_join3F_conj (τ g : Perm (Fin n)) (z v : PermMod n) :
    (join3F (permAct n τ z) (permAct n τ v) (τ * g * τ⁻¹)).card = (join3F z v g).card := by
  rw [join3F_conj]
  exact Finset.card_image_of_injective _ (permAct n τ).injective

end Transport

section Helpers

variable {n : ℕ}

theorem fix_of_closure {S : Set (Perm (Fin n))} {z : PermMod n}
    (h : ∀ s ∈ S, permAct n s z = z) : ∀ s ∈ Subgroup.closure S, permAct n s z = z := by
  intro s hs
  induction hs using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul, MulAut.mul_apply, hy, hx]
  | inv x _ hx =>
    calc permAct n x⁻¹ z = permAct n x⁻¹ (permAct n x z) := by rw [hx]
      _ = z := permAct_inv_apply_self x z

theorem sign_conj (τ s : Perm (Fin n)) : sign (τ⁻¹ * s * τ) = sign s := by
  rw [map_mul, map_mul, map_inv]
  rw [mul_comm (sign τ)⁻¹ (sign s), mul_assoc, inv_mul_cancel, mul_one]

theorem card_closure_conj (τ : Perm (Fin n)) (D D₀ : Subgroup (Perm (Fin n))) (g : Perm (Fin n))
    (hτ : ∀ s : Perm (Fin n), s ∈ D₀ ↔ τ⁻¹ * s * τ ∈ D) :
    Nat.card ↥(Subgroup.closure ((D₀ : Set (Perm (Fin n))) ∪ {τ * g * τ⁻¹})) =
      Nat.card ↥(Subgroup.closure ((D : Set (Perm (Fin n))) ∪ {g})) := by
  let f : Perm (Fin n) →* Perm (Fin n) := (MulAut.conj τ).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj τ).injective
  have himg : f '' ((D : Set (Perm (Fin n))) ∪ {g}) = (D₀ : Set (Perm (Fin n))) ∪ {τ * g * τ⁻¹} := by
    ext s
    simp only [Set.mem_image, Set.mem_union, SetLike.mem_coe, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, (hy | rfl), rfl⟩
      · left
        rw [hτ]
        show τ⁻¹ * (τ * y * τ⁻¹) * τ ∈ D
        simpa [mul_assoc] using hy
      · right; rfl
    · rintro (hs | rfl)
      · refine ⟨τ⁻¹ * s * τ, Or.inl ((hτ s).1 hs), ?_⟩
        show τ * (τ⁻¹ * s * τ) * τ⁻¹ = s
        group
      · exact ⟨g, Or.inr rfl, rfl⟩
  rw [← himg, ← MonoidHom.map_closure]
  exact Subgroup.card_map_of_injective hf

end Helpers

theorem fac_two (m : ℕ) (hm : ¬ 2 ∣ m) (hm0 : m ≠ 0) (k : ℕ) : (2 ^ k * m).factorization 2 = k := by
  rw [Nat.factorization_mul (by positivity) hm0, Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

theorem fac_alt6 : (Nat.card (alternatingGroup (Fin 6))).factorization 2 = 3 := by
  have h : Nat.card (alternatingGroup (Fin 6)) = 2 ^ 3 * 45 := by
    rw [nat_card_alternatingGroup]; simp [Nat.factorial]
  rw [h]; exact fac_two 45 (by norm_num) (by norm_num) 3

theorem fac_alt7 : (Nat.card (alternatingGroup (Fin 7))).factorization 2 = 3 := by
  have h : Nat.card (alternatingGroup (Fin 7)) = 2 ^ 3 * 315 := by
    rw [nat_card_alternatingGroup]; simp [Nat.factorial]
  rw [h]; exact fac_two 315 (by norm_num) (by norm_num) 3

theorem exists_conj_sylow {n : ℕ} (hfac : (Nat.card (alternatingGroup (Fin n))).factorization 2 = 3)
    {D D₀ : Subgroup (Perm (Fin n))} (hD : D ≤ alternatingGroup (Fin n))
    (hD₀ : D₀ ≤ alternatingGroup (Fin n)) (h8 : Nat.card D = 8) (h8' : Nat.card D₀ = 8) :
    ∃ τ : Perm (Fin n), ∀ s : Perm (Fin n), s ∈ D₀ ↔ τ⁻¹ * s * τ ∈ D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A := alternatingGroup (Fin n)
  have hc : Nat.card (D.subgroupOf A) = 2 ^ (Nat.card A).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD).toEquiv, h8, hfac]; norm_num
  have hc₀ : Nat.card (D₀.subgroupOf A) = 2 ^ (Nat.card A).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD₀).toEquiv, h8', hfac]; norm_num
  let P : Sylow 2 A := Sylow.ofCard (D.subgroupOf A) hc
  let P₀ : Sylow 2 A := Sylow.ofCard (D₀.subgroupOf A) hc₀
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq A P P₀
  refine ⟨(t : Perm (Fin n)), fun s => ?_⟩
  have hmem : ∀ s' : A, s' ∈ (P₀ : Subgroup A) ↔ t⁻¹ * s' * t ∈ (P : Subgroup A) := by
    intro s'
    rw [← ht, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  constructor
  · intro hs
    have hsA : s ∈ A := hD₀ hs
    have h1 := (hmem ⟨s, hsA⟩).1 (by
      show (⟨s, hsA⟩ : A) ∈ D₀.subgroupOf A
      exact hs)
    exact h1
  · intro hs
    have hsA : s ∈ A := by
      have h2 : (t : Perm (Fin n))⁻¹ * s * t ∈ A := hD hs
      have ht' : (t : Perm (Fin n)) ∈ A := t.2
      have := A.mul_mem (A.mul_mem ht' h2) (A.inv_mem ht')
      simpa [mul_assoc] using this
    have := (hmem ⟨s, hsA⟩).2 (by
      show t⁻¹ * (⟨s, hsA⟩ : A) * t ∈ D.subgroupOf A
      exact hs)
    exact this

@[expose] def ModelOut (n : ℕ) : Prop :=
  ∀ D : Subgroup (Perm (Fin n)), (∀ d ∈ D, sign d = 1) → Nat.card D = 8 →
    ∀ z v : PermMod n, (∑ i, Multiplicative.toAdd z i = 0) → z ≠ 1 →
    (∑ i, Multiplicative.toAdd v i = 0) → v ≠ 1 → v ≠ z →
    (∀ d ∈ D, permAct n d z = z ∧ (permAct n d v = v ∨ permAct n d v = z * v)) →
    (wt v = wt z ∨ wt (z * v) = wt z) →
    ∀ g : Perm (Fin n), g ^ 3 = 1 → permAct n g z = z → permAct n g v ≠ v →
      permAct n g v ≠ z * v → (join3F z v g).card ≠ 8 →
      ¬ 5 ∣ Nat.card ↥(Subgroup.closure ((D : Set (Perm (Fin n))) ∪ {g})) →
      ∃ y : PermMod n, y ∈ join3F z v g ∧ (∑ i, Multiplicative.toAdd y i = 0) ∧ y ≠ 1 ∧ y ≠ z ∧
        (∀ d ∈ D, permAct n d y = y) ∧
        (∀ u : PermMod n, (∑ i, Multiplicative.toAdd u i = 0) → (∀ d ∈ D, permAct n d u = u) →
          u = 1 ∨ u = z ∨ u = y ∨ u = z * y) ∧
        (∃ j : Perm (Fin n), sign j = 1 ∧ permAct n j y = y ∧ permAct n j z ≠ z) ∧
        (∃ j' : Perm (Fin n), sign j' = 1 ∧ permAct n j' y = y ∧ permAct n j' v ≠ v ∧
          permAct n j' v ≠ z * v ∧ permAct n j' v ≠ z) ∧
        (∃ L : List (Perm (Fin n)), L.length = 8 ∧ (∀ σ ∈ L, sign σ = 1) ∧
          (L.map (fun σ => permAct n σ (z * y))).Nodup) ∧
        ((Finset.univ.filter fun u : PermMod n =>
          (∑ i, Multiplicative.toAdd u i = 0) ∧ wt u = wt y).card ≤ 7)

end CFSG.Quasithin.ModC

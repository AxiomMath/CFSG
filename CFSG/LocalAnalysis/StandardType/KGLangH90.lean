module

import Mathlib.GroupTheory.Index

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.Nat.Prime.Defs

public section

namespace CFSG.StandardType

private noncomputable def kgLangH90Aux_normHom {M : Type} [CommGroup M] (β : MulAut M) (p : ℕ) :
    M →* M where
  toFun m := ((List.range p).map fun i => (β ^ i) m).prod
  map_one' := by simp
  map_mul' a b := by simp only [map_mul, List.prod_map_mul]

private noncomputable def kgLangH90Aux_langHom {M : Type} [CommGroup M] (β : MulAut M) : M →* M where
  toFun s := s⁻¹ * β s
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, mul_inv]
    exact mul_mul_mul_comm a⁻¹ b⁻¹ (β a) (β b)

private theorem kgLangH90Aux_pow_apply_comm {M : Type} [CommGroup M] (β : MulAut M) (i : ℕ) (m : M) :
    (β ^ i) (β m) = β ((β ^ i) m) := by
  rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_succ, pow_succ']

private theorem kgLangH90Aux_map_normHom {M : Type} [CommGroup M] (β : MulAut M) (p : ℕ) (m : M) :
    β (kgLangH90Aux_normHom β p m) = kgLangH90Aux_normHom β p (β m) := by
  simp only [kgLangH90Aux_normHom, MonoidHom.coe_mk, OneHom.coe_mk, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, kgLangH90Aux_pow_apply_comm]

private theorem kgLangH90Aux_normHom_apply_mul {M : Type} [CommGroup M] (β : MulAut M) (p : ℕ)
    (m : M) :
    β (kgLangH90Aux_normHom β p m) * m = kgLangH90Aux_normHom β p m * (β ^ p) m := by
  have h1 : ((List.range (p + 1)).map fun i => (β ^ i) m).prod = m * β (kgLangH90Aux_normHom β p m) := by
    rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map, kgLangH90Aux_map_normHom]
    simp only [pow_zero, MulAut.one_apply, kgLangH90Aux_normHom, MonoidHom.coe_mk, OneHom.coe_mk]
    congr 2
  have h2 : ((List.range (p + 1)).map fun i => (β ^ i) m).prod =
      kgLangH90Aux_normHom β p m * (β ^ p) m := by
    rw [List.range_succ, List.map_append, List.prod_append]
    simp [kgLangH90Aux_normHom]
  rw [mul_comm, ← h1, h2]

private theorem kgLangH90Aux_normHom_fixed {M : Type} [CommGroup M] (β : MulAut M) {p : ℕ}
    (hβ : β ^ p = 1) (m : M) :
    β (kgLangH90Aux_normHom β p m) = kgLangH90Aux_normHom β p m := by
  have h := kgLangH90Aux_normHom_apply_mul β p m
  rw [hβ, MulAut.one_apply] at h
  exact mul_right_cancel h

private theorem kgLangH90Aux_normHom_langHom {M : Type} [CommGroup M] (β : MulAut M) {p : ℕ}
    (hβ : β ^ p = 1) (s : M) :
    kgLangH90Aux_normHom β p (kgLangH90Aux_langHom β s) = 1 := by
  change kgLangH90Aux_normHom β p (s⁻¹ * β s) = 1
  rw [map_mul, map_inv, ← kgLangH90Aux_map_normHom, kgLangH90Aux_normHom_fixed β hβ, inv_mul_cancel]

theorem kgLangH90_iff_normSurj {p : ℕ} {M : Type} [CommGroup M] [Finite M] (β : MulAut M)
    (hβ : β ^ p = 1) :
    (∀ c : M, ((List.range p).map fun i => (β ^ i) c).prod = 1 → ∃ s, c = s⁻¹ * β s) ↔
      ∀ c : M, β c = c → ∃ s, c = ((List.range p).map fun i => (β ^ i) s).prod := by
  classical
  have hNL : (kgLangH90Aux_langHom β).range ≤ (kgLangH90Aux_normHom β p).ker := by
    rintro _ ⟨s, rfl⟩; exact kgLangH90Aux_normHom_langHom β hβ s
  let Fix : Subgroup M := (kgLangH90Aux_langHom β).ker
  have hFix : ∀ c, c ∈ Fix ↔ β c = c := fun c => by
    change c⁻¹ * β c = 1 ↔ _
    rw [inv_mul_eq_one, eq_comm]
  have hNF : (kgLangH90Aux_normHom β p).range ≤ Fix := by
    rintro _ ⟨m, rfl⟩; exact (hFix _).2 (kgLangH90Aux_normHom_fixed β hβ m)
  have c1 : Nat.card (kgLangH90Aux_langHom β).range * Nat.card Fix = Nat.card M := by
    rw [mul_comm]; exact Subgroup.card_ker_mul_card_range (kgLangH90Aux_langHom β)
  have c2 : Nat.card (kgLangH90Aux_normHom β p).range * Nat.card (kgLangH90Aux_normHom β p).ker =
      Nat.card M := by
    rw [mul_comm]; exact Subgroup.card_ker_mul_card_range (kgLangH90Aux_normHom β p)
  have hpos : 0 < Nat.card M := Nat.card_pos
  constructor
  · intro h c hc
    have hle : (kgLangH90Aux_normHom β p).ker ≤ (kgLangH90Aux_langHom β).range := fun c hc' => by
      obtain ⟨s, hs⟩ := h c hc'; exact ⟨s, hs.symm⟩
    have heq : (kgLangH90Aux_normHom β p).ker = (kgLangH90Aux_langHom β).range := le_antisymm hle hNL
    have hcard : Nat.card (kgLangH90Aux_normHom β p).range = Nat.card Fix := by
      rw [heq] at c2
      have : Nat.card (kgLangH90Aux_normHom β p).range * Nat.card (kgLangH90Aux_langHom β).range =
          Nat.card Fix * Nat.card (kgLangH90Aux_langHom β).range := by rw [c2, mul_comm, c1]
      exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (by
        intro h0; rw [h0, zero_mul] at c1; omega)) this
    have := Subgroup.eq_of_le_of_card_ge hNF hcard.ge
    obtain ⟨s, hs⟩ : c ∈ (kgLangH90Aux_normHom β p).range := by rw [this]; exact (hFix c).2 hc
    exact ⟨s, hs.symm⟩
  · intro h c hc
    have hle : Fix ≤ (kgLangH90Aux_normHom β p).range := fun c hc' => by
      obtain ⟨s, hs⟩ := h c ((hFix c).1 hc'); exact ⟨s, hs.symm⟩
    have heq : (kgLangH90Aux_normHom β p).range = Fix := le_antisymm hNF hle
    have hcard : Nat.card (kgLangH90Aux_normHom β p).ker = Nat.card (kgLangH90Aux_langHom β).range := by
      rw [heq] at c2
      have : Nat.card Fix * Nat.card (kgLangH90Aux_normHom β p).ker =
          Nat.card Fix * Nat.card (kgLangH90Aux_langHom β).range := by rw [c2, ← c1, mul_comm]
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (by
        intro h0; rw [h0, zero_mul] at c2; omega)) this
    have := Subgroup.eq_of_le_of_card_ge hNL hcard.le
    obtain ⟨s, hs⟩ : c ∈ (kgLangH90Aux_langHom β).range := by rw [this]; exact hc
    exact ⟨s, hs.symm⟩

private theorem kgLangH90Aux_pow_apply_eq_self {M : Type} [Group M] (α : MulAut M) {c : M}
    (hc : α c = c) (k : ℕ) : (α ^ k) c = c := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, MulAut.mul_apply, hc, ih]

private theorem kgLangH90Aux_pow_mod {M : Type} [Group M] (β : MulAut M) {p : ℕ}
    (hβ : β ^ p = 1) (k : ℕ) : β ^ k = β ^ (k % p) := by
  conv_lhs => rw [← Nat.div_add_mod k p]
  rw [pow_add, pow_mul, hβ, one_pow, one_mul]

private theorem kgLangH90Aux_mul_mod_mul_mod {p a c b : ℕ} (hp : p.Prime) (h : a * c % p = 1)
    (hb : b < p) : (c * ((a * b) % p)) % p = b := by
  have hmod : a * c ≡ 1 [MOD p] := by
    show a * c % p = 1 % p
    rw [h, Nat.mod_eq_of_lt hp.one_lt]
  have h1 : c * ((a * b) % p) ≡ c * (a * b) [MOD p] :=
    Nat.ModEq.mul_left c (Nat.mod_modEq (a * b) p)
  have h2 : c * (a * b) ≡ b [MOD p] := by
    have he : c * (a * b) = (a * c) * b := by rw [← mul_assoc c a b, mul_comm c a]
    rw [he]
    calc (a * c) * b ≡ 1 * b [MOD p] := Nat.ModEq.mul_right b hmod
      _ = b := one_mul b
  have h3 : (c * ((a * b) % p)) % p = b % p := h1.trans h2
  rwa [Nat.mod_eq_of_lt hb] at h3

theorem kgLangH90_pow_iff {p j : ℕ} (hp : p.Prime) (hj : ¬ p ∣ j) {M : Type} [CommGroup M]
    [Finite M] (β : MulAut M) (hβ : β ^ p = 1) :
    (∀ c : M, ((List.range p).map fun i => (β ^ i) c).prod = 1 → ∃ s, c = s⁻¹ * β s) ↔
      ∀ c : M, ((List.range p).map fun i => ((β ^ j) ^ i) c).prod = 1 →
        ∃ s, c = s⁻¹ * (β ^ j) s := by
  classical
  set γ : MulAut M := β ^ j with hγdef
  have hγ : γ ^ p = 1 := by
    rw [hγdef, ← pow_mul, mul_comm j p, pow_mul, hβ, one_pow]
  have hcop : Nat.Coprime j p := ((hp.coprime_iff_not_dvd).mpr hj).symm
  obtain ⟨j', _hj'lt, hj'mod⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hβγ : γ ^ j' = β := by
    rw [hγdef, ← pow_mul]
    have hmul : j * j' = p * (j * j' / p) + j * j' % p := (Nat.div_add_mod (j * j') p).symm
    rw [hmul, pow_add, pow_mul, hβ, one_pow, one_mul, hj'mod, pow_one]
  have hγβ : ∀ c, γ c = c → β c = c := by
    intro c hc
    have h := kgLangH90Aux_pow_apply_eq_self γ hc j'
    rwa [hβγ] at h
  have hβγ' : ∀ c, β c = c → γ c = c := by
    intro c hc
    have h := kgLangH90Aux_pow_apply_eq_self β hc j
    simpa [hγdef] using h
  have hfix : ∀ c, γ c = c ↔ β c = c := fun c => ⟨hγβ c, hβγ' c⟩
  have hnorm : ∀ s, ((List.range p).map fun i => (γ ^ i) s).prod =
      ((List.range p).map fun i => (β ^ i) s).prod := by
    intro s
    have hmap : (List.range p).map (fun i => (γ ^ i) s) =
        (List.range p).map (fun i => (β ^ (j * i % p)) s) := by
      apply List.map_congr_left
      intro i _
      rw [hγdef, ← pow_mul]
      exact congrArg (fun x : MulAut M => x s) (kgLangH90Aux_pow_mod β hβ (j * i))
    rw [hmap,
      ← List.prod_toFinset (l := List.range p) (f := fun i => (β ^ (j * i % p)) s)
        List.nodup_range,
      ← List.prod_toFinset (l := List.range p) (f := fun i => (β ^ i) s) List.nodup_range,
      List.toFinset_range]
    refine Finset.prod_bij' (fun a _ => (j * a) % p) (fun b _ => (j' * b) % p)
      ?_ ?_ ?_ ?_ ?_
    · intro a _
      exact Finset.mem_range.mpr (Nat.mod_lt _ hp.pos)
    · intro a _
      exact Finset.mem_range.mpr (Nat.mod_lt _ hp.pos)
    · intro a ha
      exact kgLangH90Aux_mul_mod_mul_mod hp hj'mod (Finset.mem_range.mp ha)
    · intro a ha
      exact kgLangH90Aux_mul_mod_mul_mod hp (by rw [Nat.mul_comm]; exact hj'mod)
        (Finset.mem_range.mp ha)
    · intro a _
      rfl
  rw [kgLangH90_iff_normSurj β hβ, kgLangH90_iff_normSurj γ hγ]
  refine ⟨fun h c hc => ?_, fun h c hc => ?_⟩
  · obtain ⟨s, hs⟩ := h c ((hfix c).mp hc)
    exact ⟨s, hs.trans (hnorm s).symm⟩
  · obtain ⟨s, hs⟩ := h c ((hfix c).mpr hc)
    exact ⟨s, hs.trans (hnorm s)⟩

end CFSG.StandardType

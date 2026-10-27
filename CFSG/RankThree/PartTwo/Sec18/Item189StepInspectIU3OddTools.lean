module

public import CFSG.LieType.Steinberg.CentralExt.SUThree

public section

namespace CFSG.RankThree.PartTwo.Sec18

open Matrix CFSG.LieType.Steinberg

section Group

variable {G : Type*} [Group G] [Finite G]

theorem eq_one_of_sylow_u3odd189 {W : Subgroup G}
    (hW : Nat.card W = 2 ^ (Nat.card G).factorization 2)
    (h : ∀ y ∈ Subgroup.normalizer (W : Set G), y ^ 3 = 1 → y = 1)
    (T : Sylow 2 G) {y : G} (hy : y ∈ Subgroup.normalizer ((T : Subgroup G) : Set G))
    (hy3 : y ^ 3 = 1) : y = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (Sylow.ofCard W hW) T
  have hT : (T : Subgroup G) = W.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  rw [hT, ← Subgroup.map_equiv_normalizer_eq] at hy
  obtain ⟨y', hy', rfl⟩ := hy
  have h3 : y' ^ 3 = 1 := by
    apply (MulAut.conj g).injective
    rw [map_pow, map_one]
    exact hy3
  rw [h y' hy' h3, map_one]

theorem eq_one_of_mulEquiv_u3odd189 {H : Type*} [Group H] (e : G ≃* H)
    (h : ∀ T : Sylow 2 H, ∀ y ∈ Subgroup.normalizer ((T : Subgroup H) : Set H), y ^ 3 = 1 →
      y = 1)
    (T : Sylow 2 G) {y : G} (hy : y ∈ Subgroup.normalizer ((T : Subgroup G) : Set G))
    (hy3 : y ^ 3 = 1) : y = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite H := Finite.of_equiv _ e.toEquiv
  have hcard : Nat.card ((T : Subgroup G).map e.toMonoidHom) =
      2 ^ (Nat.card H).factorization 2 := by
    rw [Subgroup.card_map_of_injective e.injective, T.card_eq_multiplicity,
      Nat.card_congr e.toEquiv]
  have hy' : e y ∈ Subgroup.normalizer
      (((Sylow.ofCard _ hcard : Sylow 2 H) : Subgroup H) : Set H) := by
    rw [Sylow.coe_ofCard, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.mem_map_of_mem _ hy
  have h1 := h _ (e y) hy' (by rw [← map_pow, hy3, map_one])
  exact e.injective (by rw [h1, map_one])

end Group

theorem eq_one_of_pow_three_u3odd189 {M : Type*} [Monoid M] {q : ℕ} (hq : q % 3 = 1) {c : M}
    (h3 : c ^ 3 = 1) (hn : c ^ q * c = 1) : c = 1 := by
  have hcq : c ^ q = c := by
    rw [← Nat.div_add_mod q 3, hq, pow_add, pow_mul, h3, one_pow, one_mul, pow_one]
  rw [hcq] at hn
  calc c = c * (c * c) := by rw [hn, mul_one]
    _ = c ^ 3 := by rw [pow_three]
    _ = 1 := h3

theorem injective_vec_three_u3odd189 {K : Type*} {a b c : K} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : Function.Injective ![a, b, c] := by
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | (exfalso; revert h; simp [hab, hac, hbc, hab.symm, hac.symm, hbc.symm])

section Diag

variable {K : Type*} [Field K] {n : ℕ}

theorem diagGL_pow_u3odd189 (d : Fin n → Kˣ) (m : ℕ) : diagGL d ^ m = diagGL (d ^ m) := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, coe_diagGL, coe_diagGL, diagonal_pow]
  congr 1

theorem diagGL_mul_u3odd189 (d e : Fin n → Kˣ) : diagGL d * diagGL e = diagGL (d * e) := by
  refine Units.ext ?_
  rw [Units.val_mul, coe_diagGL, coe_diagGL, coe_diagGL, diagonal_mul_diagonal]
  congr 1

end Diag

end CFSG.RankThree.PartTwo.Sec18

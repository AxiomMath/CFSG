module

public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagUnitary

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace TableB.TwE6

theorem exists_mul_inv_pow_eq_cube {G : Type*} [Group G] [IsCyclic G] {x' : G}
    (hx' : ¬ ∃ y : G, y ^ 3 = x') (x : G) : ∃ (k : ℕ) (y : G), x * (x' ^ k)⁻¹ = y ^ 3 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x')
  have hj : ¬ (3 : ℤ) ∣ j := by
    rintro ⟨l, rfl⟩
    refine hx' ⟨g ^ l, ?_⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
    rfl
  have key : ∃ k : ℕ, (3 : ℤ) ∣ i - j * k := by
    have h1 : j % 3 = 1 ∨ j % 3 = 2 := by omega
    have h2 : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 | h2
    · exact ⟨0, by push_cast; omega⟩
    · exact ⟨1, by push_cast; omega⟩
    · exact ⟨2, by push_cast; omega⟩
    · exact ⟨0, by push_cast; omega⟩
    · exact ⟨2, by push_cast; omega⟩
    · exact ⟨1, by push_cast; omega⟩
  obtain ⟨k, m, hm⟩ := key
  refine ⟨k, g ^ m, ?_⟩
  rw [← zpow_natCast (g ^ j) k, ← zpow_mul, ← zpow_neg, ← zpow_add, ← zpow_natCast, ← zpow_mul]
  congr 1
  push_cast
  linarith

variable {K : Type} [Field K]

theorem cartanChar_eq (s : Fin 6 → Kˣ) :
    cartanChar (τ := Tag.E6) s = ![s 0 ^ 2 * (s 2)⁻¹, s 1 ^ 2 * (s 3)⁻¹,
      (s 0)⁻¹ * s 2 ^ 2 * (s 3)⁻¹, (s 1)⁻¹ * (s 2)⁻¹ * s 3 ^ 2 * (s 4)⁻¹,
      (s 3)⁻¹ * s 4 ^ 2 * (s 5)⁻¹, (s 4)⁻¹ * s 5 ^ 2] := by
  have h : cartanChar (τ := Tag.E6) s =
      fun l : Fin 6 => ∏ j : Fin 6, s j ^ LargeEvenCartanE 6 j l := rfl
  rw [h]
  funext l
  rw [Fin.prod_univ_six]
  fin_cases l <;> simp [LargeEvenCartanE]

@[expose] def cartanHom : (Fin 6 → Kˣ) →* (Fin 6 → Kˣ) where
  toFun s := fun l => ∏ j, s j ^ LargeEvenCartanE 6 j l
  map_one' := by
    funext l
    simp
  map_mul' s t := by
    funext l
    simp [mul_zpow, Finset.prod_mul_distrib]

theorem cartanHom_apply (s : Fin 6 → Kˣ) : cartanHom s = cartanChar (τ := Tag.E6) s :=
  rfl

theorem cartanHom_eq (s : Fin 6 → Kˣ) :
    cartanHom s = ![s 0 ^ 2 * (s 2)⁻¹, s 1 ^ 2 * (s 3)⁻¹,
      (s 0)⁻¹ * s 2 ^ 2 * (s 3)⁻¹, (s 1)⁻¹ * (s 2)⁻¹ * s 3 ^ 2 * (s 4)⁻¹,
      (s 3)⁻¹ * s 4 ^ 2 * (s 5)⁻¹, (s 4)⁻¹ * s 5 ^ 2] :=
  cartanChar_eq s

theorem rhoE6_values : LargeEvenRhoE6 0 = 5 ∧ LargeEvenRhoE6 1 = 1 ∧ LargeEvenRhoE6 2 = 4 ∧
    LargeEvenRhoE6 3 = 3 ∧ LargeEvenRhoE6 4 = 2 ∧ LargeEvenRhoE6 5 = 0 := by
  decide

variable (σ : K →+* K)

@[expose] def compat : Subgroup (Fin 6 → Kˣ) where
  carrier := {b | ∀ i, b (LargeEvenRhoE6 i) = Units.map σ.toMonoidHom (b i)}
  mul_mem' {a b} ha hb i := by
    rw [Pi.mul_apply, Pi.mul_apply, ha i, hb i, map_mul]
  one_mem' i := by
    simp
  inv_mem' {a} ha i := by
    rw [Pi.inv_apply, Pi.inv_apply, ha i, map_inv]

theorem mem_compat {b : Fin 6 → Kˣ} :
    b ∈ compat σ ↔ ∀ i, b (LargeEvenRhoE6 i) = Units.map σ.toMonoidHom (b i) :=
  Iff.rfl

@[expose] def torus₀ : Subgroup (Fin 6 → Kˣ) :=
  (compat σ).map cartanHom

@[expose] def edge : Kˣ →* (Fin 6 → Kˣ) where
  toFun x := ![x, 1, 1, 1, 1, Units.map σ.toMonoidHom x]
  map_one' := by
    funext i
    fin_cases i <;> simp
  map_mul' x y := by
    funext i
    fin_cases i <;> simp

theorem edge_apply (x : Kˣ) : edge σ x = ![x, 1, 1, 1, 1, Units.map σ.toMonoidHom x] :=
  rfl

variable {σ}

theorem units_map_map (hσσ : ∀ c, σ (σ c) = c) (y : Kˣ) :
    Units.map σ.toMonoidHom (Units.map σ.toMonoidHom y) = y :=
  Units.ext (hσσ y)

theorem sigma_sigma [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q)
    (c : K) : σ (σ c) = c := by
  have : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card] at hK
  rw [hσ, hσ, ← pow_mul, ← sq, ← hK]
  exact FiniteField.pow_card c

theorem edge_pow_three_mem (hσσ : ∀ c, σ (σ c) = c) (y : Kˣ) : edge σ (y ^ 3) ∈ torus₀ σ := by
  refine ⟨![y ^ 4 * Units.map σ.toMonoidHom y ^ 2, y ^ 3 * Units.map σ.toMonoidHom y ^ 3,
    y ^ 5 * Units.map σ.toMonoidHom y ^ 4, y ^ 6 * Units.map σ.toMonoidHom y ^ 6,
    y ^ 4 * Units.map σ.toMonoidHom y ^ 5, y ^ 2 * Units.map σ.toMonoidHom y ^ 4],
    fun i => ?_, ?_⟩
  · fin_cases i <;> (apply Units.ext; simp [rhoE6_values, hσσ]; try ring)
  · rw [cartanHom_eq, edge_apply]
    funext l
    fin_cases l <;> (apply Units.ext; simp; try field_simp)

theorem exists_mul_edge_inv_mem [Finite K] {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 2)
    (hσ : ∀ c, σ c = c ^ q) {b : Fin 6 → Kˣ} (hb : b ∈ compat σ) :
    ∃ x : Kˣ, b * (edge σ x)⁻¹ ∈ torus₀ σ := by
  have hσσ := sigma_sigma hK hσ
  obtain ⟨h0, h1, h2, h3, -, -⟩ := rhoE6_values
  have hb0 := hb 0
  have hb1 := hb 1
  have hb2 := hb 2
  have hb3 := hb 3
  rw [h0] at hb0
  rw [h1] at hb1
  rw [h2] at hb2
  rw [h3] at hb3
  have hb1' : σ (b 1 : K) = b 1 := (congrArg Units.val hb1).symm
  have hb3' : σ (b 3 : K) = b 3 := (congrArg Units.val hb3).symm
  have hwq : (((b 1 ^ 2 * b 3)⁻¹ : Kˣ) : K) ^ q = ((b 1 ^ 2 * b 3)⁻¹ : Kˣ) := by
    rw [← hσ]
    simp [hb1', hb3']
  obtain ⟨z, hz⟩ := exists_norm_eq hq hK (Units.ne_zero _) hwq
  have hzσ : (z : K) * σ z * ((b 1 : K) ^ 2 * b 3) = 1 := by
    rw [hσ, ← pow_succ', hz]
    simp only [Units.val_inv_eq_inv_val, Units.val_mul, Units.val_pow_eq_pow_val]
    field_simp
  refine ⟨b 0 * ((z ^ 2 * b 1 * (b 2)⁻¹) ^ 2 * z⁻¹)⁻¹, ![z ^ 2 * b 1 * (b 2)⁻¹, 1, z, (b 1)⁻¹,
    Units.map σ.toMonoidHom z, Units.map σ.toMonoidHom (z ^ 2 * b 1 * (b 2)⁻¹)],
    fun i => ?_, ?_⟩
  · fin_cases i <;> (apply Units.ext; simp [rhoE6_values, hσσ, hb1'])
  · rw [cartanHom_eq, edge_apply]
    funext l
    fin_cases l
    · apply Units.ext
      simp
    · apply Units.ext
      simp
    · apply Units.ext
      simp
      field_simp
    · apply Units.ext
      simp
      field_simp
      linear_combination -hzσ
    · apply Units.ext
      simp [hb1', hb2]
      field_simp
    · apply Units.ext
      simp [hb1', hb0]
      field_simp

theorem exists_mul_inv_pow_mem [Finite K] {q : ℕ} (hq : 2 ≤ q) (hK : Nat.card K = q ^ 2)
    (hσ : ∀ c, σ c = c ^ q) {a a' : Fin 6 → Kˣ} (ha : a ∈ compat σ) (ha' : a' ∈ compat σ)
    (hn : a' ∉ torus₀ σ) : ∃ k : ℕ, a * (a' ^ k)⁻¹ ∈ torus₀ σ := by
  have hσσ := sigma_sigma hK hσ
  set π := QuotientGroup.mk' (torus₀ σ)
  have hker : ∀ c, π c = 1 ↔ c ∈ torus₀ σ := fun c => QuotientGroup.eq_one_iff c
  obtain ⟨x, hx⟩ := exists_mul_edge_inv_mem hq hK hσ ha
  obtain ⟨x', hx'⟩ := exists_mul_edge_inv_mem hq hK hσ ha'
  have e : ∀ {c : Fin 6 → Kˣ} {y : Kˣ}, c * (edge σ y)⁻¹ ∈ torus₀ σ →
      π c = π (edge σ y) := by
    intro c y h
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, hker]
    exact h
  have hcube : ∀ y : Kˣ, π (edge σ (y ^ 3)) = 1 := fun y => (hker _).2 (edge_pow_three_mem hσσ y)
  have hx'c : ¬ ∃ y : Kˣ, y ^ 3 = x' := by
    rintro ⟨y, rfl⟩
    exact hn ((hker _).1 (by rw [e hx', hcube]))
  obtain ⟨k, y, hk⟩ := exists_mul_inv_pow_eq_cube hx'c x
  refine ⟨k, (hker _).1 ?_⟩
  have hπe : π (edge σ x) * (π (edge σ x') ^ k)⁻¹ = π (edge σ (x * (x' ^ k)⁻¹)) := by
    simp only [map_mul, map_inv, map_pow]
  rw [map_mul, map_inv, map_pow, e hx, e hx', hπe, hk, hcube]

end TableB.TwE6

end CFSG.StandardType

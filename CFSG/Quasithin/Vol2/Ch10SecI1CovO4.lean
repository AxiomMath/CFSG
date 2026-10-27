module

public import CFSG.Quasithin.Vol2.Ch10SecI1CovNat

public section

noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ASInputs.C10KH

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit
open CFSG.Assembly.LowTwoRank Matrix

theorem exists_pow_ne_self' {k : Type} [Field k] [Finite k] {n : ℕ} (hn : 1 < n)
    (hk : Nat.card k = n ^ 2) : ∃ u : k, u ^ n ≠ u := by
  classical
  by_contra h
  push Not at h
  have := Fintype.ofFinite k
  have hcard : Fintype.card k = n ^ 2 := by rw [← Nat.card_eq_fintype_card, hk]
  have hdeg : (Polynomial.X ^ n - Polynomial.X : Polynomial k).natDegree = n :=
    FiniteField.X_pow_card_sub_X_natDegree_eq k hn
  have hne : (Polynomial.X ^ n - Polynomial.X : Polynomial k) ≠ 0 := fun h0 => by
    rw [h0, Polynomial.natDegree_zero] at hdeg
    omega
  have hsub : (Finset.univ : Finset k).val ⊆
      (Polynomial.X ^ n - Polynomial.X : Polynomial k).roots := fun u _ => by
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, h u, sub_self]
  have := Polynomial.card_le_degree_of_subset_roots hsub
  rw [Finset.card_univ, hcard, hdeg] at this
  nlinarith

section Polar

variable {K : Type} [Field K]

@[expose] def detPolar (X Y : Matrix (Fin 2) (Fin 2) K) : K := (X + Y).det - X.det - Y.det

theorem detPolar_eq (X Y : Matrix (Fin 2) (Fin 2) K) :
    detPolar X Y = X 0 0 * Y 1 1 + Y 0 0 * X 1 1 - X 0 1 * Y 1 0 - Y 0 1 * X 1 0 := by
  simp only [detPolar, det_fin_two, Matrix.add_apply]
  ring

theorem detPolar_add_left (X Y Z : Matrix (Fin 2) (Fin 2) K) :
    detPolar (X + Y) Z = detPolar X Z + detPolar Y Z := by
  simp only [detPolar_eq, Matrix.add_apply]
  ring

theorem detPolar_add_right (X Y Z : Matrix (Fin 2) (Fin 2) K) :
    detPolar X (Y + Z) = detPolar X Y + detPolar X Z := by
  simp only [detPolar_eq, Matrix.add_apply]
  ring

theorem detPolar_smul_right (X Y : Matrix (Fin 2) (Fin 2) K) (t : K) :
    detPolar X (t • Y) = t * detPolar X Y := by
  simp only [detPolar_eq, Matrix.smul_apply, smul_eq_mul]
  ring

theorem detPolar_zero_left (Y : Matrix (Fin 2) (Fin 2) K) : detPolar 0 Y = 0 := by
  simp only [detPolar_eq, Matrix.zero_apply]
  ring

theorem detPolar_zero_right (X : Matrix (Fin 2) (Fin 2) K) : detPolar X 0 = 0 := by
  simp only [detPolar_eq, Matrix.zero_apply]
  ring

@[expose] def hermPair (ℓ : K →+ ZMod 2) (X Y : Multiplicative (Matrix (Fin 2) (Fin 2) K)) :
    ZMod 2 :=
  ℓ (detPolar (Multiplicative.toAdd X) (Multiplicative.toAdd Y))

theorem hermPair_mul_left (ℓ : K →+ ZMod 2) (X Y Z : Multiplicative (Matrix (Fin 2) (Fin 2) K)) :
    hermPair ℓ (X * Y) Z = hermPair ℓ X Z + hermPair ℓ Y Z := by
  simp only [hermPair, toAdd_mul, detPolar_add_left, map_add]

theorem hermPair_mul_right (ℓ : K →+ ZMod 2) (X Y Z : Multiplicative (Matrix (Fin 2) (Fin 2) K)) :
    hermPair ℓ X (Y * Z) = hermPair ℓ X Y + hermPair ℓ X Z := by
  simp only [hermPair, toAdd_mul, detPolar_add_right, map_add]

theorem hermPair_one_left (ℓ : K →+ ZMod 2) (Y : Multiplicative (Matrix (Fin 2) (Fin 2) K)) :
    hermPair ℓ 1 Y = 0 := by
  simp only [hermPair, toAdd_one, detPolar_zero_left, map_zero]

theorem hermPair_one_right (ℓ : K →+ ZMod 2) (X : Multiplicative (Matrix (Fin 2) (Fin 2) K)) :
    hermPair ℓ X 1 = 0 := by
  simp only [hermPair, toAdd_one, detPolar_zero_right, map_zero]

variable [CharP K 2]

theorem hermPair_secPairing (ℓ : K →+ ZMod 2) (a : ℕ) :
    SecPairing (FFModel.twistTensor a (StatedSL 2 K)) (hermPair ℓ) where
  add_left := hermPair_mul_left ℓ
  add_right := hermPair_mul_right ℓ
  ker_left k hk y _ := by
    have hk1 : k = 1 := hk
    rw [hk1]
    exact hermPair_one_left ℓ y
  ker_right x _ k hk := by
    have hk1 : k = 1 := hk
    rw [hk1]
    exact hermPair_one_right ℓ x

theorem hermPair_invariant (ℓ : K →+ ZMod 2) (a : ℕ) (g : ↥(StatedSL 2 K))
    (X Y : Multiplicative (Matrix (Fin 2) (Fin 2) K)) :
    hermPair ℓ (twistAct a (StatedSL 2 K) g X) (twistAct a (StatedSL 2 K) g Y) =
      hermPair ℓ X Y := by
  have hd : ∀ M : Multiplicative (Matrix (Fin 2) (Fin 2) K),
      (Multiplicative.toAdd (twistAct a (StatedSL 2 K) g M)).det = (Multiplicative.toAdd M).det :=
    fun M => hermDet_twistAct g (Multiplicative.toAdd M)
  simp only [hermPair, detPolar]
  rw [← toAdd_mul, ← toAdd_mul, ← twistAct_mul, hd, hd, hd]

end Polar

section O4Cover

variable {K : Type} [Field K] [CharP K 2]

theorem mem_hermSub_iff {a : ℕ} (M : Matrix (Fin 2) (Fin 2) K) :
    Multiplicative.ofAdd M ∈ hermSub a (Fin 2) K ↔ ∀ i j, M j i ^ 2 ^ a = M i j := by
  change (frobPow a M)ᵀ = M ↔ _
  constructor
  · intro h i j
    have h1 := congrFun (congrFun h i) j
    simpa only [frobPow, transpose_apply, map_apply] using h1
  · intro h
    ext i j
    simp only [frobPow, transpose_apply, map_apply]
    exact h i j

theorem hermPair_nondeg [Finite K] {a : ℕ} (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a))
    {ℓ : K →+ ZMod 2} (hℓ : ℓ 1 = 1) {X : Multiplicative (Matrix (Fin 2) (Fin 2) K)}
    (hX : X ∈ hermSub a (Fin 2) K) (h : ∀ Y ∈ hermSub a (Fin 2) K, hermPair ℓ X Y = 0) :
    X = 1 := by
  set A := Multiplicative.toAdd X with hA
  have hq0 : 2 ^ a ≠ 0 := pow_ne_zero a two_ne_zero
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hσσ : ∀ x : K, (x ^ 2 ^ a) ^ 2 ^ a = x := by
    intro x
    have : Fintype K := Fintype.ofFinite K
    rw [← pow_mul, ← pow_add, ← two_mul, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hXh : ∀ i j, A j i ^ 2 ^ a = A i j := (mem_hermSub_iff A).mp hX
  have hfix : ∀ M : Matrix (Fin 2) (Fin 2) K, (∀ i j, M j i ^ 2 ^ a = M i j) →
      M.det ^ 2 ^ a = M.det := fun M hM => hermDet_pow ((mem_hermSub_iff M).mpr hM)
  have hz : ∀ Y : Matrix (Fin 2) (Fin 2) K, (∀ i j, Y j i ^ 2 ^ a = Y i j) →
      detPolar A Y = 0 := by
    intro Y hY
    by_contra hp
    set p := detPolar A Y with hpdef
    have hAY : ∀ i j, (A + Y) j i ^ 2 ^ a = (A + Y) i j := fun i j => by
      rw [Matrix.add_apply, Matrix.add_apply, add_pow_char_pow, hXh, hY]
    have hpq : p ^ 2 ^ a = p := by
      rw [hpdef, detPolar, sub_pow_char_pow, sub_pow_char_pow, hfix _ hAY, hfix _ hXh, hfix _ hY]
    have hY' : ∀ i j, (p⁻¹ • Y) j i ^ 2 ^ a = (p⁻¹ • Y) i j := fun i j => by
      rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, mul_pow, inv_pow, hpq,
        hY]
    have h1 := h (Multiplicative.ofAdd (p⁻¹ • Y)) ((mem_hermSub_iff _).mpr hY')
    rw [hermPair, toAdd_ofAdd, ← hA, detPolar_smul_right, ← hpdef, inv_mul_cancel₀ hp, hℓ] at h1
    exact one_ne_zero h1
  have h11 : A 1 1 = 0 := by
    have h1 := hz !![1, 0; 0, 0] (by intro i j; fin_cases i <;> fin_cases j <;> simp)
    simpa [detPolar_eq] using h1
  have h00 : A 0 0 = 0 := by
    have h1 := hz !![0, 0; 0, 1] (by intro i j; fin_cases i <;> fin_cases j <;> simp)
    simpa [detPolar_eq] using h1
  have h01 : A 0 1 = 0 := by
    by_contra hu
    have hcard : Nat.card K = (2 ^ a) ^ 2 := by rw [hK, ← pow_mul, mul_comm]
    obtain ⟨s, hs⟩ := exists_pow_ne_self' (k := K) (n := 2 ^ a) (Nat.one_lt_two_pow (by omega))
      hcard
    have htq : ((s / A 0 1) ^ 2 ^ a) ^ 2 ^ a = s / A 0 1 := hσσ _
    have h1 := hz !![0, (s / A 0 1) ^ 2 ^ a; s / A 0 1, 0] (by
      intro i j
      fin_cases i <;> fin_cases j <;> simp [htq])
    rw [detPolar_eq] at h1
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
      mul_zero, zero_mul, add_zero, zero_sub] at h1
    have e1 : A 0 1 * (s / A 0 1) = s := mul_div_cancel₀ s hu
    have e2 : (s / A 0 1) ^ 2 ^ a * A 1 0 = s ^ 2 ^ a := by
      rw [← hXh 1 0, ← mul_pow, div_mul_cancel₀ s hu]
    rw [e1, e2] at h1
    exact hs (by linear_combination -h1 - s * h2)
  have h10 : A 1 0 = 0 := by
    rw [← hXh 1 0, h01, zero_pow hq0]
  apply Multiplicative.toAdd.injective
  change A = 0
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

variable [Finite K] {W : Type} [CommGroup W] [Finite W]

theorem orth4Cover_card_le {a : ℕ} (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a))
    (hW2 : ∀ w : W, w ^ 2 = 1) {Gm : Subgroup (MulAut W)} {Z : Subgroup W}
    (hZ : Z ≤ fixV Gm) (hcomm : commV Gm = ⊤)
    (hR : (FFModel.twistTensor a (StatedSL 2 K)).Realizes Gm ⊤ Z) {d : ℕ}
    (hH1 : ∀ {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
      (ρ : Representation (ZMod 2) (FFModel.twistTensor a (StatedSL 2 K)).Gam M),
        (FFModel.twistTensor a (StatedSL 2 K)).IsModel ρ → Module.finrank (ZMod 2) (H1 ρ) ≤ d) :
    Nat.card Z ≤ 2 ^ d := by
  obtain ⟨ℓ, hℓ⟩ := exists_addHom_one K
  have : Finite (FFModel.twistTensor a (StatedSL 2 K)).Gam :=
    inferInstanceAs (Finite ↥(StatedSL 2 K))
  exact cover_card_le_of_form hW2 hZ hcomm hR (FFModel.twistTensor_isActionModel a _ hK)
    (sec_sq_eq_one fun x => sq_eq_one_of_charTwo (K := K) (A := Matrix (Fin 2) (Fin 2) K) x)
    (hermPair_secPairing ℓ a)
    (fun x hx h => Subgroup.mem_bot.mpr (hermPair_nondeg ha hK hℓ hx h))
    (fun γ x _ y _ => hermPair_invariant ℓ a γ x y) hH1

end O4Cover

end CFSG.Quasithin.ASInputs.C10KH

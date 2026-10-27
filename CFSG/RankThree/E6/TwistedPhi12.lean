module

public import CFSG.RankThree.E6.CoxeterSquareEisensteinLines

public noncomputable section

namespace CFSG.RankThree.E6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def phi12Matrix : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ := -weylMatrix e6Coxeter

@[expose] def phi12Matrix6 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  (!![0, -1, 0, 0, 0, 1; 0, 0, -1, 0, 0, 1; -1, -1, 0, 0, 0, 1; 0, -1, -1, 0, 0, 1;
    0, 0, 0, -1, 0, 1; 0, 0, 0, 0, -1, 1] : Matrix (Fin 6) (Fin 6) ℤ)

theorem weylMatrix_e6Coxeter : weylMatrix e6Coxeter = -phi12Matrix6 :=
  weylMatrix_wordProd_e6 (by decide +kernel)

theorem phi12Matrix_eq : phi12Matrix = phi12Matrix6 := by
  rw [phi12Matrix, weylMatrix_e6Coxeter, neg_neg]

theorem phi12Matrix_poly :
    phi12Matrix ^ 6 - phi12Matrix ^ 5 + phi12Matrix ^ 3 - phi12Matrix + 1 = 0 := by
  rw [phi12Matrix_eq]
  decide +kernel

@[expose] def phi12VWord : List (Fin 6) :=
  [2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3, 2, 1]

theorem weylMatrix_phi12V :
    weylMatrix ((coxeterSystem Tag.E6).wordProd (e6Word phi12VWord)) =
      -(weylMatrix e6Coxeter * rhoMatrix) := by
  rw [weylMatrix_e6Coxeter]
  exact weylMatrix_wordProd_e6 (by decide +kernel)

theorem exists_weyl_eq_neg_coxeter_rho : ∃ v : WeylGroup Tag.E6, ∀ x : Fin Tag.E6.rank → ℤ,
    v • x = -(e6Coxeter • permLattice e6Rho x) := by
  refine ⟨(coxeterSystem Tag.E6).wordProd (e6Word phi12VWord), fun x => ?_⟩
  rw [← weylMatrix_mulVec, weylMatrix_phi12V, permLattice_eq_mulVec, ← weylMatrix_mulVec,
    Matrix.mulVec_mulVec, Matrix.neg_mulVec]

@[expose] def phi12OrbitBasis : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  Matrix.of fun i j => ((phi12Matrix ^ (j : ℕ)).mulVec (Pi.single (e6Index 0) 1)) i

@[expose] def phi12OrbitBasis6 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  (!![1, 0, 0, -1, 0, 0; 0, 0, 1, 0, 1, 0; 0, -1, 0, -1, 1, 0; 0, 0, 1, -1, 1, -1;
    0, 0, 0, -1, 1, 0; 0, 0, 0, 0, 1, 0] : Matrix (Fin 6) (Fin 6) ℤ)

@[expose] def phi12OrbitBasisInv6 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  (!![1, 0, 0, 0, -1, 1; 0, 0, -1, 0, 1, 0; 0, 1, 0, 0, 0, -1; 0, 0, 0, 0, -1, 1;
    0, 0, 0, 0, 0, 1; 0, 1, 0, -1, 1, -1] : Matrix (Fin 6) (Fin 6) ℤ)

theorem phi12OrbitBasis_eq : phi12OrbitBasis = phi12OrbitBasis6 := by
  rw [phi12OrbitBasis, phi12Matrix_eq]
  decide +kernel

theorem det_phi12OrbitBasis : phi12OrbitBasis.det = 1 := by
  rw [phi12OrbitBasis_eq, ← detLaplace_eq_det]
  decide +kernel

theorem phi12OrbitBasis_mul_inv :
    phi12OrbitBasis * phi12OrbitBasisInv6 = 1 := by
  rw [phi12OrbitBasis_eq]
  decide +kernel

@[expose] def phi12Seed : Fin 6 → Fin Tag.E6.rank → ℤ :=
  (![![-1, -2, -2, -3, -2, -1], ![-1, -1, -2, -2, -2, -1], ![-1, -1, -1, -2, -1, -1],
    ![-1, -1, -1, -2, -1, 0], ![-1, -1, -1, -1, -1, -1], ![-1, 0, -1, -1, -1, -1]] :
    Fin 6 → Fin 6 → ℤ)

@[expose] def phi12SeedPoly : Fin 6 → Fin Tag.E6.rank → ℤ :=
  (![![0, 0, -1, 1, -1, 0], ![0, 0, 0, 1, -1, 0], ![-1, 0, 0, 0, -1, 1], ![0, 0, -1, 1, 0, 0],
    ![-1, 0, 0, 0, -1, 0], ![-1, 0, 1, 0, -1, 1]] : Fin 6 → Fin 6 → ℤ)

theorem phi12Seed_eq : ∀ i : Fin 6,
    phi12OrbitBasis6.mulVec (phi12SeedPoly i) = phi12Seed i := by
  decide +kernel

@[expose] def phi12OrbitIndex : Fin 72 → Fin 6 × Fin 12 := fun m =>
  ((![
    4, 2, 5, 5, 4, 5, 5, 1, 2, 4, 4, 4, 4, 3, 5, 1, 4, 3, 2, 5, 3, 5, 5, 2, 1, 0, 3, 2, 0, 5, 1,
    4, 2, 2, 2, 1, 0, 0, 4, 1, 4, 2, 2, 1, 4, 3, 3, 5, 1, 5, 3, 5, 1, 3, 4, 0, 2, 3, 0, 0, 2, 3,
    3, 0, 1, 1, 3, 1, 0, 0, 0, 0] : Fin 72 → Fin 6) m,
  (![
    4, 9, 2, 6, 10, 8, 1, 9, 3, 6, 5, 1, 9, 3, 7, 3, 11, 10, 4, 3, 11, 11, 10, 1, 2, 3, 4, 10,
    4, 4, 10, 2, 11, 8, 7, 8, 9, 10, 7, 4, 3, 5, 2, 6, 8, 9, 5, 0, 11, 9, 7, 5, 1, 0, 0, 11, 6,
    2, 8, 5, 0, 6, 8, 2, 5, 7, 1, 0, 1, 7, 6, 0] : Fin 72 → Fin 12) m)

theorem phi12_orbit : ∀ m : Fin 72,
    (phi12Matrix6 ^ ((phi12OrbitIndex m).2 : ℕ)).mulVec (phi12Seed (phi12OrbitIndex m).1) =
      e6RootVec m := by
  decide +kernel

theorem natCast_ne_zero_of_two {p : ℕ} [Fact p.Prime] (hp : 3 < p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℤ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
  have := Int.le_of_dvd (by norm_num) h'
  omega

section Regular

variable {R : Type*} [CommRing R]

theorem phi12SeedPoly_eval (a : R) (i : Fin 6) :
    ∑ j : Fin Tag.E6.rank, ((phi12SeedPoly i j : ℤ) : R) * a ^ (j : ℕ) =
      (![-a ^ 2 + a ^ 3 - a ^ 4, a ^ 3 - a ^ 4, -1 - a ^ 4 + a ^ 5, -a ^ 2 + a ^ 3, -1 - a ^ 4,
        -1 + a ^ 2 - a ^ 4 + a ^ 5] : Fin 6 → R) i := by
  change ∑ j : Fin 6, _ = _
  fin_cases i <;> simp [Fin.sum_univ_six, phi12SeedPoly] <;> ring

theorem phi12SeedPoly_eval_ne_zero [Nontrivial R] (h2 : (2 : R) ≠ 0) {a : R}
    (ha : a ^ 4 - a ^ 2 + 1 = 0) (i : Fin 6) :
    ∑ j : Fin Tag.E6.rank, ((phi12SeedPoly i j : ℤ) : R) * a ^ (j : ℕ) ≠ 0 := by
  rw [phi12SeedPoly_eval]
  intro h0
  fin_cases i
  ·
    apply h2
    change -a ^ 2 + a ^ 3 - a ^ 4 = 0 at h0
    linear_combination (-1 + 2 * a ^ 2 + a ^ 3) * h0 - (-2 - a ^ 2 - a ^ 3) * ha
  ·
    apply one_ne_zero (α := R)
    change a ^ 3 - a ^ 4 = 0 at h0
    linear_combination (1 + a - a ^ 3) * h0 - (-1 - a ^ 2 + a ^ 3) * ha
  ·
    apply h2
    change -1 - a ^ 4 + a ^ 5 = 0 at h0
    linear_combination (-1 - a + a ^ 2) * h0 - (-1 + a - 2 * a ^ 2 + a ^ 3) * ha
  ·
    apply one_ne_zero (α := R)
    change -a ^ 2 + a ^ 3 = 0 at h0
    linear_combination (-1 - a) * h0 + ha
  ·
    apply one_ne_zero (α := R)
    change -1 - a ^ 4 = 0 at h0
    linear_combination (-1 + a ^ 2) * h0 + a ^ 2 * ha
  ·
    apply one_ne_zero (α := R)
    change -1 + a ^ 2 - a ^ 4 + a ^ 5 = 0 at h0
    linear_combination (-a) * h0 - (-1 + a - a ^ 2) * ha

theorem charVal_ne_zero_of_phi12 [IsDomain R] (h2 : (2 : R) ≠ 0) {a : R}
    (ha : a ^ 4 - a ^ 2 + 1 = 0) {z : Fin Tag.E6.rank → R} (hz : z ≠ 0)
    (hu : ((phi12Matrix.map (Int.cast : ℤ → R)).transpose).mulVec z = a • z)
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) : charVal z α ≠ 0 := by
  have hpow := charVal_pow_mulVec_of_eigen hu
  have ha0 : a ≠ 0 := by
    intro h
    rw [h] at ha
    simp at ha
  have he1 : charVal z (Pi.single (e6Index 0) 1) ≠ 0 := by
    intro h0
    apply hz
    refine eq_zero_of_charVal_columns phi12OrbitBasis_mul_inv fun j => ?_
    change charVal z ((phi12Matrix ^ (j : ℕ)).mulVec (Pi.single (e6Index 0) 1)) = 0
    rw [hpow, h0, mul_zero]
  have hseed : ∀ i : Fin 6, charVal z (phi12Seed i) ≠ 0 := by
    intro i
    rw [← phi12Seed_eq i, ← phi12OrbitBasis_eq, charVal_mulVec_eq_sum]
    have e : ∀ j : Fin Tag.E6.rank, charVal z (fun l => phi12OrbitBasis l j) =
        a ^ (j : ℕ) * charVal z (Pi.single (e6Index 0) 1) := fun j => hpow _ _
    simp only [e, ← mul_assoc, ← Finset.sum_mul]
    exact mul_ne_zero (phi12SeedPoly_eval_ne_zero h2 ha i) he1
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hα
  rw [← phi12_orbit m, ← phi12Matrix_eq, hpow]
  exact mul_ne_zero (pow_ne_zero _ ha0) (hseed _)

end Regular

end CFSG.RankThree.E6

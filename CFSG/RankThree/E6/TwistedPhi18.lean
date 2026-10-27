module

public import CFSG.RankThree.E6.RootLatticeTools
public import CFSG.Timmesfeld.Orders.ExceptionalWeyl

public noncomputable section

namespace CFSG.RankThree.E6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.ExceptionalOrders Polynomial

@[expose] def phi18Word : List (Fin 6) := [0, 2, 3, 1]

@[expose] def phi18Matrix : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  weylMatrix ((coxeterSystem Tag.E6).wordProd (e6Word phi18Word)) * rhoMatrix

theorem phi18Matrix_mulVec (x : Fin Tag.E6.rank → ℤ) :
    phi18Matrix.mulVec x =
      (coxeterSystem Tag.E6).wordProd (e6Word phi18Word) • permLattice e6Rho x := by
  rw [phi18Matrix, ← Matrix.mulVec_mulVec, weylMatrix_mulVec, permLattice_eq_mulVec]

@[expose] def phi18Matrix6 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  (!![0, -1, 1, 0, 0, 0; 0, -1, 0, 1, 0, 0; 0, -1, 1, 0, 0, 1; 0, -1, 1, 0, 1, 0;
    0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 0, 0] : Matrix (Fin 6) (Fin 6) ℤ)

@[expose] def phi18WordMatrix6 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  (!![0, -1, 0, 0, 1, 0; 0, -1, 0, 1, 0, 0; 1, -1, 0, 0, 1, 0; 0, -1, 1, 0, 1, 0;
    0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1] : Matrix (Fin 6) (Fin 6) ℤ)

theorem phi18Matrix_eq : phi18Matrix = phi18Matrix6 := by
  rw [phi18Matrix, weylMatrix_wordProd_e6 (M := phi18WordMatrix6) (by decide +kernel)]
  decide +kernel

@[expose] def phi18Cube : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  (!![1, 0, 0, 0, -1, 1; 0, 0, 1, 0, -1, 1; 1, -1, 1, 0, -1, 1; 1, -1, 1, 0, -1, 2;
    1, 0, 1, -1, 0, 1; 0, 0, 1, -1, 0, 1] : Matrix (Fin 6) (Fin 6) ℤ)

@[expose] def phi18Sixth : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  (!![0, 0, 0, 0, -1, 1; 0, -1, 1, 0, -1, 1; 1, -1, 0, 0, -1, 1; 1, -1, 1, -1, -1, 2;
    1, 0, 1, -1, -1, 1; 0, 0, 1, -1, 0, 0] : Matrix (Fin 6) (Fin 6) ℤ)

theorem phi18Matrix6_pow_three : phi18Matrix6 ^ 3 = phi18Cube := by decide +kernel

theorem phi18Cube_mul_self : phi18Cube * phi18Cube = phi18Sixth := by decide +kernel

theorem phi18Matrix_pow_three : phi18Matrix ^ 3 = phi18Cube := by
  rw [phi18Matrix_eq, phi18Matrix6_pow_three]

theorem phi18Matrix_pow_six : phi18Matrix ^ 6 = phi18Sixth := by
  rw [show 6 = 3 + 3 from rfl, pow_add, phi18Matrix_pow_three, phi18Cube_mul_self]

theorem phi18Matrix_poly : phi18Matrix ^ 6 - phi18Matrix ^ 3 + 1 = 0 := by
  rw [phi18Matrix_pow_six, phi18Matrix_pow_three]
  decide +kernel

theorem det_phi18Matrix : phi18Matrix.det = 1 := by
  rw [phi18Matrix_eq, ← detLaplace_eq_det]
  decide +kernel

@[expose] def phi18Next : Fin 72 → Fin 72 :=
  ![
    5, 37, 29, 1, 3, 2, 16, 40, 28, 27, 38, 39, 8, 9, 12, 11, 10, 47, 49, 18, 4, 17, 46, 48, 19,
    20, 22, 54, 15, 56, 14, 7, 13, 6, 53, 55, 30, 26, 60, 25, 61, 24, 0, 21, 23, 59, 36, 64, 33,
    35, 31, 34, 32, 42, 45, 62, 44, 41, 43, 65, 51, 66, 52, 50, 67, 57, 68, 69, 70, 71, 58, 63]

theorem phi18Matrix6_mulVec_e6RootVec : ∀ m : Fin 72,
    phi18Matrix6.mulVec (e6RootVec m) = e6RootVec (phi18Next m) := by
  decide +kernel

theorem phi18Matrix_mulVec_e6RootVec (m : Fin 72) :
    phi18Matrix.mulVec (e6RootVec m) = e6RootVec (phi18Next m) := by
  rw [phi18Matrix_eq, phi18Matrix6_mulVec_e6RootVec]

theorem e6RootVec_phi18Next_iterate (k : ℕ) (m : Fin 72) :
    e6RootVec (phi18Next^[k] m) = (phi18Matrix ^ k).mulVec (e6RootVec m) := by
  induction k generalizing m with
  | zero => rw [Function.iterate_zero_apply, pow_zero, Matrix.one_mulVec]
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, ← phi18Matrix_mulVec_e6RootVec, Matrix.mulVec_mulVec,
      ← pow_succ]

@[expose] def phi18SeedIdx : Fin 4 → Fin 72 := ![71, 59, 60, 46]

@[expose] def phi18OrbitSeed : Fin 72 → Fin 4 :=
  ![
    2, 3, 2, 3, 3, 2, 2, 0, 3, 1, 2, 3, 3, 1, 3, 3, 2, 0, 1, 1, 3, 0, 3, 2, 1, 3, 3, 1, 3, 2, 3,
    0, 1, 2, 2, 1, 3, 3, 2, 3, 0, 1, 2, 0, 2, 1, 3, 0, 2, 1, 0, 2, 1, 2, 1, 1, 2, 1, 0, 1, 2, 0,
    1, 0, 0, 1, 0, 0, 0, 0, 0, 0]

@[expose] def phi18OrbitExp : Fin 72 → ℕ :=
  ![
    5, 14, 7, 13, 12, 6, 14, 4, 5, 14, 16, 8, 4, 13, 3, 7, 15, 13, 6, 5, 11, 12, 17, 11, 4, 10,
    16, 15, 6, 8, 2, 3, 12, 13, 2, 8, 1, 15, 17, 9, 5, 3, 4, 11, 10, 17, 0, 14, 12, 7, 2, 1, 11,
    3, 16, 9, 9, 2, 10, 0, 0, 6, 10, 1, 15, 1, 7, 16, 8, 17, 9, 0]

theorem phi18Next_iterate_orbit : ∀ m : Fin 72,
    phi18Next^[phi18OrbitExp m] (phi18SeedIdx (phi18OrbitSeed m)) = m := by
  decide +kernel

@[expose] def phi18RootOrbit (α : Fin Tag.E6.rank → ℤ) :
    Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  Matrix.of fun i j => ((phi18Matrix ^ (j : ℕ)).mulVec α) i

theorem phi18RootOrbit_mulVec (x : Fin Tag.E6.rank → ℤ) :
    phi18RootOrbit (phi18Matrix.mulVec x) = phi18Matrix * phi18RootOrbit x := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [phi18RootOrbit, Matrix.of_apply, Matrix.mulVec_mulVec]
  rw [← pow_succ, pow_succ', ← Matrix.mulVec_mulVec]
  rfl

theorem det_phi18RootOrbit_mulVec (x : Fin Tag.E6.rank → ℤ) :
    (phi18RootOrbit (phi18Matrix.mulVec x)).det = (phi18RootOrbit x).det := by
  rw [phi18RootOrbit_mulVec, Matrix.det_mul, det_phi18Matrix, one_mul]

theorem det_phi18RootOrbit_iterate (k : ℕ) (m : Fin 72) :
    (phi18RootOrbit (e6RootVec (phi18Next^[k] m))).det =
      (phi18RootOrbit (e6RootVec m)).det := by
  induction k generalizing m with
  | zero => rw [Function.iterate_zero_apply]
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, ← phi18Matrix_mulVec_e6RootVec,
      det_phi18RootOrbit_mulVec]

theorem phi18RootOrbit_e6RootVec (m : Fin 72) :
    phi18RootOrbit (e6RootVec m) =
      Matrix.of fun i j : Fin Tag.E6.rank => e6RootVec (phi18Next^[(j : ℕ)] m) i := by
  ext i j
  rw [phi18RootOrbit, Matrix.of_apply, Matrix.of_apply, e6RootVec_phi18Next_iterate]

@[expose] def phi18SeedOrbit : Fin 4 → Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  ![(!![-1, 0, 0, 0, 1, 1; -2, -1, -1, -1, 0, 0; -2, -1, -1, 0, 1, 1; -3, -2, -2, -1, 0, 1;
      -2, -2, -1, -1, 0, 1; -1, -1, 0, 0, 0, 1] : Matrix (Fin 6) (Fin 6) ℤ),
    (!![-1, -1, 0, 0, 0, 0; -1, -1, -1, -1, 0, -1; -2, -1, -1, -1, 0, 0;
      -2, -2, -2, -1, -1, -1; -1, -2, -1, -1, -1, 0; 0, -1, -1, 0, 0, 0] :
      Matrix (Fin 6) (Fin 6) ℤ),
    (!![-1, 0, 0, -1, 0, 1; -1, -1, 0, -1, -1, 0; -1, -1, -1, -1, 0, 0;
      -2, -1, -1, -2, -1, 0; -1, -1, -1, -1, -1, 0; -1, -1, 0, 0, -1, 0] :
      Matrix (Fin 6) (Fin 6) ℤ),
    (!![-1, 0, 0, 0, 0, 0; -1, 0, -1, 0, 0, -1; -1, 0, -1, 0, 0, 0; -1, -1, -1, 0, -1, 0;
      -1, -1, 0, -1, 0, 0; 0, -1, 0, 0, 0, 0] : Matrix (Fin 6) (Fin 6) ℤ)]

theorem phi18SeedOrbit_eq : ∀ i : Fin 4,
    (Matrix.of fun r c : Fin Tag.E6.rank =>
      e6RootVec (phi18Next^[(c : ℕ)] (phi18SeedIdx i)) r) = phi18SeedOrbit i := by
  decide +kernel

theorem detLaplace_phi18SeedOrbit_zero : detLaplace 6 (phi18SeedOrbit 0) = 1 := by
  decide +kernel

theorem detLaplace_phi18SeedOrbit_one : detLaplace 6 (phi18SeedOrbit 1) = 3 := by
  decide +kernel

theorem detLaplace_phi18SeedOrbit_two : detLaplace 6 (phi18SeedOrbit 2) = 1 := by
  decide +kernel

theorem detLaplace_phi18SeedOrbit_three : detLaplace 6 (phi18SeedOrbit 3) = 1 := by
  decide +kernel

theorem det_phi18SeedOrbit (i : Fin 4) :
    (phi18SeedOrbit i).det = 1 ∨ (phi18SeedOrbit i).det = 3 := by
  rw [← detLaplace_eq_det]
  fin_cases i
  · exact Or.inl detLaplace_phi18SeedOrbit_zero
  · exact Or.inr detLaplace_phi18SeedOrbit_one
  · exact Or.inl detLaplace_phi18SeedOrbit_two
  · exact Or.inl detLaplace_phi18SeedOrbit_three

theorem det_phi18RootOrbit {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    (phi18RootOrbit α).det = 1 ∨ (phi18RootOrbit α).det = 3 := by
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hα
  rw [← phi18Next_iterate_orbit m, det_phi18RootOrbit_iterate, phi18RootOrbit_e6RootVec,
    phi18SeedOrbit_eq]
  exact det_phi18SeedOrbit _

@[expose] def phi18OrbitBasis6 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  (!![1, 0, 0, 1, 1, 0; 0, 0, 0, 0, 1, 1; 0, 0, 1, 1, 1, 1; 0, 0, 0, 1, 2, 1;
    0, 0, 0, 1, 1, 1; 0, 1, 0, 0, 1, 1] : Matrix (Fin 6) (Fin 6) ℤ)

theorem e6RootVec_zero : e6RootVec 0 = Pi.single (e6Index 0) 1 := by decide +kernel

theorem phi18OrbitBasis_eq_of : (Matrix.of fun r c : Fin Tag.E6.rank =>
    e6RootVec (phi18Next^[(c : ℕ)] 0) r) = phi18OrbitBasis6 := by
  decide +kernel

theorem phi18RootOrbit_single_eq :
    phi18RootOrbit (Pi.single (e6Index 0) 1) = phi18OrbitBasis6 := by
  rw [← e6RootVec_zero, phi18RootOrbit_e6RootVec, phi18OrbitBasis_eq_of]

theorem det_phi18OrbitBasis : (phi18RootOrbit (Pi.single (e6Index 0) 1)).det = 1 := by
  rw [phi18RootOrbit_single_eq, ← detLaplace_eq_det]
  decide +kernel

theorem charVal_ne_zero_of_phi18 {K : Type*} [Field K] (h3 : (3 : K) ≠ 0) {a : K}
    {v : Fin Tag.E6.rank → K} (hv : v ≠ 0)
    (hu : ((phi18Matrix.map (Int.cast : ℤ → K)).transpose).mulVec v = a • v)
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) : charVal v α ≠ 0 := by
  intro h0
  apply hv
  have hpow := charVal_pow_mulVec_of_eigen hu
  have hdet : ((phi18RootOrbit α).map (Int.cast : ℤ → K)).det ≠ 0 := by
    rw [show (Int.cast : ℤ → K) = ⇑(Int.castRingHom K) from rfl, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det, eq_intCast]
    rcases det_phi18RootOrbit hα with h | h <;> rw [h]
    · simp
    · exact_mod_cast h3
  refine Matrix.eq_zero_of_vecMul_eq_zero hdet ?_
  funext j
  have e : (Matrix.vecMul v ((phi18RootOrbit α).map (Int.cast : ℤ → K))) j =
      charVal v ((phi18Matrix ^ (j : ℕ)).mulVec α) := by
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, phi18RootOrbit, Matrix.of_apply,
      charVal]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e, hpow, h0, mul_zero, Pi.zero_apply]

theorem natCast_three_ne_zero {p : ℕ} [Fact p.Prime] (hp : 3 < p) : (3 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((3 : ℤ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
  have := Int.le_of_dvd (by norm_num) h'
  omega

end CFSG.RankThree.E6

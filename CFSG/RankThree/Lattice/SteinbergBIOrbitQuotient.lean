module

public import CFSG.RankThree.Lattice.SteinbergBISaturation
public import CFSG.RankThree.Lattice.SteinbergBIOrbitLattice

public section

namespace CFSG.RankThree.Lattice

open Polynomial Matrix Module

variable {n : ℕ}

@[expose] noncomputable def ratEnd (w : Matrix (Fin n) (Fin n) ℤ) : Module.End ℚ (Fin n → ℚ) :=
  Matrix.toLin' (w.map (Int.castRingHom ℚ))

theorem castLin_pow_mulVec (w : Matrix (Fin n) (Fin n) ℤ) (v : Fin n → ℤ) (j : ℕ) :
    castLin n ((w ^ j) *ᵥ v) = (ratEnd w ^ j) (castLin n v) := by
  induction j with
  | zero => rw [pow_zero, pow_zero, Matrix.one_mulVec, Module.End.one_apply]
  | succ j ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, castLin_mulVec, ih, pow_succ', Module.End.mul_apply]
    rfl

theorem ratSpan_orbitLattice (w : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) :
    ratSpan (orbitLattice w x) = cycSpan (ratEnd w) (castLin n x) := by
  rw [orbitLattice, ratSpan_span, cycSpan, ← Set.range_comp]
  simp only [Function.comp_def, castLin_pow_mulVec]

theorem aeval_ratEnd_map (w : Matrix (Fin n) (Fin n) ℤ) (p : ℤ[X]) (v : Fin n → ℤ) :
    aeval (ratEnd w) (p.map (Int.castRingHom ℚ)) (castLin n v) =
      castLin n ((aeval w p) *ᵥ v) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.map_add, map_add, LinearMap.add_apply, hp, hq, map_add, Matrix.add_mulVec,
      map_add]
  | monomial j a =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, Module.End.mul_apply,
      Module.algebraMap_end_apply, ← castLin_pow_mulVec, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, Matrix.smul_mulVec, map_zsmul, eq_intCast,
      Int.cast_smul_eq_zsmul]

theorem aeval_mulVec_pow_mulVec (w : Matrix (Fin n) (Fin n) ℤ) (p : ℤ[X]) (x : Fin n → ℤ)
    (j : ℕ) : (aeval w p) *ᵥ ((w ^ j) *ᵥ x) = (w ^ j) *ᵥ ((aeval w p) *ᵥ x) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← aeval_X_pow (R := ℤ), ← map_mul, ← map_mul,
    mul_comm]

theorem orbitQuot_of_cert (w : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) {k : ℕ} (hk : k ≤ n)
    {p g : ℤ[X]} (hp : p.Monic) (hpk : p.natDegree = k) (hrel : (aeval w p) *ᵥ x = 0)
    (hchar : w.charpoly = p * g) {P P' : Matrix (Fin n) (Fin n) ℤ} (hPP : P * P' = 1)
    (hzero : ∀ i : Fin n, k ≤ (i : ℕ) → ∀ j : Fin k, (P' *ᵥ ((w ^ (j : ℕ)) *ᵥ x)) i = 0)
    (hdet : (certMat hk (fun j : Fin k => (w ^ (j : ℕ)) *ᵥ x) P').det ≠ 0) :
    finrank ℤ (orbitLattice w x) = k ∧
      LinearIndependent ℤ (fun j : Fin k => (w ^ (j : ℕ)) *ᵥ x) ∧
      Submodule.span ℤ (Set.range fun j : Fin k => (w ^ (j : ℕ)) *ᵥ x) = orbitLattice w x ∧
      satIndex (orbitLattice w x) =
        (certMat hk (fun j : Fin k => (w ^ (j : ℕ)) *ᵥ x) P').det.natAbs ∧
      ∃ h : ratSpan (orbitLattice w x) ≤ (ratSpan (orbitLattice w x)).comap (ratEnd w),
        ((ratEnd w).restrict h).charpoly = p.map (Int.castRingHom ℚ) ∧
        ((ratSpan (orbitLattice w x)).mapQ _ (ratEnd w) h).charpoly =
          g.map (Int.castRingHom ℚ) := by
  have hspan := (orbitLattice_eq_span_of_monic w x hp hpk hrel).symm
  have hli := linearIndependent_of_cert hzero hdet
  refine ⟨?_, hli, hspan, ?_, ?_⟩
  · rw [← hspan, finrank_span_eq_card hli, Fintype.card_fin]
  · rw [← hspan]
    exact relIndex_saturation_of_cert hPP hzero hdet
  · rw [ratSpan_orbitLattice]
    have hinv := cycSpan_le_comap (ratEnd w) (castLin n x)
    have hliQ : LinearIndependent ℚ fun j : Fin k => (ratEnd w ^ (j : ℕ)) (castLin n x) := by
      have h := linearIndependent_castLin_of_cert hdet
      simp only [castLin_pow_mulVec] at h
      exact h
    have hres : ((ratEnd w).restrict hinv).charpoly = p.map (Int.castRingHom ℚ) :=
      charpoly_restrict_cycSpan (ratEnd w) (castLin n x) (hp.map _)
        (by rw [hp.natDegree_map, hpk])
        (by rw [aeval_ratEnd_map, hrel, map_zero]) hliQ hinv
    refine ⟨hinv, hres, ?_⟩
    have hmul := charpoly_eq_restrict_mul_mapQ _ (ratEnd w) hinv
    rw [hres, show (ratEnd w).charpoly = (w.map (Int.castRingHom ℚ)).charpoly from
      Matrix.charpoly_toLin' _, Matrix.charpoly_map, hchar, Polynomial.map_mul] at hmul
    exact (mul_left_cancel₀ (hp.map _).ne_zero hmul).symm

section Transfer

variable {w : Matrix (Fin n) (Fin n) ℤ} {m : ℕ}

theorem pow_mul_pow_eq_one (hm : 0 < m) (hw : w ^ m = 1) (j : ℕ) :
    w ^ ((m - 1) * j) * w ^ j = 1 := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [← pow_add, Nat.add_sub_cancel, show m' * j + j = (m' + 1) * j by ring, pow_mul, hw,
    one_pow]

theorem orbitLattice_pow_mulVec (hm : 0 < m) (hw : w ^ m = 1) (x : Fin n → ℤ) (j : ℕ) :
    orbitLattice w ((w ^ j) *ᵥ x) = orbitLattice w x := by
  apply le_antisymm
  · rw [orbitLattice, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show (w ^ i) *ᵥ ((w ^ j) *ᵥ x) ∈ orbitLattice w x
    rw [Matrix.mulVec_mulVec, ← pow_add]
    exact pow_mulVec_mem_orbitLattice w x (i + j)
  · rw [orbitLattice, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h : (w ^ i) *ᵥ x = (w ^ (i + (m - 1) * j)) *ᵥ ((w ^ j) *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, pow_add, Matrix.mul_assoc, pow_mul_pow_eq_one hm hw,
        Matrix.mul_one]
    show (w ^ i) *ᵥ x ∈ orbitLattice w ((w ^ j) *ᵥ x)
    rw [h]
    exact pow_mulVec_mem_orbitLattice w _ _

theorem linearIndependent_pow_mulVec (hm : 0 < m) (hw : w ^ m = 1) {x : Fin n → ℤ} {k : ℕ}
    (hli : LinearIndependent ℤ fun i : Fin k => (w ^ (i : ℕ)) *ᵥ x) (j : ℕ) :
    LinearIndependent ℤ fun i : Fin k => (w ^ (i : ℕ)) *ᵥ ((w ^ j) *ᵥ x) := by
  have hinj : Function.Injective (Matrix.mulVecLin (w ^ j)) := by
    intro u v huv
    have h := congrArg (fun z => (w ^ ((m - 1) * j)) *ᵥ z) huv
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, pow_mul_pow_eq_one hm hw,
      Matrix.one_mulVec] at h
    exact h
  have h := hli.map' (Matrix.mulVecLin (w ^ j)) (LinearMap.ker_eq_bot.2 hinj)
  convert h using 1
  funext i
  simp only [Function.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← pow_add,
    add_comm]

end Transfer

end CFSG.RankThree.Lattice

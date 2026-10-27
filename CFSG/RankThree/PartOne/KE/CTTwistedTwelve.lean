module

public import CFSG.RankThree.PartOne.KE.CTTwisted
public import CFSG.RankThree.PartOne.KE.CTTwistedArith
public import CFSG.RankThree.E6.TwistedPhi12
public import CFSG.RankThree.Chevalley.SteinbergBNExceptionalCyclotomicExhaustion

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  Polynomial Matrix
open CFSG.RankThree.Chevalley (exhaustionPhi)
open CFSG.RankThree.E6 (charVal e6Coxeter e6Index e6Rho phi12Matrix phi12Matrix_poly
  phi12OrbitBasis det_phi12OrbitBasis exists_weyl_eq_neg_coxeter_rho charVal_ne_zero_of_phi12
  natCast_ne_zero_of_two weylMatrix_mulVec)

theorem twisted_E6_twelve_cyclic_sylow {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpf : (p : ℤ) ∣ (exhaustionPhi 12).eval ((ℓ ^ f : ℕ) : ℤ)) :
    7 < p ∧ orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 12 ∧
      ∃ k : ℕ, CyclicSylowConclusion' (twistedE6RootGroup K σ) p
        (((ℓ ^ f) ^ 4 - (ℓ ^ f) ^ 2 + 1) * ((ℓ ^ f) ^ 2 - ℓ ^ f + 1)) (3 ^ k) := by
  have hq : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hpf' : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 4 - ((ℓ ^ f : ℕ) : ℤ) ^ 2 + 1 := by
    simpa [exhaustionPhi] using hpf
  obtain ⟨hp7, hpq, hord⟩ := CTE6.e6Twelve_data hp hp3 hpf'
  refine ⟨hp7, hord, ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have hx : ((ℓ ^ f : ℕ) : ZMod p) ^ 4 - ((ℓ ^ f : ℕ) : ZMod p) ^ 2 + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd
      (((ℓ ^ f : ℕ) : ℤ) ^ 4 - ((ℓ ^ f : ℕ) : ℤ) ^ 2 + 1) p).2 hpf'
    simpa using this
  obtain ⟨v, hv⟩ := exists_weyl_eq_neg_coxeter_rho
  have hv' : ∀ x : Fin Tag.E6.rank → ℤ, v • x = phi12Matrix *ᵥ permLattice e6Rho x :=
    fun x => by rw [hv x, phi12Matrix, Matrix.neg_mulVec, weylMatrix_mulVec]
  have hunit : IsUnit (orbitMat phi12Matrix (Pi.single (e6Index 0) 1) Tag.E6.rank).det := by
    change IsUnit phi12OrbitBasis.det
    rw [det_phi12OrbitBasis]
    exact isUnit_one
  obtain ⟨hlin, hspan⟩ := (isBasis_iff_isUnit_det phi12Matrix (Pi.single (e6Index 0) 1)).2 hunit
  have hchar : phi12Matrix.charpoly = X ^ 6 - X ^ 5 + X ^ 3 - X + 1 := by
    refine charpoly_eq_of_cyclic phi12Matrix (Pi.single (e6Index 0) 1) (by monicity!)
      (by compute_degree!) ?_ ?_
    · have : aeval phi12Matrix (X ^ 6 - X ^ 5 + X ^ 3 - X + 1 : ℤ[X]) = 0 := by
        simpa using phi12Matrix_poly
      rw [this]
      exact Matrix.zero_mulVec _
    · change phi12OrbitBasis.det ≠ 0
      rw [det_phi12OrbitBasis]
      exact one_ne_zero
  have h24 : (ℓ ^ f) ^ 2 ≤ (ℓ ^ f) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h21 : ℓ ^ f ≤ (ℓ ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hn₀ : ((ℓ ^ f) ^ 4 - (ℓ ^ f) ^ 2 + 1) * ((ℓ ^ f) ^ 2 - ℓ ^ f + 1) ≠ 0 :=
    Nat.mul_ne_zero (by omega) (by omega)
  have hev : phi12Matrix.charpoly.eval ((ℓ ^ f : ℕ) : ℤ) =
      ((((ℓ ^ f) ^ 4 - (ℓ ^ f) ^ 2 + 1) * ((ℓ ^ f) ^ 2 - ℓ ^ f + 1) : ℕ) : ℤ) := by
    rw [hchar]
    simp only [eval_add, eval_sub, eval_pow, eval_X, eval_one]
    push_cast [Nat.cast_sub h24, Nat.cast_sub h21]
    ring
  have hnat : (phi12Matrix.charpoly.eval ((ℓ ^ f : ℕ) : ℤ)).natAbs =
      ((ℓ ^ f) ^ 4 - (ℓ ^ f) ^ 2 + 1) * ((ℓ ^ f) ^ 2 - ℓ ^ f + 1) := by
    rw [hev, Int.natAbs_natCast]
  have hne : phi12Matrix.charpoly.eval ((ℓ ^ f : ℕ) : ℤ) ≠ 0 := by
    rw [hev]
    exact_mod_cast hn₀
  have hdet : phi12Matrix.charpoly.coeff 0 = 1 ∨ phi12Matrix.charpoly.coeff 0 = -1 := by
    left
    rw [hchar, coeff_zero_eq_eval_zero]
    simp
  have hreg' : ∀ z : Fin TwistTag.E6.tag.rank → ZMod p, z ≠ 0 →
      ((phi12Matrix.map (Int.cast : ℤ → ZMod p)).transpose).mulVec z =
        ((ℓ ^ f : ℕ) : ZMod p) • z →
      ∀ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α → charVal z α ≠ 0 :=
    fun z hz0 hz α hα => charVal_ne_zero_of_phi12 (natCast_ne_zero_of_two hp3) hx hz0 hz hα
  have hord' : p ^ ((ℓ ^ f) ^ 36 * ((ℓ ^ f) ^ 12 - 1) * ((ℓ ^ f) ^ 9 + 1) * ((ℓ ^ f) ^ 8 - 1) *
        ((ℓ ^ f) ^ 6 - 1) * ((ℓ ^ f) ^ 5 + 1) * ((ℓ ^ f) ^ 2 - 1)).factorization p =
      p ^ (phi12Matrix.charpoly.eval ((ℓ ^ f : ℕ) : ℤ)).natAbs.factorization p := by
    rw [hnat]
    exact CTTw.ordProj_twisted_twelve hp hq hpq hord
  obtain ⟨k, hk⟩ := cyclic_sylow_twisted_E6 hℓ hf K hK σ hσ hp hp7 phi12Matrix v hv'
    (Pi.single (e6Index 0) 1) hlin hspan hdet hne hreg' hord'
  exact ⟨k, hnat ▸ hk⟩

end CFSG.RankThree.PartOne.KE

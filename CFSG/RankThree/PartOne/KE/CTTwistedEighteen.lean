module

public import CFSG.RankThree.PartOne.KE.CTTwisted
public import CFSG.RankThree.PartOne.KE.CTTwistedArith
public import CFSG.RankThree.E6.TwistedPhi18
public import CFSG.RankThree.Chevalley.SteinbergBNExceptionalCyclotomicExhaustion

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  Polynomial Matrix
open CFSG.RankThree.Chevalley (exhaustionPhi)
open CFSG.RankThree.E6 (charVal e6Index e6Rho e6Word phi18Word phi18Matrix phi18Matrix_mulVec
  phi18Matrix_poly phi18RootOrbit det_phi18OrbitBasis charVal_ne_zero_of_phi18
  natCast_three_ne_zero)

theorem permLattice_e6Rho_permLattice (x : Fin Tag.E6.rank → ℤ) :
    permLattice e6Rho (permLattice e6Rho x) = x := by
  funext i
  exact congrArg x (e6_perm_symm_symm_apply i)

theorem twisted_E6_eighteen_cyclic_sylow {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 18).eval ((ℓ ^ f : ℕ) : ℤ)) :
    7 < p ∧ orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 18 ∧
      ∃ k : ℕ, CyclicSylowConclusion' (twistedE6RootGroup K σ) p
        ((ℓ ^ f) ^ 6 - (ℓ ^ f) ^ 3 + 1) (3 ^ k) := by
  have hq : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hpf' : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 6 - ((ℓ ^ f : ℕ) : ℤ) ^ 3 + 1 := by
    simpa [exhaustionPhi] using hpf
  obtain ⟨hp7, hpq, hord⟩ := CTE6.e7Eighteen_data hp hp3 hpf'
  refine ⟨hp7, hord, ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have hv : ∀ x : Fin Tag.E6.rank → ℤ,
      (coxeterSystem Tag.E6).wordProd (e6Word phi18Word) • x =
        phi18Matrix *ᵥ permLattice e6Rho x :=
    fun x => by rw [phi18Matrix_mulVec, permLattice_e6Rho_permLattice]
  have hunit : IsUnit (orbitMat phi18Matrix (Pi.single (e6Index 0) 1) Tag.E6.rank).det := by
    change IsUnit (phi18RootOrbit (Pi.single (e6Index 0) 1)).det
    rw [det_phi18OrbitBasis]
    exact isUnit_one
  obtain ⟨hlin, hspan⟩ := (isBasis_iff_isUnit_det phi18Matrix (Pi.single (e6Index 0) 1)).2 hunit
  have hchar : phi18Matrix.charpoly = X ^ 6 - X ^ 3 + 1 := by
    refine charpoly_eq_of_cyclic phi18Matrix (Pi.single (e6Index 0) 1) (by monicity!)
      (by compute_degree!) ?_ ?_
    · have : aeval phi18Matrix (X ^ 6 - X ^ 3 + 1 : ℤ[X]) = 0 := by
        simpa using phi18Matrix_poly
      rw [this]
      exact Matrix.zero_mulVec _
    · change (phi18RootOrbit (Pi.single (e6Index 0) 1)).det ≠ 0
      rw [det_phi18OrbitBasis]
      exact one_ne_zero
  have h36 : (ℓ ^ f) ^ 3 ≤ (ℓ ^ f) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hn₀ : (ℓ ^ f) ^ 6 - (ℓ ^ f) ^ 3 + 1 ≠ 0 := by omega
  have hev : phi18Matrix.charpoly.eval ((ℓ ^ f : ℕ) : ℤ) =
      (((ℓ ^ f) ^ 6 - (ℓ ^ f) ^ 3 + 1 : ℕ) : ℤ) := by
    rw [hchar]
    simp only [eval_add, eval_sub, eval_pow, eval_X, eval_one]
    push_cast [Nat.cast_sub h36]
    ring
  have hnat : (phi18Matrix.charpoly.eval ((ℓ ^ f : ℕ) : ℤ)).natAbs =
      (ℓ ^ f) ^ 6 - (ℓ ^ f) ^ 3 + 1 := by
    rw [hev, Int.natAbs_natCast]
  have hne : phi18Matrix.charpoly.eval ((ℓ ^ f : ℕ) : ℤ) ≠ 0 := by
    rw [hev]
    exact_mod_cast hn₀
  have hdet : phi18Matrix.charpoly.coeff 0 = 1 ∨ phi18Matrix.charpoly.coeff 0 = -1 := by
    left
    rw [hchar, coeff_zero_eq_eval_zero]
    simp
  have hreg' : ∀ z : Fin TwistTag.E6.tag.rank → ZMod p, z ≠ 0 →
      ((phi18Matrix.map (Int.cast : ℤ → ZMod p)).transpose).mulVec z =
        ((ℓ ^ f : ℕ) : ZMod p) • z →
      ∀ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α → charVal z α ≠ 0 :=
    fun z hz0 hz α hα => charVal_ne_zero_of_phi18 (natCast_three_ne_zero hp3) hz0 hz hα
  have hord' : p ^ ((ℓ ^ f) ^ 36 * ((ℓ ^ f) ^ 12 - 1) * ((ℓ ^ f) ^ 9 + 1) * ((ℓ ^ f) ^ 8 - 1) *
        ((ℓ ^ f) ^ 6 - 1) * ((ℓ ^ f) ^ 5 + 1) * ((ℓ ^ f) ^ 2 - 1)).factorization p =
      p ^ (phi18Matrix.charpoly.eval ((ℓ ^ f : ℕ) : ℤ)).natAbs.factorization p := by
    rw [hnat]
    exact CTTw.ordProj_twisted_eighteen hp hq hpq hord
  obtain ⟨k, hk⟩ := cyclic_sylow_twisted_E6 hℓ hf K hK σ hσ hp hp7 phi18Matrix
    ((coxeterSystem Tag.E6).wordProd (e6Word phi18Word)) hv (Pi.single (e6Index 0) 1) hlin hspan
    hdet hne hreg' hord'
  exact ⟨k, hnat ▸ hk⟩

end CFSG.RankThree.PartOne.KE

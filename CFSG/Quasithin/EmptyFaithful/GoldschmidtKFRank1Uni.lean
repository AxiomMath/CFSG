module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFRank1Heis
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.LieType.Chevalley.RootPairCommonField
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdNineLin

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.QuasithinUnique Id2519
open scoped Matrix

section ElemNine

variable {K : Type} [Field K]

theorem tMat_hermitian {ω : K} {q : ℕ} (hq : 1 ≤ q) (hω : ω ^ (q + 1) = 1) :
    ((tMat ω).map (· ^ q))ᵀ * tMat ω = 1 := by
  have h0 : (fun x : K => x ^ q) 0 = 0 := zero_pow (by omega)
  rw [tMat, Matrix.diagonal_map (f := fun x : K => x ^ q) h0, Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i
  · simp
  · simp [← pow_succ, hω]
  · have h2 : (ω ^ 2) ^ q * ω ^ 2 = (ω ^ (q + 1)) ^ 2 := by ring
    simp only [Fin.reduceFinMk, Matrix.cons_val]
    rw [h2, hω, one_pow]

theorem pMat_hermitian {q : ℕ} (hq : 1 ≤ q) :
    (((pMat : Matrix (Fin 3) (Fin 3) K)).map (· ^ q))ᵀ * (pMat : Matrix (Fin 3) (Fin 3) K) = 1 := by
  have h0 : (0 : K) ^ q = 0 := zero_pow (by omega)
  have hm : ((pMat : Matrix (Fin 3) (Fin 3) K)).map (· ^ q) = pMat := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pMat, h0]
  rw [hm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem hasElemAb_nine_psu_three [Finite K] {q : ℕ} (hq : 1 ≤ q) (hK : Nat.card K = q ^ 2)
    (h3 : 3 ∣ q + 1) : HasElemAb 3 9 (StatedProj (StatedSU 3 q K)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    have h2 : (k + 1) ^ 2 = k * (k + 2) + 1 := by ring
    rw [h2, Nat.add_sub_cancel]
    exact Dvd.dvd.mul_left (by simpa [add_assoc] using h3) k
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 hcard
  have hω3 : ((ω : Kˣ) : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hω, pow_orderOf_eq_one, Units.val_one]
  have hω1 : ((ω : Kˣ) : K) ≠ 1 := by
    intro h
    have : ω = 1 := Units.ext h
    rw [this, orderOf_one] at hω
    omega
  have hωq : ((ω : Kˣ) : K) ^ (q + 1) = 1 := by
    obtain ⟨m, hm⟩ := h3
    rw [hm, pow_mul, hω3, one_pow]
  refine hasElemAb_nine_statedProj (x := tGL ((ω : Kˣ) : K) hω3) (y := pGL)
    (Subgroup.subset_closure ⟨det_tMat hω3, tMat_hermitian hq hωq⟩)
    (Subgroup.subset_closure ⟨det_pMat, pMat_hermitian hq⟩)
    (tGL_pow_three _ _) pGL_pow_three
    ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) (ω ^ 2), ⟨ω ^ 2, rfl⟩, tGL_mul_pGL ω hω3⟩
    (tGL_not_scalar ω hω3 hω1) (fun n c hc => by
      obtain ⟨u, rfl⟩ := hc
      exact tGL_pow_mul_scalar_ne _ hω3 n u)

end ElemNine

section Pinned

variable {p f : ℕ} {K : Type} [Field K]

theorem outThreeBound_psu3 (h : UnitaryFieldData p f K) (hq : 2 < p ^ f) (h3 : ¬ 3 ∣ p ^ f + 1) :
    OutThreeBound (unitaryPSU h 3) := by
  have := h.finite
  have : IsCyclic (K ≃+* K) := CFSG.LieType.Chevalley.ringAut_isCyclic
  exact outThreeBound_of_pinned_cube (stdPinnedPSU3 h) (stdPinnedPSU3_stable hq).normal
    (fun τ hτ3 hτD => isField_psu3_of_pow_three_eq_one hq hτ3 hτD)
    (isCyclic_range_of_cyclic _) (psu3_inndiag_cube h3)

theorem outThreeOrElemNine_of_statedPSU3 {S : Type} [Group S] [Finite K] (hp : p.Prime)
    (hf : 1 ≤ f) (hq : 2 < p ^ f) (hK : Nat.card K = (p ^ f) ^ 2)
    (e : S ≃* StatedProj (StatedSU 3 (p ^ f) K)) : OutThreeOrElemNine S := by
  by_cases h3 : 3 ∣ p ^ f + 1
  · right
    exact HasElemAb.of_mulEquiv e.symm
      (hasElemAb_nine_psu_three (Nat.one_le_pow _ _ hp.pos) hK h3)
  · left
    have hU : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    exact (outThreeBound_psu3 hU hq h3).of_mulEquiv
      (e.trans (unitaryPSUEquiv hU (by norm_num)).symm)

end Pinned

end CFSG.Quasithin.SBd19F

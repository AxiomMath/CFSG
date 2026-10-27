module

public import CFSG.Quasithin.Background.F7TwoInvL2OddUnip
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare
public import CFSG.Dihedral.Glauberman.DicksonMaxUp

public section

namespace CFSG.Quasithin.F7Two

open CFSG.GorensteinWalter CFSG.PSL2Table
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def nonsplitJ (ν : K) (hν : ν ≠ 0) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, ν; 1, 0] (by simp [Matrix.det_fin_two, hν])

@[expose] def N0 (ν : K) (hν : ν ≠ 0) : PGL2 K :=
  Matrix.ProjGenLinGroup.mk (nonsplitJ ν hν)

theorem nonsplitJ_mul_self (ν : K) (hν : ν ≠ 0) :
    nonsplitJ ν hν * nonsplitJ ν hν =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 ν hν) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nonsplitJ, Matrix.mul_apply]

theorem N0_mul_self (ν : K) (hν : ν ≠ 0) : N0 ν hν * N0 ν hν = 1 := by
  rw [N0, ← map_mul, nonsplitJ_mul_self]
  exact Matrix.ProjGenLinGroup.mk_scalar _

theorem N0_ne_one (ν : K) (hν : ν ≠ 0) : N0 ν hν ≠ 1 := by
  intro h
  rw [N0, Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at h
  obtain ⟨u, hu⟩ := h
  have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 1 0) hu
  simp [nonsplitJ] at this

theorem det_nonsplitJ (ν : K) (hν : ν ≠ 0) : ((nonsplitJ ν hν).det : K) = -ν := by
  simp [nonsplitJ, Matrix.det_fin_two]

theorem isSquare_neg_iff_of_not_isSquare [Finite K] {ν : K} (hν : ¬ IsSquare ν) :
    IsSquare (-ν) ↔ ¬ IsSquare (-1 : K) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have h1 : quadraticChar K ν = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hν
  have h2 : quadraticChar K (-ν) = quadraticChar K (-1) * quadraticChar K ν := by
    rw [← map_mul, neg_one_mul]
  have hm1 : (-1 : K) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hnν : -ν ≠ 0 := neg_ne_zero.mpr (ne_zero_of_not_isSquare hν)
  by_cases h : IsSquare (-1 : K)
  · have hc : quadraticChar K (-1) = 1 := (quadraticChar_one_iff_isSquare hm1).mpr h
    have : quadraticChar K (-ν) = -1 := by rw [h2, hc, h1, one_mul]
    simp only [h, not_true_eq_false, iff_false]
    exact quadraticChar_neg_one_iff_not_isSquare.mp this
  · have hc : quadraticChar K (-1) = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr h
    have : quadraticChar K (-ν) = 1 := by rw [h2, hc, h1]; norm_num
    simp only [h, not_false_eq_true, iff_true]
    exact (quadraticChar_one_iff_isSquare hnν).mp this

theorem N0_mem_range_iff [Finite K] {ν : K} (hν : ¬ IsSquare ν) :
    N0 ν (ne_zero_of_not_isSquare hν) ∈
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range ↔
      ¬ IsSquare (-1 : K) := by
  rw [N0, pgl2_mk_mem_psl2_range_iff_det_isSquare, det_nonsplitJ]
  exact isSquare_neg_iff_of_not_isSquare hν

omit [Field K] in
theorem exists_prime_pow_of_isOddPrimePower [Finite K] (hK : IsOddPrimePower (Nat.card K)) :
    ∃ p n : ℕ, Fact p.Prime ∧ p ≠ 2 ∧ Nat.card K = p ^ n := by
  obtain ⟨p, n, hp, hpodd, -, hKcard⟩ := hK
  exact ⟨p, n, ⟨hp⟩, fun h => (Nat.not_even_iff_odd.2 hpodd) (h ▸ even_two), hKcard⟩

theorem ringChar_ne_two_of_isOddPrimePower [Finite K] (hK : IsOddPrimePower (Nat.card K)) :
    ringChar K ≠ 2 := by
  obtain ⟨p, n, hp, hp2, hKcard⟩ := exists_prime_pow_of_isOddPrimePower hK
  exact CFSG.Glauberman.Dickson.MaxUp.ringChar_ne_two hKcard hp2

theorem mem_nonsplitSL_or_isAntiNS_of_mem_normalizer [Fintype K] (hF : ringChar K ≠ 2) {ν : K}
    (hν : ¬ IsSquare ν) (hq : 5 ≤ Fintype.card K) {M : SL(2, K)}
    (hM : mk M ∈ Subgroup.normalizer (nonsplitTorus ν : Set (PSL2 K))) :
    M ∈ nonsplitSL ν ∨ IsAntiNS ν M := by
  obtain ⟨x, hxS, hx1⟩ := exists_ne_one_nonsplitTorus hF hq hν
  obtain ⟨C, hC, hy, rfl⟩ := exists_of_mem_nonsplitTorus hxS hx1
  have h := (Subgroup.mem_normalizer_iff.1 hM (mk C)).1 hxS
  rw [mk_conj, mk_mem_nonsplitTorus_iff] at h
  exact (conj_mem_nonsplitSL_iff (Ring.two_ne_zero hF) hν hC hy M).1 h

theorem N0_mul_toPGL_mk_comm (ν : K) (hν : ν ≠ 0) {M : SL(2, K)}
    (hM : M ∈ nonsplitSL ν ∨ IsAntiNS ν M) :
    N0 ν hν * Matrix.ProjectiveSpecialLinearGroup.toPGL (mk M) =
      Matrix.ProjectiveSpecialLinearGroup.toPGL (mk M) * N0 ν hν := by
  change Matrix.ProjGenLinGroup.mk (nonsplitJ ν hν) *
      Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL M) =
    Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL M) *
      Matrix.ProjGenLinGroup.mk (nonsplitJ ν hν)
  rw [← map_mul, ← map_mul]
  rcases hM with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · congr 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [nonsplitJ, Matrix.mul_apply, Fin.sum_univ_two, h1, h2] <;> ring
  · rw [Matrix.ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨-1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [nonsplitJ, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, h1, h2] <;>
      ring

theorem pgl2InnerAutPSL2_N0_mk [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (hcard : 3 < Nat.card K) (ν : K) (hν : ν ≠ 0) {A A' : SL(2, K)}
    (h : (nonsplitJ ν hν : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K) =
      (A' : Matrix (Fin 2) (Fin 2) K) * (nonsplitJ ν hν : Matrix (Fin 2) (Fin 2) K)) :
    pgl2InnerAutPSL2 K hK hcard (N0 ν hν) (mk A) = mk A' := by
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [toPGL_pgl2InnerAutPSL2_apply, mul_inv_eq_iff_eq_mul]
  change Matrix.ProjGenLinGroup.mk (nonsplitJ ν hν) *
      Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL A) =
    Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL A') *
      Matrix.ProjGenLinGroup.mk (nonsplitJ ν hν)
  rw [← map_mul, ← map_mul]
  congr 1
  ext i j
  exact congrFun (congrFun h i) j

theorem pgl2InnerAutPSL2_N0_of_mem_normalizer [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (hcard : 3 < Nat.card K) {ν : K} (hν : ¬ IsSquare ν) {g : PSL2 K}
    (hg : g ∈ Subgroup.normalizer (nonsplitTorus ν : Set (PSL2 K))) :
    pgl2InnerAutPSL2 K hK hcard (N0 ν (ne_zero_of_not_isSquare hν)) g = g := by
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨M, rfl⟩ := exists_mk_eq g
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [toPGL_pgl2InnerAutPSL2_apply, mul_inv_eq_iff_eq_mul]
  refine N0_mul_toPGL_mk_comm _ _ (mem_nonsplitSL_or_isAntiNS_of_mem_normalizer
    (ringChar_ne_two_of_isOddPrimePower hK) hν ?_ hg)
  rw [← Nat.card_eq_fintype_card]
  exact five_le_of_odd_of_three_lt (odd_of_isOddPrimePower hK) hcard

theorem normalizer_nonsplitTorus_le_fix_N0 [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (hcard : 3 < Nat.card K) {ν : K} (hν : ¬ IsSquare ν) :
    Subgroup.normalizer (nonsplitTorus ν : Set (PSL2 K)) ≤
      fixSubgroup (pgl2InnerAutPSL2 K hK hcard (N0 ν (ne_zero_of_not_isSquare hν))) :=
  fun _ hg => pgl2InnerAutPSL2_N0_of_mem_normalizer hK hcard hν hg

theorem pgl2InnerAutPSL2_N0_mul_self [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (hcard : 3 < Nat.card K) (ν : K) (hν : ν ≠ 0) :
    pgl2InnerAutPSL2 K hK hcard (N0 ν hν) * pgl2InnerAutPSL2 K hK hcard (N0 ν hν) = 1 := by
  rw [← map_mul, N0_mul_self, map_one]

theorem pgl2InnerAutPSL2_N0_ne_one [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (hcard : 3 < Nat.card K) (ν : K) (hν : ν ≠ 0) :
    pgl2InnerAutPSL2 K hK hcard (N0 ν hν) ≠ 1 := fun h =>
  N0_ne_one ν hν (pgl2InnerAutPSL2_injective K hK hcard (h.trans (map_one _).symm))

theorem isCoatom_fixSubgroup_N0 [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) (hq7 : Nat.card K ≠ 7)
    (hq9 : Nat.card K ≠ 9) {ν : K} (hν : ¬ IsSquare ν) :
    IsCoatom (fixSubgroup (pgl2InnerAutPSL2 K hK hcard (N0 ν (ne_zero_of_not_isSquare hν)))) := by
  obtain ⟨p, n, hp, hp2, hKcard⟩ := exists_prime_pow_of_isOddPrimePower hK
  have hq5 : 5 ≤ p ^ n := hKcard ▸ five_le_of_odd_of_three_lt (odd_of_isOddPrimePower hK) hcard
  have hcoN := CFSG.Glauberman.Dickson.MaxUp.isCoatom_normalizer_nonsplitTorus hKcard hp2 hq5
    (hKcard ▸ hq7) (hKcard ▸ hq9) hν
  have hle := normalizer_nonsplitTorus_le_fix_N0 hK hcard hν
  have hne : fixSubgroup (pgl2InnerAutPSL2 K hK hcard (N0 ν (ne_zero_of_not_isSquare hν))) ≠ ⊤ :=
    fun htop => pgl2InnerAutPSL2_N0_ne_one hK hcard ν (ne_zero_of_not_isSquare hν)
      (MulEquiv.ext fun x => mem_fixSubgroup_iff.1 (htop ▸ Subgroup.mem_top x))
  rw [(hcoN.le_iff_eq hne).1 hle]
  exact hcoN

theorem invAutGen_pgl2_nonsplit_involution [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) (hq7 : Nat.card K ≠ 7)
    (hq9 : Nat.card K ≠ 9) {ν : K} (hν : ¬ IsSquare ν) :
    InvAutGen (PSL2 K) (pgl2InnerAutPSL2 K hK hcard (N0 ν (ne_zero_of_not_isSquare hν))) :=
  invAutGen_of_isCoatom_fix (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega))
    psl2_nonabelian (pgl2InnerAutPSL2_N0_mul_self hK hcard _ _)
    (pgl2InnerAutPSL2_N0_ne_one hK hcard _ _) (isCoatom_fixSubgroup_N0 hK hcard hq7 hq9 hν)

end CFSG.Quasithin.F7Two

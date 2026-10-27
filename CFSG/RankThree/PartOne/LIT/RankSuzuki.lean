module

public import Mathlib
public import CFSG.StronglyEmbedded.Catalog.Suzuki
public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.RankThree.PartOne.LIT.RankMatrix
public import CFSG.Open.Defs

public section

namespace CFSG.RankThree.PartOne.LIT

open Matrix CFSG.BenderSuzuki.MatrixGroups

theorem suzukiRoot_form (m : ℕ) (a b : GaloisField 2 (2 * m + 1)) :
    (SuzukiRootMatrix m a b)ᵀ * SuzukiWeylMatrix m * SuzukiRootMatrix m a b =
      SuzukiWeylMatrix m := by
  have h2 : (2 : GaloisField 2 (2 * m + 1)) = 0 := CharTwo.two_eq_zero
  have h4 : (4 : GaloisField 2 (2 * m + 1)) = 0 := by linear_combination 2 * h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiRootMatrix, SuzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four] <;>
    ring_nf <;> simp [h2, h4]

theorem suzukiTorus_form (m : ℕ) (x : (GaloisField 2 (2 * m + 1))ˣ) :
    (SuzukiTorusMatrix m x)ᵀ * SuzukiWeylMatrix m * SuzukiTorusMatrix m x =
      SuzukiWeylMatrix m := by
  have hx1 : ((x : GaloisField 2 (2 * m + 1)) ^ (1 + 2 ^ m)) ≠ 0 := pow_ne_zero _ x.ne_zero
  have hx2 : ((x : GaloisField 2 (2 * m + 1)) ^ (2 ^ m)) ≠ 0 := pow_ne_zero _ x.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiTorusMatrix, SuzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four, hx1, hx2]

theorem suzukiWeyl_form (m : ℕ) :
    (SuzukiWeylMatrix m : Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1)))ᵀ *
      SuzukiWeylMatrix m * SuzukiWeylMatrix m = SuzukiWeylMatrix m := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four]

theorem suzukiWeyl_alt (m : ℕ) (v : Fin 4 → GaloisField 2 (2 * m + 1)) :
    v ⬝ᵥ (SuzukiWeylMatrix m *ᵥ v) = 0 := by
  have h2 : (2 : GaloisField 2 (2 * m + 1)) = 0 := CharTwo.two_eq_zero
  simp [SuzukiWeylMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  linear_combination (v 0 * v 3 + v 1 * v 2) * h2

theorem suzukiWeyl_det (m : ℕ) : (SuzukiWeylMatrix m : Matrix (Fin 4) (Fin 4)
    (GaloisField 2 (2 * m + 1))).det ≠ 0 := by
  have h : (SuzukiWeylMatrix m : Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1))) *
      SuzukiWeylMatrix m = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SuzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four]
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at this
  exact left_ne_zero_of_mul_eq_one this

theorem pRank_suzukiMatrixGroup_le (m : ℕ) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (⊤ : Subgroup (SuzukiMatrixGroup m)) ≤ 2 := by
  have hrK : (r : GaloisField 2 (2 * m + 1)) ≠ 0 := natCast_ne_zero_of_charTwo hr hr2
  have hH : ∀ h ∈ SuzukiMatrixSubgroup m,
      (h : Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1)))ᵀ * SuzukiWeylMatrix m *
        (h : Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * m + 1))) = SuzukiWeylMatrix m :=
    mem_closure_form (by
      rintro g (⟨a, b, rfl⟩ | ⟨x, rfl⟩ | rfl)
      · exact suzukiRoot_form m a b
      · exact suzukiTorus_form m x
      · exact suzukiWeyl_form m)
  have := pRank_le_half_of_form_gl hr hrK (SuzukiWeylMatrix m) (suzukiWeyl_det m)
    (suzukiWeyl_alt m) (SuzukiMatrixSubgroup m) hH
  simpa using this

theorem pRank_le_two_of_suzuki {G : Type} [Group G] [Finite G] {m : ℕ}
    (hm : (TauCeti.LieTypeIndex.suzuki m).Valid)
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) : CFSG.Open.pRank r (⊤ : Subgroup G) ≤ 2 := by
  have e' : G ≃* SuzukiMatrixGroup m :=
    e.trans (CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hm)
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e']
  exact pRank_suzukiMatrixGroup_le m hr hr2

end CFSG.RankThree.PartOne.LIT

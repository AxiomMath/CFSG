module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowETools

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429E

open CFSG
open scoped Matrix

section Table

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

theorem eq_sum_of_commute {y X kr kr' : Matrix ι ι R} {v : ι → R} {M : ι → Matrix ι ι R}
    {e : ι → ℕ} (hM : ∀ j, M j = y ^ e j) (hkr : ∀ i j, kr i j = (M j *ᵥ v) i)
    (hinv : kr' * kr = 1) (hX : X * y = y * X) :
    X = ∑ j, (kr' *ᵥ (X *ᵥ v)) j • M j := by
  have h := eq_krylovPoly_of_commute (e := e) (fun i j => (hkr i j).trans (by rw [hM])) hinv hX
  calc X = krylovPoly y kr' e (X *ᵥ v) := h
    _ = ∑ j, (kr' *ᵥ (X *ᵥ v)) j • M j := by simp only [krylovPoly, hM]

end Table

theorem det_eq_one_of_mem_statedSU {n q : ℕ} {K : Type} [Field K] {A : GL (Fin n) K}
    (hA : A ∈ CFSG.Open.StatedSU n q K) : (A : Matrix (Fin n) (Fin n) K).det = 1 := by
  have hle : CFSG.Open.StatedSU n q K ≤
      (Matrix.GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker := by
    unfold CFSG.Open.StatedSU
    rw [Subgroup.closure_le]
    rintro B ⟨hB, -⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    exact Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, hB, Units.val_one])
  have h := hle hA
  rw [MonoidHom.mem_ker] at h
  have h' := congrArg Units.val h
  rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h'

end CFSG.RankThree.PartTwo.Sec4.RonanK429E

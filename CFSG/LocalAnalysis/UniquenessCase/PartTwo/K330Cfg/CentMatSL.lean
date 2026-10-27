module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.CentPslNo
public import CFSG.Open.StatedAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open

theorem pow_eq_one_of_mem_scalars {n : ℕ} {F : Type} [Field F] {H : Subgroup (GL (Fin n) F)}
    (hH : H ≤ StatedSL n F) {z : H} (hz : z ∈ (StatedScalars (Fin n) F).subgroupOf H) :
    z ^ n = 1 := by
  rw [Subgroup.mem_subgroupOf] at hz
  obtain ⟨c, hc⟩ := hz
  have hdet : (z : GL (Fin n) F) ∈ StatedSL n F := hH z.2
  have hdet1 :
      (Matrix.GeneralLinearGroup.scalar (Fin n) c : Matrix (Fin n) (Fin n) F).det = 1 := by
    rw [hc]
    exact CFSG.Open.StatedAPI.det_of_mem_statedSL hdet
  have hc1 : ((c : F)) ^ n = 1 := by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet1
    exact hdet1
  have hc1' : c ^ n = 1 := Units.ext (by simpa using hc1)
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hc, ← map_pow, hc1', map_one]

theorem e9c7Free_statedSL {n : ℕ} (hn : n = 4 ∨ n = 5) {F : Type} [Field F] [Finite F]
    (hF3 : Nat.card F % 3 = 2) (h7 : ¬ 7 ∣ Nat.card F) (h7' : ¬ 7 ∣ Nat.card F ^ 2 - 1) :
    E9C7Free ↥(StatedSL n F) := by
  have hfac : Nat.card F ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
    simpa [mul_comm] using Nat.pow_two_sub_pow_two (Nat.card F) 1
  have h1 : ¬ 7 ∣ Nat.card F - 1 := by
    intro hd
    apply h7'
    rw [hfac]
    exact dvd_mul_of_dvd_left hd _
  have h2 : ¬ 7 ∣ Nat.card F + 1 := by
    intro hd
    apply h7'
    rw [hfac]
    exact dvd_mul_of_dvd_right hd _
  have hn' : Module.finrank F (Fin n → F) = 4 ∨ Module.finrank F (Fin n → F) = 5 := by
    rw [Module.finrank_fin_fun F]
    exact hn
  have hfree : E9C7Free ((Fin n → F) ≃ₗ[F] (Fin n → F)) := fun x y r =>
    psl_no_e9c7 hn' hF3 ⟨h7, h1, h2⟩ x y r
  refine e9c7Free_subgroup (StatedSL n F) (e9c7Free_of_injective
    (Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin n → F))).toMonoidHom ?_ hfree)
  exact (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin n → F))).injective

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

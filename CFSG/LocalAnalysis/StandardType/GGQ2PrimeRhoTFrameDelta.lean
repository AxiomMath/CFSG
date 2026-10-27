module

public import CFSG.Fischer.Polar.Delta
public import CFSG.RankThree.PartOne.KF.UnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTFrameKer
import all CFSG.Fischer.F4

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Fischer
open CFSG.RankThree.PartOne.KFU (diagU diagU_val diagUHom)

private noncomputable def rhoTFrame_permGL : Equiv.Perm (Fin 6) →* GL (Fin 6) F4 :=
  Matrix.permMatrixHom.toHomUnits

private theorem rhoTFrame_coe_permGL (σ : Equiv.Perm (Fin 6)) :
    ((rhoTFrame_permGL σ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      (σ⁻¹).permMatrix F4 := rfl

private theorem rhoTFrame_coe_permGL_inv (σ : Equiv.Perm (Fin 6)) :
    (((rhoTFrame_permGL σ)⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      σ.permMatrix F4 := by
  rw [← map_inv, rhoTFrame_coe_permGL, inv_inv]

private theorem rhoTFrame_permGL_conj (σ : Equiv.Perm (Fin 6)) (d : Fin 6 → F4ˣ) :
    rhoTFrame_permGL σ * diagU d * (rhoTFrame_permGL σ)⁻¹ = diagU (fun i => d (σ⁻¹ i)) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, rhoTFrame_coe_permGL_inv, rhoTFrame_coe_permGL, diagU_val,
    diagU_val]
  ext i k
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  rw [Finset.sum_eq_single (σ.symm i)]
  · simp
  · intro x _ hx
    simp [Ne.symm hx]
  · simp

private theorem rhoTFrame_permGL_mem (σ : Equiv.Perm (Fin 6)) : rhoTFrame_permGL σ ∈ GU0 := by
  show IsIsom _
  intro x y
  have hmul : ∀ x : W, ((σ⁻¹).permMatrix F4).mulVec x = fun i => x (σ⁻¹ i) := by
    intro x
    ext i
    simp [Matrix.mulVec, dotProduct, PEquiv.toMatrix_apply]
  rw [rhoTFrame_coe_permGL, hmul, hmul, herm_eq, herm_eq]
  exact Equiv.sum_comp σ⁻¹ (fun i => x i * y i ^ 2)

private def rhoTFrame_ωu : F4ˣ := Units.mk0 F4.ω (by decide)

private theorem rhoTFrame_deltaGU_zpow (k : ℤ) :
    ((deltaGU ^ k : GU0) : GL (Fin 6) F4) =
      diagU (fun i : Fin 6 => if i = 0 then rhoTFrame_ωu ^ k else 1) := by
  have h1 : ((deltaGU : GU0) : GL (Fin 6) F4) =
      diagU (fun i : Fin 6 => if i = 0 then rhoTFrame_ωu else 1) := by
    apply Units.ext
    rw [deltaGU_val, diagU_val, deltaM]
    congr 1
    funext i
    by_cases hi : i = 0 <;> simp [hi, rhoTFrame_ωu]
  have h2 : diagU (fun i : Fin 6 => if i = 0 then rhoTFrame_ωu ^ k else 1) =
      diagUHom (fun i : Fin 6 => if i = 0 then rhoTFrame_ωu else 1) ^ k := by
    rw [← map_zpow]
    show _ = diagU _
    congr 1
    funext i
    by_cases hi : i = 0 <;> simp [hi]
  rw [h2, Subgroup.coe_zpow, h1]
  rfl

theorem rhoTFrame_exists_conj_delta
    {y z : GU0} {wd : Fin 6 → F4ˣ} {k₀ : Fin 6} {c u : F4ˣ} (hu : u ≠ 1)
    (hyz : (y : GL (Fin 6) F4)⁻¹ * (z : GL (Fin 6) F4) * (y : GL (Fin 6) F4) = diagU wd)
    (hwd : ∀ k, wd k = if k = k₀ then c * u else c) :
    ∃ (y' : GU0) (k : ℤ), (k = 1 ∨ k = -1) ∧ piGU z = piGU (y' * deltaGU ^ k * y'⁻¹) := by
  obtain ⟨k, hk, huk⟩ : ∃ k : ℤ, (k = 1 ∨ k = -1) ∧ u = rhoTFrame_ωu ^ k := by
    have h3 : ∀ u : F4ˣ, u ≠ 1 → u = rhoTFrame_ωu ∨ u = rhoTFrame_ωu⁻¹ := by decide
    rcases h3 u hu with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, zpow_one]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h, zpow_neg_one]⟩
  let τ : Equiv.Perm (Fin 6) := Equiv.swap 0 k₀
  let P : GU0 := ⟨rhoTFrame_permGL τ, rhoTFrame_permGL_mem τ⟩
  refine ⟨y * P, k, hk, ?_⟩
  have hτ : ∀ i, τ⁻¹ i = 0 ↔ i = k₀ := by
    intro i
    rw [Equiv.Perm.inv_eq_iff_eq]
    simp [τ, eq_comm]
  have hdiag : diagU wd = scalarGL c * diagU (fun i => (if τ⁻¹ i = 0 then u else 1)) := by
    apply Units.ext
    rw [Units.val_mul, scalarGL_val, diagU_val, diagU_val, Matrix.smul_mul, Matrix.one_mul]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul, hwd]
      by_cases hi : i = k₀
      · rw [if_pos hi, if_pos ((hτ i).2 hi)]
        simp
      · rw [if_neg hi, if_neg (fun h => hi ((hτ i).1 h))]
        simp
    · simp [Matrix.diagonal_apply_ne _ hij]
  have hcomm : diagU (fun i => (if τ⁻¹ i = 0 then u else 1)) =
      rhoTFrame_permGL τ * ((deltaGU ^ k : GU0) : GL (Fin 6) F4) * (rhoTFrame_permGL τ)⁻¹ := by
    rw [rhoTFrame_deltaGU_zpow, rhoTFrame_permGL_conj, huk]
  have key : (z : GL (Fin 6) F4) = scalarGL c *
      (((y * P) * deltaGU ^ k * (y * P)⁻¹ : GU0) : GL (Fin 6) F4) := by
    have h1 : (z : GL (Fin 6) F4) = y * diagU wd * (y : GL (Fin 6) F4)⁻¹ := by
      rw [← hyz]
      group
    rw [h1, hdiag, hcomm]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, P]
    rw [← mul_assoc (y : GL (Fin 6) F4) (scalarGL c), (scalarGL_central c y).symm]
    group
  have hz : z = ⟨scalarGL c, SU0_le_GU0 (scalarGL_mem c)⟩ * (y * P * deltaGU ^ k * (y * P)⁻¹) :=
    Subtype.ext key
  have h1 : piGU ⟨scalarGL c, SU0_le_GU0 (scalarGL_mem c)⟩ = 1 := rhoTFrame_piSU_scalarGL c
  rw [hz, map_mul, h1, one_mul]

end CFSG.GGQ2Prime

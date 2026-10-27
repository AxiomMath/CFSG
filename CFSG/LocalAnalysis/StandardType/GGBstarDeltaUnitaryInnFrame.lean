module

public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryMat
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryField
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepairPair

public section

namespace CFSG.StandardType

namespace TableBUI

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher InndiagSU
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective det_diagHom)

variable {K : Type} [Field K] {d n : ℕ} (h : UnitaryFieldData 2 n K)

theorem mem_scalars_of_projU_eq_one {w : ↥(unitarySU 2 n K d)} (hw : projU n d K w = 1) :
    (w : GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K := by
  have h1 := (QuotientGroup.eq_one_iff (N := (LargeEvenScalars (Fin d) K).subgroupOf
    (LargeEvenSUGroup (Fin d) K (2 ^ n))) (show LargeEvenSUGroup (Fin d) K (2 ^ n) from w)).mp hw
  exact Subgroup.mem_subgroupOf.mp h1

theorem exists_scalar_of_frameMk_eq (P : GL (Fin d) K)
    (hP : P ∈ primeFormUnitary h (idGram K d)) {u v : ↥(unitarySU 2 n K d)}
    (huv : frameMk h P hP u = frameMk h P hP v) :
    ∃ c : Kˣ, (v : GL (Fin d) K) = Matrix.GeneralLinearGroup.scalar (Fin d) c * u := by
  have h0 : projU n d K ((TableBUE.conjSU h P hP).symm (u⁻¹ * v)) = 1 := by
    rw [← frameMk_apply, map_mul, map_inv, huv, inv_mul_cancel]
  obtain ⟨c, hc⟩ := mem_scalars_of_projU_eq_one h0
  have hcc := Subgroup.mem_center_iff.mp (TableB.scalars_le_center (ι := Fin d) (K := K) ⟨c, rfl⟩)
  refine ⟨c, ?_⟩
  have e1 : (Matrix.GeneralLinearGroup.scalar (Fin d) c : GL (Fin d) K) =
      P * ((u : GL (Fin d) K)⁻¹ * v) * P⁻¹ := by
    rw [hc, coe_conjSU_symm]
    rfl
  have e2 : (u : GL (Fin d) K)⁻¹ * v = Matrix.GeneralLinearGroup.scalar (Fin d) c := by
    have h3 : P⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin d) c * P =
        Matrix.GeneralLinearGroup.scalar (Fin d) c := by
      rw [mul_assoc, ← hcc P, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [← h3, e1]
    group
  calc (v : GL (Fin d) K) = u * ((u : GL (Fin d) K)⁻¹ * v) := by group
    _ = u * Matrix.GeneralLinearGroup.scalar (Fin d) c := by rw [e2]
    _ = Matrix.GeneralLinearGroup.scalar (Fin d) c * u := hcc u

theorem ker_frameMk_le_center (P : GL (Fin d) K) (hP : P ∈ primeFormUnitary h (idGram K d)) :
    (frameMk h P hP).ker ≤ Subgroup.center ↥(unitarySU 2 n K d) := by
  intro u hu
  have hu' : frameMk h P hP 1 = frameMk h P hP u := by
    rw [map_one]
    exact hu.symm
  obtain ⟨c, hc⟩ := exists_scalar_of_frameMk_eq h P hP hu'
  have hcc := Subgroup.mem_center_iff.mp (TableB.scalars_le_center (ι := Fin d) (K := K) ⟨c, rfl⟩)
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  change (g : GL (Fin d) K) * u = u * g
  rw [hc, Subgroup.coe_one, mul_one, hcc]

theorem frameActs_of_eq (P : GL (Fin d) K) (hP : P ∈ primeFormUnitary h (idGram K d))
    {x : ↥(unitarySU 2 n K d)} {σ : Fin d → Kˣ}
    (hx : (TableBUE.conjSU h P hP x : GL (Fin d) K) = diagHom d σ)
    (hσ : ∀ k, ((σ k : Kˣ) : K) ^ (2 ^ n + 1) = 1) :
    SURep.GGFrameActs (frameMk h P hP) (projU n d K x) σ := by
  have hx' : (x : GL (Fin d) K) = P * diagHom d σ * P⁻¹ := by
    rw [← hx, TableBUE.coe_conjSU]
    group
  refine ⟨hσ, fun s s' hss' => ?_⟩
  rw [frameMk_apply, frameMk_apply, ← map_mul, ← map_inv, ← map_mul]
  congr 1
  apply Subtype.ext
  change (x : GL (Fin d) K) * (P * s * P⁻¹) * (x : GL (Fin d) K)⁻¹ = P * s' * P⁻¹
  rw [hx', hss']
  group

theorem glAut_diagHom_of_pow {p : ℕ} (hp : p.Prime) {φ : K ≃+* K} (hφ : φ ^ p = 1)
    {σ : Fin d → Kˣ} (hσ : ∀ k, σ k ^ p = 1) : glAut φ (diagHom d σ) = diagHom d σ := by
  rw [TableBUM.glAut_diagHom]
  congr 1
  funext k
  apply Units.ext
  rw [Units.coe_map]
  exact TableBUF.ringEquiv_apply_eq_of_pow_eq_one hp hφ (by
    rw [← Units.val_pow_eq_pow_val, hσ k, Units.val_one])

theorem semilinNorm_diagHom (β : Fin d → Kˣ) (φ : K ≃+* K) (m : ℕ) :
    semilinNorm (diagHom d β) φ m =
      diagHom d (fun k => ∏ l ∈ Finset.range m, Units.map ((φ ^ l : K ≃+* K) : K →* K) (β k)) := by
  induction m with
  | zero =>
    rw [semilinNorm]
    simp only [Finset.range_zero, Finset.prod_empty]
    rw [show (fun _ : Fin d => (1 : Kˣ)) = 1 from rfl, map_one]
  | succ m ih =>
    rw [semilinNorm, ih, TableBUM.glAut_diagHom, ← map_mul]
    congr 1
    funext k
    rw [Pi.mul_apply, Finset.prod_range_succ]

end TableBUI

end CFSG.StandardType

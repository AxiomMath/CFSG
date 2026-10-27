module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsModel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryModelPointStructure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphismCoord
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitarySublineAutomorphism

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryHulls

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped LinearAlgebra.Projectivization

variable {K : Type} [Field K] {J : HermitianForm 3 K} {C : Subgroup J.specialSubgroup} [C.Normal]

@[expose] def torusCoord (c : normOne J) (z : hermitianUnipotentCoord J) :
    hermitianUnipotentCoord J :=
  ⟨(((c : Kˣ) : K) ^ 3 * z.1.1, z.1.2), by
    have hc : ((c : Kˣ) : K) * J.conj ((c : Kˣ) : K) = 1 := c.2
    have hz := z.2
    dsimp only
    rw [map_mul, map_pow]
    linear_combination hz + z.1.1 * J.conj z.1.1 *
      (((c : Kˣ) : K) ^ 2 * J.conj ((c : Kˣ) : K) ^ 2 + ((c : Kˣ) : K) * J.conj ((c : Kˣ) : K) + 1)
      * hc⟩

theorem torus_conj_heisL (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (c : normOne J)
    (z : hermitianUnipotentCoord J) :
    QuotientGroup.mk' C (torusHom J hJ c) * heisL J C hJ z *
        (QuotientGroup.mk' C (torusHom J hJ c))⁻¹ = heisL J C hJ (torusCoord c z) := by
  change ((torusHom J hJ c * hermitianUnipotentSU J hJ z * (torusHom J hJ c)⁻¹ :
    J.specialSubgroup) : J.specialSubgroup ⧸ C) = heisL J C hJ (torusCoord c z)
  congr 1
  have hc : J.conj ((c : Kˣ) : K) = ((c : Kˣ) : K)⁻¹ := conj_eq_inv_of_mem_normOne J c.2
  have hc0 : ((c : Kˣ) : K) ≠ 0 := (c : Kˣ).ne_zero
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
  rw [coe_torusHom, coe_hermitianUnipotentSU, coe_hermitianUnipotentSU, coe_diag3,
    coe_diag3_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, torusCoord, map_mul, map_pow, hc] <;>
    field_simp

theorem glAut_conj_hermitianUnipotentGL (z : hermitianUnipotentCoord J) :
    glAut J.conj (hermitianUnipotentGL J z) = hermitianUnipotentGL J (rootTau J z) := by
  apply Units.ext
  rw [coe_glAut, hermitianUnipotentGL_val, hermitianUnipotentGL_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermitianUnipotentMatrix, J.conj_involutive _]

theorem diag3_one_smul_point (e : Kˣ) {i : Fin 3} (hi : i ≠ 1) :
    ProjGenLinGroup.mk (diag3 1 e 1) • unitaryCoordinatePoint (K := K) i =
      unitaryCoordinatePoint i := by
  rw [unitary_projective_coordinate_maps_iff]
  intro k hk
  rw [coe_diag3]
  fin_cases i <;> fin_cases k <;> simp_all

variable [CharP K 2] [Finite K]

omit [CharP K 2] in
theorem coverToPGL_sublineAutHom_inl (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) (e : normOne J) (x : J.specialSubgroup ⧸ C) :
    coverToPGL J C hJ hC (sublineAutHom J C hJ hC (SemidirectProduct.inl e) x) =
      ProjGenLinGroup.mk (diag3 1 (e : Kˣ) 1) * coverToPGL J C hJ hC x *
        (ProjGenLinGroup.mk (diag3 1 (e : Kˣ) 1))⁻¹ := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C x
  obtain ⟨hg, h⟩ := sublineAutHom_mk hJ hC (SemidirectProduct.inl e) g
  change coverToPGL J C hJ hC (sublineAutHom J C hJ hC (SemidirectProduct.inl e)
    (g : J.specialSubgroup ⧸ C)) = _
  rw [h, coverToPGL_mk, show coverToPGL J C hJ hC ((QuotientGroup.mk' C) g) =
    ProjGenLinGroup.mk (g : GL (Fin 3) K) from rfl]
  simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl, OneMemClass.coe_one,
    map_one, MulAut.one_apply, map_mul, map_inv]

omit [CharP K 2] in
theorem sublineAutHom_inl_smul_iff (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) (e : normOne J) (x : J.specialSubgroup ⧸ C) {i : Fin 3}
    (hi : i ≠ 1) :
    coverToPGL J C hJ hC (sublineAutHom J C hJ hC (SemidirectProduct.inl e) x) •
        unitaryCoordinatePoint (K := K) 0 = unitaryCoordinatePoint i ↔
      coverToPGL J C hJ hC x • unitaryCoordinatePoint (K := K) 0 = unitaryCoordinatePoint i := by
  rw [coverToPGL_sublineAutHom_inl, mul_smul, mul_smul,
    inv_smul_eq_iff.mpr (diag3_one_smul_point (e : Kˣ) (i := 0) (by decide)).symm]
  constructor
  · intro h
    have h' := congrArg (fun P => (ProjGenLinGroup.mk (diag3 1 (e : Kˣ) 1))⁻¹ • P) h
    simp only [inv_smul_smul] at h'
    rw [h', inv_smul_eq_iff, diag3_one_smul_point _ hi]
  · intro h
    rw [h, diag3_one_smul_point _ hi]

theorem sublineAutHom_bar_heisL {f : ℕ} (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hC : C ≤ scalarCenter J)
    (z : hermitianUnipotentCoord J) :
    sublineAutHom J C hJ hC (SemidirectProduct.inr ⟨J.conj, Subgroup.mem_zpowers _⟩)
        (heisL J C hJ z) = heisL J C hJ (rootTau J z) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hbar, -⟩ :=
    unitary_central_cover_subline_automorphism_two_part J f hf hcard hfixed hJ C hC
  obtain ⟨hg, h⟩ := hbar (hermitianUnipotentSU J hJ z)
  change sublineAutHom J C hJ hC (SemidirectProduct.inr ⟨J.conj, Subgroup.mem_zpowers _⟩)
    ((hermitianUnipotentSU J hJ z : J.specialSubgroup) : J.specialSubgroup ⧸ C) = _
  rw [h]
  change _ = ((hermitianUnipotentSU J hJ (rootTau J z) : J.specialSubgroup) :
    J.specialSubgroup ⧸ C)
  congr 1
  exact Subtype.ext (glAut_conj_hermitianUnipotentGL z)

omit [CharP K 2] in
theorem heisL_regular {f : ℕ} (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hC : C ≤ scalarCenter J)
    {x y : J.specialSubgroup ⧸ C}
    (hx : coverToPGL J C hJ hC x • unitaryCoordinatePoint (K := K) 0 ≠ unitaryCoordinatePoint 0)
    (hy : coverToPGL J C hJ hC y • unitaryCoordinatePoint (K := K) 0 ≠ unitaryCoordinatePoint 0) :
    ∃! z : hermitianUnipotentCoord J,
      coverToPGL J C hJ hC (heisL J C hJ z) • (coverToPGL J C hJ hC x • unitaryCoordinatePoint 0) =
        coverToPGL J C hJ hC y • unitaryCoordinatePoint (K := K) 0 := by
  obtain ⟨-, -, -, -, -, rho, -, hnative, -, -, -, -, -, -, -, -, -, -, -, -, hreg, -⟩ :=
    UnitaryModel.unitary_three_point_structure J f hf hcard hfixed hJ
  set α := unitaryOuterIsotropicPoint J hJ 0 (by decide)
  set b := rho (coverToPSU J C hJ hC x) α
  set c := rho (coverToPSU J C hJ hC y) α
  have hb : (b : ℙ K (Fin 3 → K)) = coverToPGL J C hJ hC x • unitaryCoordinatePoint 0 :=
    hnative _ _
  have hc : (c : ℙ K (Fin 3 → K)) = coverToPGL J C hJ hC y • unitaryCoordinatePoint 0 :=
    hnative _ _
  have hbα : b ≠ α := fun h => hx (by rw [← hb, h]; rfl)
  have hcα : c ≠ α := fun h => hy (by rw [← hc, h]; rfl)
  obtain ⟨⟨u, w, rfl⟩, hu, huniq⟩ := hreg b c hbα hcα
  have hmove : ∀ z : hermitianUnipotentCoord J,
      coverToPGL J C hJ hC (heisL J C hJ z) • (b : ℙ K (Fin 3 → K)) =
        ((rho (hermitianUnipotentPSU J hJ z) b : unitaryIsotropicPoints J) :
          ℙ K (Fin 3 → K)) := fun z => by
    rw [hnative (hermitianUnipotentPSU J hJ z) b, hermitianUnipotentPSU_val]
    rfl
  refine ⟨w, ?_, fun z hz => ?_⟩
  · show coverToPGL J C hJ hC (heisL J C hJ w) •
      (coverToPGL J C hJ hC x • unitaryCoordinatePoint 0) = _
    rw [← hb]
    exact (hmove w).trans ((congrArg Subtype.val hu).trans hc)
  · have hz' : rho ((⟨hermitianUnipotentPSU J hJ z, z, rfl⟩ :
        (hermitianUnipotentPSU J hJ).range) : ProjectiveSpecialUnitaryMatrixGroup J) b = c := by
      apply Subtype.ext
      rw [← hmove, hb, hz, hc]
    have h := congrArg Subtype.val (huniq _ hz')
    have h' := congrArg (fun g : ProjectiveSpecialUnitaryMatrixGroup J =>
      (g : ProjGenLinGroup (Fin 3) K)) h
    simp only [hermitianUnipotentPSU_val] at h'
    exact hermitianUnipotentGL_mk_injective h'

end CFSG.ShultStronglyClosedTI.UnitaryHulls

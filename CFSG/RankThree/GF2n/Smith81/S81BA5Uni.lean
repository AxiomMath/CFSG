module

public import CFSG.RankThree.GF2n.Smith81.S81A5KerRho
public import CFSG.RankThree.GF2n.Smith81.S81BA5Def

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.A5Cube

section CubeHom

variable (K : Type) [Field K] [CharP K 2]

theorem cubeHom_scalar_le :
    (StatedScalars (Fin 6) K).subgroupOf (StatedSL 6 K) ≤
      ((rhoEquiv K).comp (StatedSL 6 K).subtype).ker := by
  intro x hx
  have hx' : (x : GL (Fin 6) K) ∈ (Matrix.GeneralLinearGroup.scalar (Fin 6)).range :=
    Subgroup.mem_subgroupOf.mp hx
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hx'
  have hdet : ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 :=
    CFSG.Open.StatedAPI.mem_statedSL_iff.mp x.2
  have hmat : ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = (c : K) • 1 := by
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  have h6 : (c : K) ^ 6 = 1 := by
    rw [hmat, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
    exact hdet
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : ((c : K) ^ 3 - 1) ^ 2 = 0 := by
    linear_combination h6 + (1 - (c : K) ^ 3) * h2
  have hc3 : (c : K) ^ 3 = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq)
  have hrho : rho K (x : GL (Fin 6) K) = 1 :=
    (rho_eq_one_iff (x : GL (Fin 6) K)).mpr ⟨(c : K), hc3, hmat⟩
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.subtype_apply]
  refine LinearEquiv.ext fun ξ => ?_
  rw [rhoEquiv_apply, hrho]
  rfl

@[expose] noncomputable def cubeHom : StatedProj (StatedSL 6 K) →* (Cube K ≃ₗ[K] Cube K) :=
  QuotientGroup.lift ((StatedScalars (Fin 6) K).subgroupOf (StatedSL 6 K))
    ((rhoEquiv K).comp (StatedSL 6 K).subtype) (cubeHom_scalar_le K)

variable {K}

theorem cubeHom_mk (g : ↥(StatedSL 6 K)) :
    cubeHom K (QuotientGroup.mk g) = rhoEquiv K (g : GL (Fin 6) K) := rfl

theorem cubeHom_injective : Function.Injective (cubeHom K) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
  rw [cubeHom_mk] at ha
  have hrho : rho K (g : GL (Fin 6) K) = 1 := by
    refine LinearMap.ext fun ξ => ?_
    have h1 := LinearEquiv.congr_fun ha ξ
    rw [rhoEquiv_apply] at h1
    exact h1
  obtain ⟨l, hl3, hl⟩ := (rho_eq_one_iff (g : GL (Fin 6) K)).mp hrho
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at hl3
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  refine ⟨Units.mk0 l hl0, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, hl, Matrix.scalar_apply,
    Matrix.smul_one_eq_diagonal]

theorem cubeHom_range : (cubeHom K).range = Gam K := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
    rw [cubeHom_mk]
    exact Subgroup.mem_map_of_mem _ g.2
  · intro hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    exact MonoidHom.mem_range.mpr ⟨QuotientGroup.mk ⟨g, hg⟩, cubeHom_mk ⟨g, hg⟩⟩

end CubeHom

end CFSG.RankThree.GF2n.Smith81

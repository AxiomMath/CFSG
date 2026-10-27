module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteA4F4

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.RootSystem

private theorem ggE6Row_coxeterE6_eq :
    CoxeterMatrix.E₆ = coxeterMatrix (isFiniteType_cartan .E6) :=
  (coxeterMatrix_eq_of_ggIntCartan (C := Tag.cartan .E6) (isFiniteType_cartan .E6)
    (by
      show GGIntCartan CoxeterMatrix.E₆ (Tag.cartanE 6)
      rw [cartanE_eq 6]
      exact ggIntCartan_E₆)).symm

private theorem ggE6Row_coxeterLift : CoxeterMatrix.E₆.IsLiftable (fun i => simple .E6 i) :=
  fun i j => by
    rw [ggE6Row_coxeterE6_eq]
    exact (CFSG.LieType.Chevalley.coxeterSystem .E6).simple_mul_simple_pow i j

private theorem ggE6Row_coxeterLift_symm :
    (coxeterMatrix (isFiniteType_cartan .E6)).IsLiftable
      (fun i => CoxeterMatrix.E₆.simple i) :=
  fun i j => by
    rw [← ggE6Row_coxeterE6_eq]
    exact CoxeterMatrix.E₆.toCoxeterSystem.simple_mul_simple_pow i j

private noncomputable def ggE6Row_coxeterHom : CoxeterMatrix.E₆.Group →* WeylGroup .E6 :=
  CoxeterMatrix.E₆.toCoxeterSystem.lift ⟨fun i => simple .E6 i, ggE6Row_coxeterLift⟩

private noncomputable def ggE6Row_coxeterHomInv : WeylGroup .E6 →* CoxeterMatrix.E₆.Group :=
  (CFSG.LieType.Chevalley.coxeterSystem .E6).lift
    ⟨fun i => CoxeterMatrix.E₆.simple i, ggE6Row_coxeterLift_symm⟩

private theorem ggE6Row_coxeterHom_simple (i : Fin 6) :
    ggE6Row_coxeterHom (CoxeterMatrix.E₆.simple i) = simple .E6 i := by
  rw [← CoxeterMatrix.toCoxeterSystem_simple]
  exact CoxeterSystem.lift_apply_simple CoxeterMatrix.E₆.toCoxeterSystem ggE6Row_coxeterLift i

noncomputable def ggE6Row_coxeterGroupEquiv : CoxeterMatrix.E₆.Group ≃* WeylGroup Tag.E6 := by
  have h1 : ggE6Row_coxeterHomInv.comp ggE6Row_coxeterHom = MonoidHom.id _ := by
    refine CoxeterMatrix.E₆.toCoxeterSystem.ext_simple fun i => ?_
    have hψ : ggE6Row_coxeterHom (CoxeterMatrix.E₆.toCoxeterSystem.simple i) =
        simple .E6 i :=
      CoxeterSystem.lift_apply_simple CoxeterMatrix.E₆.toCoxeterSystem ggE6Row_coxeterLift i
    have hψ' : ggE6Row_coxeterHomInv (simple .E6 i) = CoxeterMatrix.E₆.simple i :=
      CoxeterSystem.lift_apply_simple (CFSG.LieType.Chevalley.coxeterSystem .E6)
        ggE6Row_coxeterLift_symm i
    rw [MonoidHom.comp_apply, MonoidHom.id_apply, hψ, hψ', CoxeterMatrix.toCoxeterSystem_simple]
  have h2 : ggE6Row_coxeterHom.comp ggE6Row_coxeterHomInv = MonoidHom.id _ := by
    refine (CFSG.LieType.Chevalley.coxeterSystem .E6).ext_simple fun i => ?_
    have hψ' : ggE6Row_coxeterHomInv (simple .E6 i) = CoxeterMatrix.E₆.simple i :=
      CoxeterSystem.lift_apply_simple (CFSG.LieType.Chevalley.coxeterSystem .E6)
        ggE6Row_coxeterLift_symm i
    have hψ : ggE6Row_coxeterHom (CoxeterMatrix.E₆.simple i) = simple .E6 i :=
      ggE6Row_coxeterHom_simple i
    rw [MonoidHom.comp_apply, MonoidHom.id_apply, hψ', hψ]
  exact MulEquiv.ofBijective ggE6Row_coxeterHom
    ⟨fun a b hab => by
      have ha := DFunLike.congr_fun h1 a
      have hb := DFunLike.congr_fun h1 b
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply] at ha hb
      rw [← ha, hab, hb],
     fun y => by
      have hh := DFunLike.congr_fun h2 y
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply] at hh
      exact ⟨ggE6Row_coxeterHomInv y, hh⟩⟩

theorem ggE6Row_coxeterGroupEquiv_simple (i : Fin 6) :
    ggE6Row_coxeterGroupEquiv (CoxeterMatrix.E₆.simple i) = simple Tag.E6 i := by
  change ggE6Row_coxeterHom (CoxeterMatrix.E₆.simple i) = simple Tag.E6 i
  rw [← CoxeterMatrix.toCoxeterSystem_simple]
  exact CoxeterSystem.lift_apply_simple CoxeterMatrix.E₆.toCoxeterSystem ggE6Row_coxeterLift i

end CFSG.StandardType

end

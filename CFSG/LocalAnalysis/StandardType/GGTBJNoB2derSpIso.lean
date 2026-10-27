module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derDefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearIsometry
public import CFSG.ClassicalGroups.Symplectic.StandardForm
import CFSG.LieType.Universal.SymplecticExtras.Matrices

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def ggB2der_bridge {K V : Type*} [CommSemiring K] [AddCommMonoid V]
    [Module K V] (B : LinearMap.BilinForm K V) :
    ↥(CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup B) ≃*
      ↥(TauCeti.BilinForm.isometryGroup B) := by
  let e := LinearMap.GeneralLinearGroup.generalLinearEquiv K V
  have hcoe : ∀ (g : V ≃ₗ[K] V) (x : V), ((↑(e.symm g) : V → V) x) = g x := by
    intro g x
    have h := LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv (R := K) (M := V) (e.symm g)
    rw [MulEquiv.apply_symm_apply] at h
    exact (congrFun h x).symm
  have he : (CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup B).map e.toMonoidHom =
      TauCeti.BilinForm.isometryGroup B := by
    ext g
    rw [Subgroup.mem_map_equiv, CFSG.LocalAnalysis.ComponentInitial.mem_bilinIsometryGroup,
      TauCeti.BilinForm.mem_isometryGroup_iff]
    constructor
    · intro h x y
      have := h x y
      rwa [hcoe g x, hcoe g y] at this
    · intro h x y
      rw [hcoe g x, hcoe g y]
      exact h x y
  exact (e.subgroupMap _).trans (MulEquiv.subgroupCongr he)

theorem ggB2der_bridge_coe {K V : Type*} [CommSemiring K] [AddCommMonoid V] [Module K V]
    (B : LinearMap.BilinForm K V)
    (x : ↥(CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup B)) :
    ((ggB2der_bridge B x : V ≃ₗ[K] V) : V →ₗ[K] V) = (x.1 : V →ₗ[K] V) := by
  change ((LinearMap.GeneralLinearGroup.generalLinearEquiv K V
    x.1 : V ≃ₗ[K] V) : V →ₗ[K] V) = (x.1 : V →ₗ[K] V)
  rw [LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap]

@[expose] noncomputable def ggB2der_spIso {K : Type} [Field K] [Finite K] [CharP K 2]
    {r : ℕ} [NeZero r] :
    LargeEvenProj (LargeEvenSpGroup K r) ≃*
      ↥(CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup (SmallRule.spBilin K r)) :=
  (TableBSymp.spProjEquivSp (K := K) (m := r)).trans
    (CFSG.ClassicalGroups.Symplectic.spEquiv (m := r) (K := K))

theorem ggB2der_spIso_coe {K : Type} [Field K] [Finite K] [CharP K 2]
    {r : ℕ} [NeZero r] (a : LargeEvenProj (LargeEvenSpGroup K r)) :
    ((ggB2der_spIso (K := K) (r := r) a :
      LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
      Module.End K (Fin r ⊕ Fin r → K)) =
      (SmallRule.spRep a : Module.End K (Fin r ⊕ Fin r → K)) := by
  refine LinearMap.ext fun v => ?_
  show (CFSG.ClassicalGroups.Symplectic.spEquiv
      (TableBSymp.spProjEquivSp (K := K) (m := r) a)).app v =
      (SmallRule.spRep a : Module.End K (Fin r ⊕ Fin r → K)) v
  rw [CFSG.ClassicalGroups.Symplectic.spEquiv_app, SmallRule.spRep_apply]
  rw [CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply]

end CFSG.StandardType

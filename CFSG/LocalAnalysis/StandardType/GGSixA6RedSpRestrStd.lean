module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedClDefs
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedSpDefs
public import CFSG.ClassicalGroups.Symplectic.StandardForm
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)

private noncomputable def isometryGroupEquivBilinIsometryGroup {K : Type*} [CommSemiring K]
    {W : Type*} [AddCommMonoid W] [Module K W] (B : BilinForm K W) :
    ↥(TauCeti.BilinForm.isometryGroup B) ≃*
      ↥(CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup B) := by
  let e := LinearMap.GeneralLinearGroup.generalLinearEquiv K W
  have hcoe : ∀ (g : W ≃ₗ[K] W) (x : W), (↑(e.symm g) : W → W) x = g x := by
    intro g x
    have h := LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv (R := K) (M := W) (e.symm g)
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
  exact (MulEquiv.subgroupCongr he.symm).trans
    (e.subgroupMap (CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup B)).symm

theorem ggA6_sp_std_equiv {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [Finite F] [CharP F 2] [FiniteDimensional F V] {U : Type} [AddCommGroup U] [Module F U]
    [FiniteDimensional F U]
    (B' : BilinForm F U) (hB' : B'.IsAlt) (hnd' : B'.Nondegenerate) (r : ℕ)
    (hdim : Module.finrank F U = 2 * r) :
    Nonempty (TauCeti.BilinForm.isometryGroup B' ≃* StatedSp r F) := by
  classical
  obtain ⟨m, b, hb⟩ := LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J hB' hnd'
  have hm : m = r := by
    have h1 : Module.finrank F U = m + m := by
      simpa using Module.finrank_eq_card_basis b
    omega
  subst hm
  refine ⟨(TauCeti.BilinForm.isometryGroupCongr B' b.equivFun).trans ?_⟩
  have hform : (LinearMap.BilinForm.congr b.equivFun) B' =
      CFSG.ClassicalGroups.Symplectic.spForm m F := by
    have hsym : ∀ i, b.equivFun.symm (Pi.single i 1) = b i := by
      intro i
      rw [LinearEquiv.symm_apply_eq]
      funext j
      rw [Module.Basis.equivFun_self, Pi.single_apply]
      by_cases h : i = j
      · subst h
        simp
      · simp [h, Ne.symm h]
    refine LinearMap.BilinForm.ext_basis (Pi.basisFun F (Fin m ⊕ Fin m)) fun i j => ?_
    rw [LinearMap.BilinForm.congr_apply, Pi.basisFun_apply, Pi.basisFun_apply, hsym, hsym]
    have h1 := congrFun (congrFun hb i) j
    rw [LinearMap.BilinForm.toMatrix_apply] at h1
    rw [h1, CFSG.ClassicalGroups.Symplectic.spForm]
    rw [Matrix.toBilin'_single]
    rcases i with a | a <;> rcases j with c | c <;>
      simp [Matrix.J, CFSG.ClassicalGroups.Symplectic.spJ, Matrix.fromBlocks, Pi.single_apply,
        CharTwo.neg_eq, Matrix.one_apply, eq_comm]
  rw [hform]
  exact (isometryGroupEquivBilinIsometryGroup
      (CFSG.ClassicalGroups.Symplectic.spForm m F)).trans
    (CFSG.ClassicalGroups.Symplectic.spEquiv.symm)

end CFSG.StandardType.A6Red

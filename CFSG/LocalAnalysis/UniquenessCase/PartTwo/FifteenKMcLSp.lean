module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKMcLNat
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis
public import CFSG.ClassicalGroups.Symplectic.Model
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open LinearMap (BilinForm)

open CFSG.Quasithin CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.CatalogueBAlternatingIsometry
  CFSG.Open

open scoped Matrix

private theorem s15k_mclsp_two (A : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) (ZMod 2))
    (hA : A.det ≠ 0) :
    Aᵀ * Matrix.J (Fin 1) (ZMod 2) * A = Matrix.J (Fin 1) (ZMod 2) := by
  revert A
  decide

private theorem s15k_mclsp_statedSp_one : StatedSp 1 (ZMod 2) = ⊤ := by
  rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic]
  ext A
  rw [TauCeti.GLSymplectic.mem_iff']
  exact ⟨fun _ => Subgroup.mem_top A,
    fun _ => s15k_mclsp_two (A : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) (ZMod 2))
      (Matrix.GeneralLinearGroup.det_ne_zero A)⟩

private theorem s15k_mclsp_map_eq {W : Type} [CommGroup W] {J : Subgroup (MulAut W)}
    {R : Subgroup W} (D : McRep J R) (f : LinearMap.BilinForm (ZMod 2) D.V) {m : ℕ}
    (b : Module.Basis (Fin m ⊕ Fin m) (ZMod 2) D.V)
    (hb : BilinForm.toMatrix b f = Matrix.J (Fin m) (ZMod 2)) :
    (bilinIsometryGroup f).map (mclt_glMatrixEquiv b).toMonoidHom = StatedSp m (ZMod 2) := by
  rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic]
  ext A
  rw [Subgroup.mem_map_equiv]
  have hcoord : ∀ v : D.V, b.equivFun ((((mclt_glMatrixEquiv b).symm A :
      LinearMap.GeneralLinearGroup (ZMod 2) D.V) : D.V →ₗ[ZMod 2] D.V) v) =
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 2)).mulVec (b.equivFun v) := by
    intro v
    rw [← mclt_glMatrixEquiv_mulVec, MulEquiv.apply_symm_apply]
  have hmat : LinearMap.toMatrix b b (((mclt_glMatrixEquiv b).symm A :
      LinearMap.GeneralLinearGroup (ZMod 2) D.V) : D.V →ₗ[ZMod 2] D.V) =
      (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 2)) := by
    apply Matrix.mulVec_injective
    funext u
    obtain ⟨v, rfl⟩ := b.equivFun.surjective u
    simp only [Module.Basis.equivFun_apply]
    rw [LinearMap.toMatrix_mulVec_repr]
    simpa only [Module.Basis.equivFun_apply] using hcoord v
  rw [mem_bilinIsometryGroup, ← TauCeti.BilinForm.isIsometry_iff,
    TauCeti.BilinForm.isIsometry_iff_toMatrix b, hmat, hb, TauCeti.GLSymplectic.mem_iff']

theorem s15k_mcl_sp {W : Type} [CommGroup W] {J : Subgroup (MulAut W)} {R : Subgroup W}
    (D : McRep J R) (hev : Even (Module.finrank (ZMod 2) D.V))
    (h2 : 2 ≤ Module.finrank (ZMod 2) D.V) (f : LinearMap.BilinForm (ZMod 2) D.V)
    (hnd : f.Nondegenerate) (halt : f.IsAlt) (h : D.ρ.range = bilinIsometryGroup f) :
    (∃ n : ℕ, 2 ≤ n ∧ BinaryNaturalSL J R ⊥ n 1) ∨ (∃ n : ℕ, 4 ≤ n ∧ NatSpn J R ⊥ n 1) := by
  haveI : FiniteDimensional (ZMod 2) D.V := Module.Finite.of_finite
  obtain ⟨m, b, hd, hb⟩ := exists_symplectic_basis f halt hnd
  have hmap := s15k_mclsp_map_eq D f b hb
  by_cases hm : m = 1
  · left
    have htop_sp : StatedSp m (ZMod 2) = ⊤ := by rw [hm, s15k_mclsp_statedSp_one]
    have htop : D.ρ.range = ⊤ := by
      apply Subgroup.map_injective (f := (mclt_glMatrixEquiv b).toMonoidHom)
        (mclt_glMatrixEquiv b).injective
      rw [h, hmap, htop_sp]
      simp
    exact s15k_mcl_top D h2 htop
  · right
    have hm2 : 2 ≤ m := by omega
    refine ⟨2 * m, by omega, ?_⟩
    refine ⟨even_two_mul m, ZMod 2, inferInstance, inferInstance, by simp, ?_⟩
    rw [Nat.mul_div_right m (by norm_num : 0 < 2)]
    exact s15k_mcl_realizes_nat D b (StatedSp m (ZMod 2)) (by rw [h, hmap])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

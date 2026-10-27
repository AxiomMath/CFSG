
module


public import CFSG.Monster.B.TwoA.Sp8.SubgeomIso
public import CFSG.Monster.B.TwoA.Sp8.SubgeomCard

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open Module Submodule Matrix CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open LinearMap (BilinForm)

attribute [local instance] parAction subgeomAction

attribute [local instance] parAction subgeomAction

theorem J_eq_fromBlocks (r : ℕ) : Matrix.J (Fin r) (ZMod 2) = fromBlocks 0 1 (-1) 0 := by
  ext (i | i) (j | j) <;> simp [Matrix.J, Matrix.one_apply]

theorem exists_std_model {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {r : ℕ} {B : BilinForm (ZMod 2) V} (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (hV : finrank (ZMod 2) V = 2 * r) :
    ∃ (φ : B.IsometryEquiv (pairedSympForm (ZMod 2) r))
      (σ : TauCeti.BilinForm.isometryGroup B ≃* CFSG.Assembly.LowTwoRank.StatedSp r (ZMod 2)),
      ∀ (g : TauCeti.BilinForm.isometryGroup B) (v : V),
        ((σ g : GL (Fin r ⊕ Fin r) (ZMod 2)) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) (ZMod 2)) *ᵥ
          φ v = φ ((g : V ≃ₗ[ZMod 2] V) v) := by
  obtain ⟨m, b, hm, hb⟩ := exists_symplectic_basis B hB hnd
  have hmr : m = r := by omega
  subst hmr
  have hb' : BilinForm.toMatrix b B =
      BilinForm.toMatrix (Pi.basisFun (ZMod 2) (Fin m ⊕ Fin m)) (pairedSympForm (ZMod 2) m) :=
    hb.trans ((J_eq_fromBlocks m).trans toMatrix_pairedSympForm.symm)
  set φ := b.isometryEquivOfToMatrixEq (Pi.basisFun (ZMod 2) (Fin m ⊕ Fin m)) hb'
  have hφ : ∀ v, φ v = b.equivFun v := by
    intro v
    have : (φ.toLinearEquiv : V →ₗ[ZMod 2] (Fin m ⊕ Fin m → ZMod 2)) =
        b.equivFun.toLinearMap := by
      refine b.ext fun i => ?_
      show φ (b i) = b.equivFun (b i)
      rw [b.isometryEquivOfToMatrixEq_apply_basis, Pi.basisFun_apply]
      funext j
      simp [Basis.equivFun_self, Pi.single_apply, eq_comm]
    exact LinearMap.congr_fun this v
  refine ⟨φ, (isometryMatrixEquiv b B hb).trans
    (MulEquiv.subgroupCongr CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic.symm),
    fun g v => ?_⟩
  rw [hφ, hφ]
  exact basisMatrixEquiv_mulVec b g.val v

abbrev StdIsoSpaces : Type :=
  {W : Submodule (ZMod 2) (Fin 4 ⊕ Fin 4 → ZMod 2) //
    IsTotallyIsotropic (pairedSympForm (ZMod 2) 4) W ∧
      (1 ≤ finrank (ZMod 2) W ∧ finrank (ZMod 2) W ≤ 4)}

theorem exists_subgeom_std_equiv :
    ∃ (Φ : subgeom ≃ StdIsoSpaces) (σ : Xgrp →* CFSG.Assembly.LowTwoRank.StatedSp 4 (ZMod 2)),
      Function.Surjective σ ∧ σ.ker = Lgrp.subgroupOf Xgrp ∧
      (∀ x : subgeom, parType x.1 = finrank (ZMod 2) (Φ x).1) ∧
      (∀ x y : subgeom, x.1.1.2 ≤ y.1.1.2 ↔ (Φ x).1 ≤ (Φ y).1) ∧
      ∀ (x : Xgrp) (c : subgeom), (Φ (x • c)).1 = (Φ c).1.map
        (Matrix.mulVecLin ((σ x : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) :
          Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2))) := by
  obtain ⟨φ, σ₀, hσ₀⟩ := exists_std_model b0_isAlt b0_nondegenerate finrank_V8
  set e := isoSubEquivOf φ (fun d => 1 ≤ d ∧ d ≤ 4)
  refine ⟨subgeomEquiv.trans e, σ₀.toMonoidHom.comp rhoXSp, σ₀.surjective.comp rhoXSp_surjective,
    ?_, fun x => ?_, fun x y => ?_, fun x c => ?_⟩
  · rw [← ker_rhoXSp]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  · rw [parType_eq_finrank]
    exact (LinearEquiv.finrank_map_eq _ _).symm
  · rw [le_iff_subgeomEquiv]
    exact (Submodule.map_le_map_iff_of_injective φ.toLinearEquiv.injective _ _).symm
  · show ((subgeomEquiv (x • c)).1).map
        (φ.toLinearEquiv : V8 →ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2)) =
      (((subgeomEquiv c).1).map
        (φ.toLinearEquiv : V8 →ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2))).map _
    rw [subgeomEquiv_smul, ← Submodule.map_comp, ← Submodule.map_comp]
    congr 1
    refine LinearMap.ext fun v => ?_
    have h := hσ₀ (rhoXSp x) v
    rw [coe_rhoXSp] at h
    exact h.symm

end CFSG.Monster.B.TwoA.Sp8

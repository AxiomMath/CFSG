module

public import CFSG.LieType.SpecialLinear.BinaryDescent.ExteriorTwist
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallL4Label
import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.Top.EndField
import CFSG.LieType.SpecialLinear.SLModel.Recognition
import CFSG.LieType.SpecialLinear.SLModel.Models
import CFSG.LieType.SpecialLinear.TypeLabel.EndPeriod
import CFSG.LieType.SpecialLinear.BinaryDescent.Descent
import CFSG.LieType.SpecialLinear.ExteriorModel.WeightRank
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor
public import CFSG.LieType.SpecialLinear.BinaryDescent.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open Matrix Module Finset
open CFSG.LieType.SpecialLinear CFSG.LieType.SpecialLinear.ExteriorModel
open CFSG.LieType.SpecialLinear.SLModel CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
open CFSG.HardMathSupport.GuralnickMalle CFSG.Quasithin.SmithCurtis
open scoped TensorProduct

theorem exists_extTwist_of_finrank_le {e : ℕ} (he : 3 ≤ e) {K : Type} [Field K] [Fintype K]
    [CharP K 2] (hK : Fintype.card K = 2 ^ e) {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (ρ : Representation (ZMod 2) (SpecialLinearGroup (Fin 4) K) W)
    (hirr : ρ.IsIrreducible) (hne : ∃ g, ρ g ≠ 1) {y : SpecialLinearGroup (Fin 4) K}
    (hy : y * y = 1) (hy1 : y ≠ 1)
    (hrk : finrank (ZMod 2) (LinearMap.range (ρ y - 1)) ≤ 2 * e + 2) :
    ∃ j r : ℕ, 1 ≤ j ∧ j < 4 ∧ ∃ β : W ≃+ (Set.powersetCard (Fin 4) j → K),
      ∀ g w, β (ρ g w) = extTwist 4 j r K g *ᵥ β w := by
  classical
  haveI : ρ.IsIrreducible := hirr
  let E := Module.End (MonoidAlgebra (ZMod 2) (SpecialLinearGroup (Fin 4) K)) ρ.asModule
  let k := AlgebraicClosure E
  letI : Algebra K k :=
    (CFSG.HardMathSupport.GuralnickMalle.nonempty_ringHom_algebraicClosure
      (K := E) (F₀ := K) (p := 2)).some.toAlgebra
  letI : CharP k 2 := charP_of_injective_algebraMap (algebraMap E k).injective 2
  obtain ⟨s, hs_pos, hE⟩ := exists_card_endField_eq_two_pow (ρ := ρ)
  obtain ⟨y₀, χ, J, ht, s₀, hs₀⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.top_exists_type (n := 3) ρ hne
  have hsimp : IsSimpleRep (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) :=
    CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.top_isSimpleRep (n := 3) ρ
  obtain ⟨ε, hε0, hεχ, hεJ, β, hβ⟩ :=
    exists_iso_slModelRep (m := 3) (f := e) (hF := hK)
      (ρ := CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) hsimp ht
  have htε : ∃ i, ε i ≠ ∅ := by
    by_contra h
    push Not at h
    exact hs₀ ((hεJ s₀).mpr fun r => by rw [h r]; simp)
  have hs_bound : e ≤ s * (univ.filter fun i => ε i ≠ ∅).card :=
    le_mul_card_active_of_isCoverType_endField (m := 3) (f := e) (W := W) (ρ := ρ)
      (by rwa [Nat.card_eq_fintype_card]) hE k ht hε0 hεχ htε
  have hrank := finrank_range_sub_one_eq_mul ρ hE k y
  have hrankβ := finrank_range_sub_one_eq_of_equiv
    (τ := CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ))
    (τ' := slModelRep (F := K) (k := k) (m := 3) ε) β hβ y
  obtain ⟨π, hπ, hπ01, hrankπ⟩ :=
    exists_perm_finrank_range_slModelRep_sub_one (F := K) (k := k) (m := 2) ε hy hy1
  have htop := card_moved_top_le (k := k) ε (n := 4) (by norm_num) π hπ hπ01
  have hm : s * movedTop (n := 4) (by norm_num) ε ≤ 4 * e + 4 := by
    have h1 : movedTop (n := 4) (by norm_num) ε ≤
        2 * finrank k (LinearMap.range (bRep ε (fun _ => permSL (k := k) π) - 1)) := by
      unfold movedTop
      convert htop
    rw [hrankπ, ← hrankβ] at h1
    have h2 : s * movedTop (n := 4) (by norm_num) ε ≤ 2 * finrank (ZMod 2)
        (LinearMap.range (ρ y - 1)) := by
      rw [hrank]
      calc s * movedTop (n := 4) (by norm_num) ε
          ≤ s * (2 * finrank k (LinearMap.range
            (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) y - 1))) :=
            Nat.mul_le_mul_left s h1
        _ = 2 * (s * finrank k (LinearMap.range
            (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) y - 1))) := by ring
    omega
  obtain ⟨r₀, j, hj1, hεr₀, hrest⟩ :=
    exists_single_of_movedTop_le he ε (fun r => by simpa using hε0 r) htε hs_bound hm
  obtain ⟨β', hβ'⟩ := exists_equiv_single (F := K) (k := k) (m := 3) ε hεr₀ hrest
  let X := ρ.asModule
  let Φ : W →+ (Set.powersetCard (Fin 4) (j : ℕ) → k) :=
    (β'.toLinearMap.toAddMonoidHom.comp β.toLinearMap.toAddMonoidHom).comp
      ((TensorProduct.mk E k X 1).toAddMonoidHom.comp ρ.asModuleEquiv.symm.toAddMonoidHom)
  have hΦ : ∀ w, Φ w = β' (β ((1 : k) ⊗ₜ[E] ρ.asModuleEquiv.symm w)) := fun w => rfl
  letI : DistribMulAction (SpecialLinearGroup (Fin 4) K) W := DistribMulAction.compHom W ρ
  have hsmul : ∀ (g : SpecialLinearGroup (Fin 4) K) (w : W), g • w = ρ g w := fun _ _ => rfl
  have hmat : ∀ g : SpecialLinearGroup (Fin 4) K,
      ((minorMatrix (j : ℕ) (g : Matrix (Fin 4) (Fin 4) K)).map
        (iterateFrobeniusEquiv K 2 r₀)).map (algebraMap K k) =
        (extTwist 4 j r₀ K g).map (algebraMap K k) := by
    intro g
    ext a b
    simp only [Matrix.map_apply, minorMatrix, Matrix.of_apply, extTwist, MonoidHom.coe_mk,
      OneHom.coe_mk, extTwistFun, minor_map]
    rfl
  have hΦeq : ∀ (g : SpecialLinearGroup (Fin 4) K) (w : W),
      Φ (g • w) = (extTwist 4 j r₀ K g).map (algebraMap K k) *ᵥ Φ w := by
    intro g w
    rw [hsmul, hΦ, hΦ, ← hmat g]
    have h1 : ρ.asModuleEquiv.symm (ρ g w) =
        CFSG.endFieldRep ρ g (ρ.asModuleEquiv.symm w) := by
      rw [CFSG.endFieldRep_apply]
      exact congrArg (fun v => ρ.asModuleEquiv.symm (ρ g v))
        (ρ.asModuleEquiv.apply_symm_apply w).symm
    have h2 : ((1 : k) ⊗ₜ[E] (CFSG.endFieldRep ρ g (ρ.asModuleEquiv.symm w))) =
        CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) g
          ((1 : k) ⊗ₜ[E] ρ.asModuleEquiv.symm w) := by
      rw [CFSG.Theory.Representation.extendScalars_apply, LinearMap.baseChange_tmul]
    rw [h1, h2, hβ, hβ']
  have hntW : Nontrivial W :=
    ((CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff ρ).mp hirr).1
  have hΦ0 : Φ ≠ 0 := by
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    intro h0
    have hw0 : Φ w = 0 := by rw [h0]; rfl
    rw [hΦ] at hw0
    have h1 : (1 : k) ⊗ₜ[E] ρ.asModuleEquiv.symm w = 0 := by
      apply β.injective
      apply β'.injective
      rw [hw0, β.map_zero, β'.map_zero]
    have h2 := (Module.FaithfullyFlat.one_tmul_eq_zero_iff E X (A := k)
      (ρ.asModuleEquiv.symm w)).mp h1
    exact hw (by simpa using congrArg ρ.asModuleEquiv h2)
  have hV : IsIrreducibleAdd
      (fun (g : SpecialLinearGroup (Fin 4) K) (v : W) => g • v) := by
    intro A hA
    have hirr' := ((CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff ρ).mp hirr).2
    rcases hirr' (AddSubgroup.toZModSubmodule 2 A) (fun g u hu => by
      rw [AddSubgroup.mem_toZModSubmodule] at hu ⊢
      exact hA g hu) with h | h
    · left
      rw [← AddSubgroup.toZModSubmodule_toAddSubgroup (n := 2) A, h]
      rfl
    · right
      rw [← AddSubgroup.toZModSubmodule_toAddSubgroup (n := 2) A, h]
      rfl
  have hj4 : (j : ℕ) < 4 := j.isLt
  obtain ⟨β₀, hβ₀⟩ := exists_addEquiv_extTwist_of_extend (n := 4) (i := j) (j := r₀) (F := K)
    (V := W) (k := k) hj1 hj4 hV Φ hΦ0 hΦeq
  exact ⟨j, r₀, hj1, hj4, β₀, fun g w => hβ₀ g w⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

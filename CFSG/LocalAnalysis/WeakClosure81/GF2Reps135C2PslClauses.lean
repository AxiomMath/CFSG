module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4Four16Label
public import CFSG.LieType.SpecialLinear.BinaryDescent.ExteriorTwist
import CFSG.LieType.SpecialLinear.TypeLabel.EndPeriod
import CFSG.LieType.SpecialLinear.SLModel.Models
import CFSG.LieType.SpecialLinear.BinaryDescent.Descent
import CFSG.LieType.SpecialLinear.ExteriorModel.WeightRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallL4Label
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.CaseAnalysis
public import CFSG.LieType.SpecialLinear.BinaryDescent.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix Module Finset
open CFSG.LieType.SpecialLinear CFSG.LieType.SpecialLinear.ExteriorModel
open CFSG.LieType.SpecialLinear.SLModel
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
open scoped TensorProduct

theorem w135c2_clauses_of_hasTwistedLabel {m f : ℕ} (hm : 1 ≤ m) {K : Type} [Field K] [Fintype K]
    [CharP K 2] (hK : Fintype.card K = 2 ^ f)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (SpecialLinearGroup (Fin (m + 1)) K) W)
    [ρ.IsIrreducible] {ε : Fin f → Finset (Fin (m + 1))} (hε : HasTwistedLabel ρ ε) {s : ℕ}
    (hE : Nat.card (Module.End (MonoidAlgebra (ZMod 2) (SpecialLinearGroup (Fin (m + 1)) K))
      ρ.asModule) = 2 ^ s)
    (hact : ∃ r, ε r ≠ ∅) :
    f ≤ s * (univ.filter fun r => ε r ≠ ∅).card ∧
      (∀ y : SpecialLinearGroup (Fin (m + 1)) K, y * y = 1 → y ≠ 1 →
        s * movedTop (by omega : 2 ≤ m + 1) ε ≤
          2 * finrank (ZMod 2) (LinearMap.range (ρ y - 1))) ∧
      (∃ (k : Type) (_ : Field k) (_ : CharP k 2),
        Nat.card W = 2 ^ (s * finrank k (BModel k ε))) ∧
      (∀ (r₀ : Fin f) (j : Fin (m + 1)), (∀ r, r ≠ r₀ → ε r = ∅) → ε r₀ = {j} →
        ∃ β : W ≃+ (Set.powersetCard (Fin (m + 1)) (j : ℕ) → K),
          ∀ g w, β (ρ g w) = extTwist (m + 1) (j : ℕ) (r₀ : ℕ) K g *ᵥ β w) := by
  classical
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨k, _, _, _, _, y, χ, J, h0, ht, hχ, _, β, hβ⟩ := hε
  have hs_bound : f ≤ s * (univ.filter fun i => ε i ≠ ∅).card :=
    le_mul_card_active_of_isCoverType_endField (m := m' + 1) (f := f) (W := W) (ρ := ρ)
      (by rwa [Nat.card_eq_fintype_card]) hE k ht h0 hχ hact
  refine ⟨hs_bound, ?_, ?_, ?_⟩
  ·
    intro y' hy hy1
    have hrank := finrank_range_sub_one_eq_mul ρ hE k y'
    have hrankβ := finrank_range_sub_one_eq_of_equiv
      (τ := CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ))
      (τ' := slModelRep (F := K) (k := k) (m := m' + 1) ε) β hβ y'
    obtain ⟨π, hπ, hπ01, hrankπ⟩ :=
      exists_perm_finrank_range_slModelRep_sub_one (F := K) (k := k) (m := m') ε hy hy1
    have htop := card_moved_top_le (k := k) (n := m' + 2) ε (by omega) π hπ hπ01
    have h1 : movedTop (by omega : 2 ≤ m' + 1 + 1) ε ≤
        2 * finrank k (LinearMap.range
          (bRep ε (fun _ => permSL (k := k) π) - 1)) := by
      unfold movedTop
      convert htop
    rw [hrankπ, ← hrankβ] at h1
    calc s * movedTop (by omega : 2 ≤ m' + 1 + 1) ε
        ≤ s * (2 * finrank k (LinearMap.range
            (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) y' - 1))) :=
          Nat.mul_le_mul_left s h1
      _ = 2 * (s * finrank k (LinearMap.range
            (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) y' - 1))) := by
          ring
      _ = 2 * finrank (ZMod 2) (LinearMap.range (ρ y' - 1)) := by rw [hrank]
  ·
    refine ⟨k, inferInstance, inferInstance, ?_⟩
    have h1 := card_eq_pow_finrank_extendScalars (ρ := ρ) k
    rw [hE, ← pow_mul, β.finrank_eq] at h1
    exact h1
  ·
    intro r₀ j hrest hεr₀
    have hj1 : 1 ≤ (j : ℕ) := by
      rcases Nat.eq_zero_or_pos (j : ℕ) with h | h
      · exfalso
        have hmem : (0 : Fin (m' + 1 + 1)) ∈ ε r₀ := by
          rw [hεr₀]
          exact Finset.mem_singleton.mpr (Fin.ext h.symm)
        exact h0 r₀ hmem
      · exact h
    obtain ⟨β', hβ'⟩ := exists_equiv_single (F := K) (k := k) (m := m' + 1) ε hεr₀ hrest
    let E := Module.End (MonoidAlgebra (ZMod 2)
      (SpecialLinearGroup (Fin (m' + 1 + 1)) K)) ρ.asModule
    let X := ρ.asModule
    let Φ : W →+ (Set.powersetCard (Fin (m' + 1 + 1)) (j : ℕ) → k) :=
      (β'.toLinearMap.toAddMonoidHom.comp β.toLinearMap.toAddMonoidHom).comp
        ((TensorProduct.mk E k X 1).toAddMonoidHom.comp ρ.asModuleEquiv.symm.toAddMonoidHom)
    have hΦ : ∀ w, Φ w = β' (β ((1 : k) ⊗ₜ[E] ρ.asModuleEquiv.symm w)) := fun w => rfl
    letI : DistribMulAction (SpecialLinearGroup (Fin (m' + 1 + 1)) K) W :=
      DistribMulAction.compHom W ρ
    have hsmul : ∀ (g : SpecialLinearGroup (Fin (m' + 1 + 1)) K) (w : W), g • w = ρ g w :=
      fun _ _ => rfl
    have hmat : ∀ g : SpecialLinearGroup (Fin (m' + 1 + 1)) K,
        ((minorMatrix (j : ℕ) (g : Matrix (Fin (m' + 1 + 1)) (Fin (m' + 1 + 1)) K)).map
          (iterateFrobeniusEquiv K 2 r₀)).map (algebraMap K k) =
          (extTwist (m' + 1 + 1) (j : ℕ) (r₀ : ℕ) K g).map (algebraMap K k) := by
      intro g
      ext a b
      simp only [Matrix.map_apply, minorMatrix, Matrix.of_apply, extTwist, MonoidHom.coe_mk,
        OneHom.coe_mk, extTwistFun, minor_map]
      rfl
    have hΦeq : ∀ (g : SpecialLinearGroup (Fin (m' + 1 + 1)) K) (w : W),
        Φ (g • w) = (extTwist (m' + 1 + 1) (j : ℕ) (r₀ : ℕ) K g).map
          (algebraMap K k) *ᵥ Φ w := by
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
    haveI hntW : Nontrivial W := Subrepresentation.irreducible_module_nontrivial ρ
    have hΦ0 : Φ ≠ 0 := by
      obtain ⟨w, hw⟩ := exists_ne (0 : W)
      intro hzero
      have hw0 : Φ w = 0 := by rw [hzero]; rfl
      rw [hΦ] at hw0
      have h1 : (1 : k) ⊗ₜ[E] ρ.asModuleEquiv.symm w = 0 := by
        apply β.injective
        apply β'.injective
        rw [hw0, β.map_zero, β'.map_zero]
      have h2 := (Module.FaithfullyFlat.one_tmul_eq_zero_iff E X (A := k)
        (ρ.asModuleEquiv.symm w)).mp h1
      exact hw (by simpa using congrArg ρ.asModuleEquiv h2)
    have hV : IsIrreducibleAdd
        (fun (g : SpecialLinearGroup (Fin (m' + 1 + 1)) K) (v : W) => g • v) := by
      intro A hA
      let S : Subrepresentation ρ :=
        ⟨AddSubgroup.toZModSubmodule 2 A, fun g u hu => by
          rw [AddSubgroup.mem_toZModSubmodule] at hu ⊢
          exact hA g hu⟩
      have hSsub : AddSubgroup.toZModSubmodule 2 A = S.toSubmodule := rfl
      rcases eq_bot_or_eq_top S with h | h
      · left
        have h' : AddSubgroup.toZModSubmodule 2 A = ⊥ := by
          rw [hSsub, h]
          rfl
        simpa using congrArg Submodule.toAddSubgroup h'
      · right
        have h' : AddSubgroup.toZModSubmodule 2 A = ⊤ := by
          rw [hSsub, h]
          rfl
        simpa using congrArg Submodule.toAddSubgroup h'
    obtain ⟨β₀, hβ₀⟩ := exists_addEquiv_extTwist_of_extend (n := m' + 1 + 1)
      (i := (j : ℕ)) (j := (r₀ : ℕ)) (F := K) (V := W) (k := k) hj1 j.isLt hV Φ hΦ0 hΦeq
    exact ⟨β₀, fun g w => hβ₀ g w⟩

end CFSG.LocalAnalysis.WeakClosure81

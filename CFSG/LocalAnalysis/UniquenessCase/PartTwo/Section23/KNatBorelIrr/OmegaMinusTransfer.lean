module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusCuts
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelTransport
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelCoordinates
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailPolar
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

open Matrix CFSG.Open CFSG.AGLEmbedding.LeviBlock CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open scoped Pointwise

section Bridge

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {A : Type}
  [AddCommGroup A] [Module K A] {r : ℕ} {qA : QuadraticForm K A}
  {Q : QuadraticForm K (ι → K)} {Q0 : (ι → K) → K}

theorem tailOmegaEquiv_symm_mulVec (ψ : (quadTail r qA).IsometryEquiv Q) (hQ : ⇑Q = Q0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (h : ↥(orthElementaryGroup (quadTail r qA))) (x : (Fin r ⊕ Fin r → K) × A) :
    ((((tailOmegaEquiv ψ hQ hE).symm h : ↥(StatedOmega Q0)) : GL ι K) : Matrix ι ι K) *ᵥ ψ x =
      ψ (h.val x) := by
  have h1 : h.val x =
      ψ.symm (toLinEquiv ι K ((tailOmegaEquiv ψ hQ hE).symm h).val (ψ x)) := by
    have h2 := tailOmegaEquiv_apply ψ hQ hE ((tailOmegaEquiv ψ hQ hE).symm h) x
    rwa [MulEquiv.apply_symm_apply] at h2
  rw [h1, ψ.apply_symm_apply, toLinEquiv_apply]

end Bridge

section Minus

variable {K : Type} [Field K] {b c : K}

private lemma pi_single_inl_ne_zero_L19 (k : ℕ) :
    (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin ((k + 3) - 1))) (1 : K) :
      Fin ((k + 3) - 1) ⊕ Fin ((k + 3) - 1) ⊕ Fin 2 → K) ≠ 0 := by
  intro h
  have h1 : (1 : K) = 0 := by
    simpa using congrFun h (Sum.inl (⟨0, by omega⟩ : Fin ((k + 3) - 1)))
  exact one_ne_zero h1

private lemma map_span_singleton_iff_L19 {V : Type} [AddCommGroup V] [Module K V]
    (e : V ≃ₗ[K] V) {v : V} (hv : v ≠ 0) :
    (Submodule.span K {v}).map e.toLinearMap = Submodule.span K {v} ↔
      ∃ c : K, e v = c • v := by
  rw [Submodule.map_span, Set.image_singleton]
  change Submodule.span K {e v} = Submodule.span K {v} ↔ ∃ c : K, e v = c • v
  have hev : e v ≠ 0 := fun h => hv (e.injective (by rw [h, map_zero]))
  constructor
  · intro h
    have hmem : e v ∈ Submodule.span K {v} := by
      rw [← h]
      exact Submodule.mem_span_singleton_self (e v)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := fun hcz => hev (by rw [hc, hcz, zero_smul])
    rw [hc]
    exact Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc0) v

private lemma lineStab_statedQuadMinus_eq_span_L19 (k : ℕ)
    (w : Fin ((k + 3) - 1) ⊕ Fin ((k + 3) - 1) ⊕ Fin 2 → K) :
    KTabD.lineStab (StatedOmega (StatedQuadMinus (k + 3) K b c)) w =
      statedDerivedSubspaceStabilizer (StatedQuadMinus (k + 3) K b c)
        (Submodule.span K {w}) := by
  ext γ
  by_cases hw : w = 0
  · subst hw
    rw [KTabD.mem_lineStab, mem_statedDerivedSubspaceStabilizer,
      Submodule.span_zero_singleton, Submodule.map_bot]
    simp
  · rw [KTabD.mem_lineStab, mem_statedDerivedSubspaceStabilizer,
      map_span_singleton_iff_L19 (toLinEquiv _ K γ.val) hw]
    simp only [toLinEquiv_apply]

theorem minusTailIsometry_hypVec_inl (k : ℕ) (i : Fin (k + 2)) :
    (minusTailIsometry (k + 3) K b c) (hypVec K (Fin 2 → K) (Sum.inl i)) =
      (Pi.single (Sum.inl i) 1 : Fin (k + 2) ⊕ Fin (k + 2) ⊕ Fin 2 → K) := by
  change tailModelEquiv (k + 2) K (Fin 2) (hypVec K (Fin 2 → K) (Sum.inl i)) =
    (Pi.single (Sum.inl i) 1 : Fin (k + 2) ⊕ Fin (k + 2) ⊕ Fin 2 → K)
  exact tailModelEquiv_hypVec_inl i

private lemma span_symm_eq_tailFlag_L19 (k : ℕ) :
    (Submodule.span K {(Pi.single (Sum.inl (⟨0, by omega⟩ : Fin ((k + 3) - 1))) (1 : K) :
        Fin ((k + 3) - 1) ⊕ Fin ((k + 3) - 1) ⊕ Fin 2 → K)}).map
      (minusTailIsometry (k + 3) K b c).symm.toLinearMap =
      tailFlag K (Fin 2 → K) (k + 2) 1 := by
  have hsymm : (minusTailIsometry (k + 3) K b c).symm
        (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin ((k + 3) - 1))) (1 : K) :
          Fin ((k + 3) - 1) ⊕ Fin ((k + 3) - 1) ⊕ Fin 2 → K) =
        hypVec K (Fin 2 → K) (Sum.inl (0 : Fin (k + 2))) := by
    rw [QuadraticMap.IsometryEquiv.symm_apply_eq]
    exact (minusTailIsometry_hypVec_inl (k := k) 0).symm
  rw [Submodule.map_span, Set.image_singleton]
  let y : (Fin ((k + 3) - 1) ⊕ Fin ((k + 3) - 1) → K) × (Fin 2 → K) :=
    (minusTailIsometry (k + 3) K b c).symm
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin ((k + 3) - 1))) (1 : K) :
        Fin ((k + 3) - 1) ⊕ Fin ((k + 3) - 1) ⊕ Fin 2 → K)
  change Submodule.span K {y} = tailFlag K (Fin 2 → K) (k + 2) 1
  rw [show y = hypVec K (Fin 2 → K) (Sum.inl (0 : Fin (k + 2))) from hsymm, tailFlag]
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro hv
    exact ⟨0, by simp, hv.symm⟩
  · rintro ⟨j, hj, rfl⟩
    have hjval : (j : ℕ) = 0 := Nat.lt_one_iff.mp hj
    have hj0 : j = 0 := Fin.ext (by simpa using hjval)
    subst hj0
    rfl

private lemma stabilizer_tailFlag_one_eq_orthParab_L19 {A : Type}
    [AddCommGroup A] [Module K A] {r : ℕ} (qA : QuadraticForm K A) :
    MulAction.stabilizer (orthElementaryGroup (quadTail r qA)) (tailFlag K A r 1) =
      orthParab r qA ![0, 1] := by
  ext x
  rw [mem_stabilizer_iff_map (Q := quadTail r qA), mem_orthParab, Fin.forall_fin_two]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simp only [Matrix.cons_val_zero, tailFlag_zero, Submodule.map_bot]
    · simpa using h
  · rintro ⟨-, h1⟩
    simpa using h1

variable [Finite K] [CharP K 2]

@[expose] noncomputable def minusPhi (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : ℕ) :
    ↥(StatedOmega (StatedQuadMinus (k + 3) K b c)) ≃*
      ↥(orthElementaryGroup (quadTail (k + 2) (minusTailForm K b c))) :=
  tailOmegaEquiv (minusTailIsometry (k + 3) K b c) (coe_quadMinus (k + 3) K b c)
    (commutator_orthogonalGroup_quadMinus_of_two_le (n := k + 3) (by omega) hirr)

theorem map_orthParab_minusPhi_symm (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : ℕ) :
    (orthParab (k + 2) (minusTailForm K b c) ![0, 1]).map (minusPhi hirr k).symm.toMonoidHom =
      KTabD.lineStab (StatedOmega (StatedQuadMinus (k + 3) K b c))
        (Pi.single (Sum.inl ⟨0, by omega⟩) 1) := by
  have hQ : ⇑(quadMinus (k + 3) K b c) = StatedQuadMinus (k + 3) K b c :=
    coe_quadMinus (k + 3) K b c
  have hE : ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus (k + 3) K b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus (k + 3) K b c)⁆ =
      elementaryGroup (quadMinus (k + 3) K b c) :=
    commutator_orthogonalGroup_quadMinus_of_two_le (n := k + 3) (by omega) hirr
  have hψ : (KTabD.lineStab (StatedOmega (StatedQuadMinus (k + 3) K b c))
      (Pi.single (Sum.inl ⟨0, by omega⟩) 1)).map
      (tailOmegaEquiv (minusTailIsometry (k + 3) K b c) hQ hE).toMonoidHom =
      orthParab (k + 2) (minusTailForm K b c) ![0, 1] := by
    rw [lineStab_statedQuadMinus_eq_span_L19 (k := k),
      tailOmegaEquiv_subspaceStabilizer (minusTailIsometry (k + 3) K b c) hQ hE,
      span_symm_eq_tailFlag_L19 (k := k)]
    exact stabilizer_tailFlag_one_eq_orthParab_L19 (minusTailForm K b c)
  have hφ : minusPhi hirr k = tailOmegaEquiv (minusTailIsometry (k + 3) K b c) hQ hE := rfl
  rw [hφ]
  exact (Subgroup.map_symm_eq_iff_map_eq
    (K := KTabD.lineStab (StatedOmega (StatedQuadMinus (k + 3) K b c))
      (Pi.single (Sum.inl ⟨0, by omega⟩) 1))
    (H := orthParab (k + 2) (minusTailForm K b c) ![0, 1])
    (e := tailOmegaEquiv (minusTailIsometry (k + 3) K b c) hQ hE)).mpr hψ

theorem minusPhi_symm_mulVec_e0 (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : ℕ)
    (h : ↥(orthElementaryGroup (quadTail (k + 2) (minusTailForm K b c)))) (a : K)
    (hh : h.val (hypVec K (Fin 2 → K) (Sum.inl (0 : Fin (k + 2)))) =
      a • hypVec K (Fin 2 → K) (Sum.inl (0 : Fin (k + 2)))) :
    ((minusPhi hirr k).symm h).val.val *ᵥ (Pi.single (Sum.inl ⟨0, by omega⟩) 1) =
      a • (Pi.single (Sum.inl ⟨0, by omega⟩) 1) := by
  have hQ : ⇑(quadMinus (k + 3) K b c) = StatedQuadMinus (k + 3) K b c :=
    coe_quadMinus (k + 3) K b c
  have hE : ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus (k + 3) K b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus (k + 3) K b c)⁆ =
      elementaryGroup (quadMinus (k + 3) K b c) :=
    commutator_orthogonalGroup_quadMinus_of_two_le (n := k + 3) (by omega) hirr
  set x : (Fin (k + 2) ⊕ Fin (k + 2) → K) × (Fin 2 → K) :=
    hypVec K (Fin 2 → K) (Sum.inl (0 : Fin (k + 2))) with hx
  have hxe : (minusTailIsometry (k + 3) K b c) x =
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin ((k + 3) - 1))) (1 : K) :
        Fin ((k + 3) - 1) ⊕ Fin ((k + 3) - 1) ⊕ Fin 2 → K) := by
    rw [hx]
    exact minusTailIsometry_hypVec_inl (k := k) 0
  have key := tailOmegaEquiv_symm_mulVec (minusTailIsometry (k + 3) K b c) hQ hE h x
  have hφ : minusPhi hirr k = tailOmegaEquiv (minusTailIsometry (k + 3) K b c) hQ hE := rfl
  rw [hφ, ← hxe, key]
  have hh' : h.val x = a • x := by
    rw [hx]
    exact hh
  rw [hh', map_smul]

end Minus

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

module

public import CFSG.Open.StatedDefs
import CFSG.ClassicalGroups.Orthogonal.Matrix
import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
import CFSG.LieType.Universal.Spin.Forms
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.RootFix
import CFSG.RankThree.GF2n.Stroth80.Sec310ClOmegaPlusFour
import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA

open CFSG.Open
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal
open QuadraticMap
open scoped Matrix commutatorElement

private theorem exists_ne_zero_one {K : Type*} [Field K] [Finite K] (hK : 2 < Nat.card K) :
    ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  by_contra h
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := by
    intro x _
    by_cases hx0 : x = 0
    · simp [hx0]
    · have hx1 : x = 1 := by
        by_contra hx1
        exact h ⟨x, hx0, hx1⟩
      simp [hx1]
  have hle : Fintype.card K ≤ 2 := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_univ, Finset.card_pair (zero_ne_one (α := K))] at this
  rw [Nat.card_eq_fintype_card] at hK
  omega

private theorem eichler_pow_nsmul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {u w : V} (hw : polar Q u w = 0) (n : ℕ) :
    eichler Q u w ^ n = eichler Q u (n • w) := by
  induction n with
  | zero => rw [pow_zero, zero_smul, eichler_zero_right]
  | succ n ih =>
    have hnw : polar Q u (n • w) = 0 := by
      rw [← Nat.cast_smul_eq_nsmul K, polar_smul_right, hw, smul_zero]
    rw [pow_succ, ih, eichler_mul hnw hw, succ_nsmul]

private theorem eichler_pow_eq_one {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {p : ℕ} [CharP K p] {u w : V} (hw : polar Q u w = 0) :
    eichler Q u w ^ p = 1 := by
  rw [eichler_pow_nsmul hw, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul,
    eichler_zero_right]

private theorem rootGroupGL_mem_iff {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm K (ι → K)) (u : ι → K) (A : GL ι K) :
    A ∈ rootGroupGL Q u ↔ ∃ w, polar Q u w = 0 ∧ eichler Q u w = toLinEquiv ι K A := by
  rw [rootGroupGL, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, mem_rootGroup]

private theorem isPGroup_rootGroupGL {K : Type} [Field K] (p : ℕ) [CharP K p]
    (u : Fin 2 ⊕ Fin 2 → K) :
    IsPGroup p ↥((rootGroupGL (quadPlus 2 K) u).subgroupOf
      (StatedOmega (StatedQuadPlus 2 K))) := by
  intro x
  have hxmem : (((x : ↥(StatedOmega (StatedQuadPlus 2 K))) : GL (Fin 2 ⊕ Fin 2) K))
      ∈ rootGroupGL (quadPlus 2 K) u := by
    simpa only [Subgroup.mem_subgroupOf] using x.2
  obtain ⟨w, hw, hwE⟩ :=
    (rootGroupGL_mem_iff (quadPlus 2 K) u
      (((x : ↥(StatedOmega (StatedQuadPlus 2 K))) : GL (Fin 2 ⊕ Fin 2) K))).mp hxmem
  let U := (rootGroupGL (quadPlus 2 K) u).subgroupOf (StatedOmega (StatedQuadPlus 2 K))
  let φ : ↥U →* ((Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) :=
    (toLinEquiv (Fin 2 ⊕ Fin 2) K).toMonoidHom.comp
      ((Subgroup.subtype (StatedOmega (StatedQuadPlus 2 K))).comp (Subgroup.subtype U))
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact (toLinEquiv (Fin 2 ⊕ Fin 2) K).injective hab
  have hφx : φ x = eichler (quadPlus 2 K) u w := by
    change toLinEquiv (Fin 2 ⊕ Fin 2) K
      (((x : ↥(StatedOmega (StatedQuadPlus 2 K))) : GL (Fin 2 ⊕ Fin 2) K))
      = eichler (quadPlus 2 K) u w
    exact hwE.symm
  refine ⟨1, ?_⟩
  rw [pow_one]
  apply hφinj
  rw [map_pow, hφx, eichler_pow_eq_one hw, map_one]

private theorem fixed_vectors_rootGroupGL {K : Type} [Field K] (u : Fin 2 ⊕ Fin 2 → K)
    (hQ : (polarBilin (quadPlus 2 K)).Nondegenerate) (hu : quadPlus 2 K u = 0) (hu0 : u ≠ 0)
    (hcomm : elementaryGroup (quadPlus 2 K) ≤
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 K),
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 K)⁆) :
    ∀ v : Fin 2 ⊕ Fin 2 → K,
      (∀ w ∈ (rootGroupGL (quadPlus 2 K) u).subgroupOf (StatedOmega (StatedQuadPlus 2 K)),
        ((w : GL (Fin 2 ⊕ Fin 2) K) : Matrix _ _ K) *ᵥ v = v) →
      v ∈ Submodule.span K {u} := by
  have hd : 3 ≤ Module.finrank K (Fin 2 ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    norm_num
  intro v hv
  refine mem_span_of_forall_eichler_apply_eq hQ hd hu hu0 ?_
  intro w hw
  have hEcom : eichler (quadPlus 2 K) u w ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 K),
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 K)⁆ :=
    hcomm (eichler_mem_elementaryGroup (quadPlus 2 K) u w)
  let A : GL (Fin 2 ⊕ Fin 2) K :=
    (toLinEquiv (Fin 2 ⊕ Fin 2) K).symm (eichler (quadPlus 2 K) u w)
  have hAe : toLinEquiv (Fin 2 ⊕ Fin 2) K A = eichler (quadPlus 2 K) u w :=
    MulEquiv.apply_symm_apply (toLinEquiv (Fin 2 ⊕ Fin 2) K) (eichler (quadPlus 2 K) u w)
  have hA : A ∈ StatedOmega (StatedQuadPlus 2 K) := by
    rw [statedOmega_eq_comap (coe_quadPlus 2 K), Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
      hAe]
    exact hEcom
  let xw : ↥(StatedOmega (StatedQuadPlus 2 K)) := ⟨A, hA⟩
  have hxwU : xw ∈ (rootGroupGL (quadPlus 2 K) u).subgroupOf
      (StatedOmega (StatedQuadPlus 2 K)) := by
    simp only [Subgroup.mem_subgroupOf]
    exact (rootGroupGL_mem_iff (quadPlus 2 K) u A).mpr ⟨w, hw, hAe.symm⟩
  have hv' : ((xw : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v
      = v := hv xw hxwU
  have hxwE : toLinEquiv (Fin 2 ⊕ Fin 2) K (xw : GL (Fin 2 ⊕ Fin 2) K)
      = eichler (quadPlus 2 K) u w := hAe
  simpa [← toLinEquiv_apply, hxwE] using hv'

theorem exists_fixedLine_statedOmega_plus_two_single {K : Type} [Field K] [Finite K] (p : ℕ)
    [Fact p.Prime] [CharP K p] (hK : 2 < Nat.card K) :
    ∃ U : Subgroup ↥(StatedOmega (StatedQuadPlus 2 K)), IsPGroup p ↥U ∧
      ∀ v : Fin 2 ⊕ Fin 2 → K,
        (∀ u ∈ U, ((u : GL (Fin 2 ⊕ Fin 2) K) : Matrix _ _ K) *ᵥ v = v) →
          v ∈ Submodule.span K {(Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K)} := by
  classical
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_one (K := K) hK
  let u : Fin 2 ⊕ Fin 2 → K := Pi.single (Sum.inl 0) 1
  have hu : quadPlus 2 K u = 0 := by
    simp [u, quadPlus_apply, Fin.sum_univ_two]
  have hu0 : u ≠ 0 := by
    intro h
    have := congrFun h (Sum.inl 0)
    simp [u] at this
  have hQ : (polarBilin (quadPlus 2 K)).Nondegenerate := nondegenerate_polarBilin_quadPlus 2 K
  have hcomm : elementaryGroup (quadPlus 2 K) ≤
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 K),
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 K)⁆ :=
    CFSG.RankThree.GF2n.Stroth80.Classify.elementaryGroup_le_commutator hQ hc0 hc1
  refine ⟨(rootGroupGL (quadPlus 2 K) u).subgroupOf
    (StatedOmega (StatedQuadPlus 2 K)), ?_, ?_⟩
  · exact isPGroup_rootGroupGL p u
  · exact fixed_vectors_rootGroupGL u hQ hu hu0 hcomm

theorem exists_fixedLine_statedOmega_plus_two {K : Type} [Field K] [Finite K] (p : ℕ)
    [Fact p.Prime] [CharP K p] (hK : 2 < Nat.card K) :
    ∃ (U : Subgroup ↥(StatedOmega (StatedQuadPlus 2 K))) (e : Fin 2 ⊕ Fin 2 → K),
      IsPGroup p ↥U ∧
      ∀ v : Fin 2 ⊕ Fin 2 → K,
        (∀ u ∈ U, ((u : GL (Fin 2 ⊕ Fin 2) K) : Matrix _ _ K) *ᵥ v = v) →
          v ∈ Submodule.span K {e} :=
  let ⟨U, hU, hfix⟩ := exists_fixedLine_statedOmega_plus_two_single p hK
  ⟨U, _, hU, hfix⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA

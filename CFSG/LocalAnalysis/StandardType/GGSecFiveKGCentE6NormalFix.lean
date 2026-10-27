module

public import CFSG.RankThree.PartOne.KE8F.FamBruhat
public import CFSG.LieType.Chevalley.ExactNormalFormE
import CFSG.LieType.Chevalley.E6EvenRootTorusCentralizer
import CFSG.LocalAnalysis.SeitzReduction.E6PilotAutDTwo
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat
import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.CharacterTheory.Semidihedral.OddFieldLift
import CFSG.LieType.Chevalley.C2E6StandardFixedData
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
import CFSG.LieType.Universal.Spin.Roots
import CFSG.LieType.Universal.Unitary
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.RankThree.PartOne.KE.A2Family
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType

namespace KGCentE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE8F
  CFSG.SeitzReduction.E6Pilot

private theorem isRoot_permLattice_exactPerm {ε : Fin (exactE .E6)} {γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot .E6 γ) : IsRoot .E6 (permLattice (exactPerm .E6 ε) γ) := by
  have hperm : permLattice (exactPerm .E6 (ε : ℕ)) γ =
      permLattice (TwistTag.E6.perm ^ (ε : ℕ)) γ := rfl
  rcases (show (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 by
    have := ε.isLt
    change (ε : ℕ) < 2 at this
    omega) with h | h
  · rw [h]
    exact hγ
  · rw [hperm, h, pow_one]
    exact IsRoot.permLattice (TwistTag.cartan_perm TwistTag.E6) hγ

private theorem exactNormalAutGL_pinnedX_E6
    {K : Type} [Field K] [CharP K 2] {a : Fin Tag.E6.rank → Kˣ} {σ : K ≃+* K}
    {ε : Fin (exactE .E6)} {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ) (c : K) :
    exactNormalAutGL .E6 K a σ ε (pinnedX .E6 K γ c) =
      pinnedX .E6 K (permLattice (exactPerm .E6 ε) γ)
        (((rootChar a (permLattice (exactPerm .E6 ε) γ) : K)) * σ c) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hσ : Units.map (entrywiseHom σ.toRingHom) (pinnedX .E6 K γ c) =
      pinnedX .E6 K γ (σ c) :=
    CFSG.RankThree.PartOne.KE.units_map_entrywiseHom_pinnedX σ.toRingHom γ c
  have hperm : permLattice (exactPerm .E6 (ε : ℕ)) γ =
      permLattice (TwistTag.E6.perm ^ (ε : ℕ)) γ := rfl
  rw [exactNormalAutGL_apply, hσ]
  rcases (show (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 by
    have := ε.isLt
    change (ε : ℕ) < 2 at this
    omega) with h | h
  · have h1 : permLattice (exactPerm .E6 0) γ = γ := rfl
    rw [h, exactQ_zero, h1]
    simp only [mul_one, inv_one]
    exact rootDiagUnit_conj_pinnedX a hγ (σ c)
  · rw [show exactQ .E6 K (ε : ℕ) = exactQ .E6 K 1 by rw [h], hperm, h, pow_one]
    rw [show rootDiagUnit .E6 a * exactQ .E6 K 1 * pinnedX .E6 K γ (σ c) * (exactQ .E6 K 1)⁻¹ *
        (rootDiagUnit .E6 a)⁻¹ = rootDiagUnit .E6 a *
        (exactQ .E6 K 1 * pinnedX .E6 K γ (σ c) * (exactQ .E6 K 1)⁻¹) *
        (rootDiagUnit .E6 a)⁻¹ from by group,
      exactQ_one_conj_pinnedX h2 hγ (σ c)]
    exact rootDiagUnit_conj_pinnedX a (IsRoot.permLattice (TwistTag.cartan_perm TwistTag.E6) hγ)
      (σ c)

private theorem normalForm_pinnedX_E6
    {K : Type} [Field K] [CharP K 2] {α : MulAut (adjointGroup .E6 K)}
    {l : Fin Tag.E6.rank → Kˣ} {w : WeylGroup Tag.E6} {a : Fin Tag.E6.rank → Kˣ}
    {σ : K ≃+* K} {ε : Fin (exactE .E6)}
    (hα : ∀ x : adjointGroup .E6 K, ((α x : adjointGroup .E6 K) : ModGL .E6 K) =
      rootDiagUnit .E6 l * canonicalRep (coxeterSystem .E6) K w *
        exactNormalAutGL .E6 K a σ ε (x : ModGL .E6 K) *
          (rootDiagUnit .E6 l * canonicalRep (coxeterSystem .E6) K w)⁻¹)
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β) (c : K) :
    ((α ⟨pinnedX .E6 K β c, pinnedX_mem_adjointGroup β c⟩ : adjointGroup .E6 K) :
        ModGL .E6 K) =
      pinnedX .E6 K (w • permLattice (exactPerm .E6 ε) β)
        ((rootChar l (w • permLattice (exactPerm .E6 ε) β) : K) *
          ((rootChar a (permLattice (exactPerm .E6 ε) β) : K) * σ c)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hρ := isRoot_permLattice_exactPerm (ε := ε) hβ
  rw [hα, exactNormalAutGL_pinnedX_E6 hβ c]
  set n := canonicalRep (coxeterSystem .E6) K w
  set e := (rootChar a (permLattice (exactPerm .E6 ε) β) : K) * σ c
  calc rootDiagUnit .E6 l * n * pinnedX .E6 K (permLattice (exactPerm .E6 ε) β) e *
        (rootDiagUnit .E6 l * n)⁻¹ = rootDiagUnit .E6 l *
          (n * pinnedX .E6 K (permLattice (exactPerm .E6 ε) β) e * n⁻¹) *
            (rootDiagUnit .E6 l)⁻¹ := by group
    _ = _ := by
      rw [RootCentExc.canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hρ e,
        rootDiagUnit_conj_pinnedX l (CFSG.LieType.Chevalley.IsRoot.smul hρ w) e]

theorem normalForm_fix_famKernel_E6
    {K : Type} [Field K] [CharP K 2] {F : Set (Fin Tag.E6.rank → Kˣ)}
    (hne : (famKernel F).Nonempty) {α : MulAut (adjointGroup .E6 K)} {h : ModGL .E6 K}
    (hh : h ∈ torusGroup .E6 K) {w : WeylGroup Tag.E6} {a : Fin Tag.E6.rank → Kˣ} {σ : K ≃+* K}
    {ε : Fin (exactE .E6)}
    (hα : ∀ x : adjointGroup .E6 K, ((α x : adjointGroup .E6 K) : ModGL .E6 K) =
      h * canonicalRep (coxeterSystem .E6) K w * exactNormalAutGL .E6 K a σ ε (x : ModGL .E6 K) *
        (h * canonicalRep (coxeterSystem .E6) K w)⁻¹)
    (hfix : ∀ β ∈ famKernel F, ∀ x : adjointGroup .E6 K,
      (x : ModGL .E6 K) ∈ rootSubgroup .E6 K β → α x = x) :
    σ = 1 ∧ ∀ β ∈ famKernel F, w • permLattice (exactPerm .E6 ε) β = β := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  have hX : ∀ β ∈ famKernel F, ∀ c : K,
      pinnedX .E6 K (w • permLattice (exactPerm .E6 ε) β)
        ((rootChar l (w • permLattice (exactPerm .E6 ε) β) : K) *
          ((rootChar a (permLattice (exactPerm .E6 ε) β) : K) * σ c)) = pinnedX .E6 K β c := by
    intro β hβ c
    rw [← normalForm_pinnedX_E6 hα hβ.1 c]
    exact congrArg Subtype.val (hfix β hβ _ (Subgroup.subset_closure ⟨c, rfl⟩))
  have hpos : ∀ β ∈ famKernel F, 0 < height β → w • permLattice (exactPerm .E6 ε) β = β :=
    fun β hβ hp => E6EvenRootTorus.eq_of_pinnedX_eq_pinnedX_of_pos
      (CFSG.LieType.Chevalley.IsRoot.smul (isRoot_permLattice_exactPerm hβ.1) w) hβ.1 hp
      one_ne_zero (hX β hβ 1)
  have hθ : ∀ β ∈ famKernel F, w • permLattice (exactPerm .E6 ε) β = β := by
    intro β hβ
    rcases IsRoot.height_pos_or_neg hβ.1 with hp | hn
    · exact hpos β hβ hp
    · have hβ' : -β ∈ famKernel F := by
        refine ⟨IsRoot.neg hβ.1, fun b hb => ?_⟩
        have h0 := rootChar_add b β (-β)
        rw [add_neg_cancel, rootChar_zero, hβ.2 b hb, one_mul] at h0
        exact h0.symm
      have h1 := hpos (-β) hβ' (by rw [height_neg]; omega)
      rw [show permLattice (exactPerm .E6 ε) (-β) = -permLattice (exactPerm .E6 ε) β from rfl,
        smul_neg, neg_inj] at h1
      exact h1
  refine ⟨?_, hθ⟩
  obtain ⟨β₀, hβ₀⟩ := hne
  have hc : ∀ c : K, (rootChar l β₀ : K) *
      ((rootChar a (permLattice (exactPerm .E6 ε) β₀) : K) * σ c) = c := by
    intro c
    have := hX β₀ hβ₀ c
    rw [hθ β₀ hβ₀] at this
    exact pinnedX_injective .E6 K β₀ this
  have hμ : (rootChar l β₀ : K) * (rootChar a (permLattice (exactPerm .E6 ε) β₀) : K) = 1 := by
    have := hc 1
    rwa [map_one, mul_one] at this
  refine RingEquiv.ext fun c => ?_
  have := hc c
  rw [← mul_assoc, hμ, one_mul] at this
  exact this

end KGCentE6

end CFSG.StandardType

end

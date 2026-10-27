module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.FrameAct
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidTools
public import CFSG.RankThree.Chevalley.SteinbergBIE7ThreeA1
public import CFSG.LieType.HighestRoot.CentChevalley
public import CFSG.RankThree.PartOne.CTP.SpinMinusEven
public import CFSG.Mathlib.GroupTheory.Automorphism.ConjCommute
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A1TwistedE6
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.SigmaPerX
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KGD.D4Frame
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public noncomputable section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Chevalley
  CFSG.RankThree.Classical
open scoped MatrixGroups


theorem torusGroup_le_rootPair_sup_centralizer {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    torusGroup τ L ≤
      (rootSubgroup τ L γ ⊔ rootSubgroup τ L (-γ)) ⊔
        Subgroup.centralizer
          (((rootSubgroup τ L γ ⊔ rootSubgroup τ L (-γ)) :
            Subgroup (ModGL τ L)) : Set (ModGL τ L)) := by
  let H : Subgroup (ModGL τ L) := rootSubgroup τ L γ ⊔ rootSubgroup τ L (-γ)
  intro t ht
  obtain ⟨χ, -, hact⟩ := torusGroup_conj_rootSL2 ht hγ
  obtain ⟨P', hP'⟩ := exists_sl2_conjSL (diagUnitOne χ)
  let a : ModGL τ L := rootSL2 τ L γ P'
  have ha : a ∈ H := by
    change a ∈ rootSubgroup τ L γ ⊔ rootSubgroup τ L (-γ)
    rw [← range_rootSL2_of_isRoot hγ]
    exact ⟨P', rfl⟩
  have hc : a⁻¹ * t ∈ Subgroup.centralizer (H : Set (ModGL τ L)) := by
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro x hx
    have hx' : x ∈ (rootSL2 τ L γ).range := by
      rw [range_rootSL2_of_isRoot hγ]
      exact hx
    obtain ⟨A, rfl⟩ := hx'
    have heq : t * rootSL2 τ L γ A * t⁻¹ = a * rootSL2 τ L γ A * a⁻¹ := by
      rw [hact A, hP' A, map_mul, map_mul, map_inv]
    have hcomm : (a⁻¹ * t) * rootSL2 τ L γ A = rootSL2 τ L γ A * (a⁻¹ * t) := by
      calc (a⁻¹ * t) * rootSL2 τ L γ A
          = a⁻¹ * (t * rootSL2 τ L γ A * t⁻¹) * t := by group
        _ = rootSL2 τ L γ A * (a⁻¹ * t) := by rw [heq]; group
    exact hcomm.symm
  have ht' : t = a * (a⁻¹ * t) := by group
  rw [ht']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hc)

theorem torus_sup_kernelRootSpan_le_component_sup_centralizer_of_pair {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hΨ : componentRoots χ i = {γ, -γ}) :
    torusGroup τ L ⊔ rootSpan τ L (kernelRoots χ) ≤
      componentRootSpan L χ i ⊔ Subgroup.centralizer (componentRootSpan L χ i : Set (ModGL τ L)) := by
  have hpair : componentRootSpan L χ i = rootSubgroup τ L γ ⊔ rootSubgroup τ L (-γ) := by
    exact (congrArg (rootSpan τ L) hΨ).trans (CFSG.LieType.HighestRoot.rootSpan_pair_eq γ)
  refine sup_le ?_ ?_
  · simpa only [hpair] using (torusGroup_le_rootPair_sup_centralizer (τ := τ) (L := L) hγ)
  · rw [← iSup_componentRootSpan (χ := χ) L]
    refine iSup_le fun j => ?_
    by_cases hji : j = i
    · subst j
      exact le_sup_left
    · intro g hg
      apply Subgroup.mem_sup_right
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro x hx
      exact (commute_of_mem_componentRootSpan hji hg hx).eq.symm

theorem exists_rootSL2_inner_hom {τ : Tag} {L : Type} [Field L] [CharP L 2]
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) {B : Type*} [Group B]
    (ν : B →* ModGL τ L)
    (hν : ∀ b : B, ν b ∈ rootSpan τ L {γ, -γ} ⊔
      Subgroup.centralizer (rootSpan τ L {γ, -γ} : Set (ModGL τ L))) :
    ∃ a : B →* SL(2, L), ∀ (b : B) (A : SL(2, L)),
      ν b * rootSL2 τ L γ A * (ν b)⁻¹ = rootSL2 τ L γ (a b * A * (a b)⁻¹) := by
  let H := (rootSL2 τ L γ).range
  let e : SL(2, L) ≃* H := MonoidHom.ofInjective (rootSL2_injective_of_field γ)
  have hspan : rootSpan τ L {γ, -γ} = H :=
    (CFSG.LieType.HighestRoot.rootSpan_pair_eq γ).trans
      (range_rootSL2_of_isRoot hγ).symm
  have hνH : ∀ b : B, ν b ∈ H ⊔ Subgroup.centralizer (H : Set (ModGL τ L)) := by
    simpa only [hspan] using hν
  have hSL : Subgroup.center SL(2, L) = ⊥ :=
    CFSG.RankThree.PartOne.CTP.center_sl2_eq_bot_of_two_eq_zero CharTwo.two_eq_zero
  have hZH : Subgroup.center H = ⊥ := by
    rw [← Subgroup.map_center_eq e, hSL, Subgroup.map_bot]
  have hN : ∀ b : B, ν b ∈ Subgroup.normalizer (H : Set (ModGL τ L)) := fun b =>
    (sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _)) (hνH b)
  let β : B →* MulAut H := H.normalizerMonoidHom.comp
    (ν.codRestrict (Subgroup.normalizer (H : Set (ModGL τ L))) hN)
  have hβ : ∀ b : B, β b ∈ (MulAut.conj : H →* MulAut H).range := by
    intro b
    obtain ⟨h, hh, c, hc, heq⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun u hu v hv => Subgroup.mem_centralizer_iff.mp hv u hu) (hνH b)
    refine ⟨⟨h, hh⟩, ?_⟩
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    change h * (u : ModGL τ L) * h⁻¹ = ν b * (u : ModGL τ L) * (ν b)⁻¹
    rw [← heq]
    have hcu : c * (u : ModGL τ L) = u * c :=
      (Subgroup.mem_centralizer_iff.mp hc u u.2).symm
    calc h * (u : ModGL τ L) * h⁻¹ = h * (c * u * c⁻¹) * h⁻¹ := by rw [hcu]; group
      _ = (h * c) * u * (h * c)⁻¹ := by group
  let ec : H ≃* (MulAut.conj : H →* MulAut H).range :=
    MonoidHom.ofInjective (CFSG.mulAut_conj_injective hZH)
  let μ : B →* H := ec.symm.toMonoidHom.comp
    (β.codRestrict (MulAut.conj : H →* MulAut H).range hβ)
  have hμ : ∀ b : B, MulAut.conj (μ b) = β b := fun b =>
    congrArg (fun z : (MulAut.conj : H →* MulAut H).range => (z : MulAut H))
      (ec.apply_symm_apply ⟨β b, hβ b⟩)
  let a : B →* SL(2, L) := e.symm.toMonoidHom.comp μ
  refine ⟨a, ?_⟩
  intro b A
  have hact := congrArg (fun z : MulAut H => ((z (e A) : H) : ModGL τ L)) (hμ b)
  change (μ b : ModGL τ L) * rootSL2 τ L γ A * (μ b : ModGL τ L)⁻¹ =
    ν b * rootSL2 τ L γ A * (ν b)⁻¹ at hact
  have hea : e (a b) = μ b := e.apply_symm_apply _
  have hμval : (μ b : ModGL τ L) = rootSL2 τ L γ (a b) :=
    (congrArg (fun z : H => (z : ModGL τ L)) hea).symm
  rw [← hact, hμval, map_mul, map_mul, map_inv]

end CFSG.StandardType.LieKnownR2.ExcPos

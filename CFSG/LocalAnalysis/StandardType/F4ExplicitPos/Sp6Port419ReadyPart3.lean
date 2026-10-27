module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodRankOne
public import CFSG.Assembly.LargeEvenDefs
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Defs
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Position
public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Defs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveTwRigidLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.AlgebraicGroups.ConnectedToralLang
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.Chevalley.OrdinaryRootHyperplaneGeneration
public import CFSG.LieType.Chevalley.ParabolicRadicalNormalizer
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterE6Adj
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.KGD.D4QA1
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate1
public import Certificates.Certificate2

@[expose] public section

public section
open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LocalAnalysis.ComponentInitial

public section
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
open scoped CFSG.ConvolutionPoints

public noncomputable section
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.AlgebraicGroups WithConv
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped CFSG.ConvolutionPoints

public section

namespace CFSG.StandardType.F4ExplicitPos.JointUntwist

open CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE

open scoped commutatorElement

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem exists_untwist_of_kernel_stable
    (S : LangSetup τ L p)
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ) {s : ℕ} (hs : 0 < s)
    (hker : ∀ γ ∈ kernelRoots χ, (S.ρ : (Fin τ.rank → ℤ) → _)^[s] γ ∈ kernelRoots χ)
    (hinner : twistInner (componentRoots χ i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[s])) :
    ∃ (σ : L ≃+* L) (z : ModGL τ L), (∀ c, σ c = c ^ (S.D.q ^ s)) ∧
      z ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots χ) ∧
      (∀ j : KernelComponent χ, ∀ g : ModGL τ L,
        g ∈ rootSpan τ L (componentRoots χ j) ↔
          z * g * z⁻¹ ∈ rootSpan τ L (componentRoots χ j)) ∧
      ∀ g ∈ rootSpan τ L (componentRoots χ i),
        iterHom S.D.step s (z * g * z⁻¹) = z * frobGL σ g * z⁻¹ := by
  classical
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_frob (L := L) r (e * s)
  have hσc : ∀ c, σ c = c ^ (S.D.q ^ s) := by
    intro c
    have h1 : σ c = iterateFrobenius L r (e * s) c := by
      rw [← hσ]
      rfl
    rw [h1, iterateFrobenius_def, hq, ← pow_mul]
  obtain ⟨w, hw, hwγ⟩ := hinner
  have hφpin : ∀ γ ∈ componentRoots χ i, ∃ m : L, m ≠ 0 ∧
      ∀ c : L, iterHom S.D.step s (pinnedX τ L γ c) = pinnedX τ L (w • γ) (m * σ c) := by
    intro γ hγ
    obtain ⟨μ, hμ0, hμ⟩ := iter_step_pinnedX S s (isRoot_of_mem_componentRoots hγ)
    exact ⟨μ, hμ0, fun c => by rw [iterHom_eq_iterate, hμ, hwγ γ hγ, hσc]⟩
  obtain ⟨y₁, hy₁, hpin⟩ := exists_pin i σ (iterHom S.D.step s) hw hφpin
  obtain ⟨z, hzZ, hφz⟩ :=
    exists_lang_torus_sup_kernelRoots S hs hker
      ((sup_le_sup_left (rootSpan_mono fun γ hγ => hγ.1) _) hy₁)
  refine ⟨σ, z, hσc, hzZ, mem_componentRootSpan_iff_conj_of_mem hzZ, fun g hg => ?_⟩
  rw [map_mul, map_mul, map_inv, hφz]
  calc z * y₁ * iterHom S.D.step s g * (z * y₁)⁻¹ =
      z * (y₁ * iterHom S.D.step s g * y₁⁻¹) * z⁻¹ := by group
    _ = z * frobGL σ g * z⁻¹ := by rw [hpin g hg]

end CFSG.StandardType.F4ExplicitPos.JointUntwist

public section

namespace CFSG.StandardType.F4ExplicitPos.FixedCover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LangTorus

open scoped commutatorElement

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem range_eq_derived_fixed_component
    (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (i : KernelComponent χ) (σ : L ≃+* L) (z : ModGL τ L)
    (hnorm : ∀ g : ModGL τ L,
      g ∈ componentRootSpan L χ i ↔ z * g * z⁻¹ ∈ componentRootSpan L χ i)
    (hz : ∀ g ∈ componentRootSpan L χ i,
      S.D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    (hperf : Group.IsPerfect (componentRootSpan (fixSubfield σ) χ i)) :
    let f := (MulAut.conj z).toMonoidHom.comp
      ((baseChangeGL (fixSubfield σ).subtype).comp
        (componentRootSpan (fixSubfield σ) χ i).subtype)
    Function.Injective f ∧
      f.range = ⁅componentRootSpan L χ i ⊓ S.Γ,
        componentRootSpan L χ i ⊓ S.Γ⁆ := by
  classical
  let Ck : Subgroup (ModGL τ (fixSubfield σ)) := componentRootSpan (fixSubfield σ) χ i
  let C : Subgroup (ModGL τ L) := componentRootSpan L χ i
  let ι : ModGL τ (fixSubfield σ) →* ModGL τ L := baseChangeGL (fixSubfield σ).subtype
  let f : Ck →* ModGL τ L := (MulAut.conj z).toMonoidHom.comp (ι.comp Ck.subtype)
  change Function.Injective f ∧ f.range = ⁅C ⊓ S.Γ, C ⊓ S.Γ⁆
  have hs : ∃ s : Lˣ, s ^ 2 ≠ 1 := by
    obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset L)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    refine ⟨Units.mk0 x hx.1, ?_⟩
    intro h
    have h2 : (x : L) ^ 2 = 1 := by
      have := congrArg (fun u : Lˣ => (u : L)) h
      simpa using this
    have h3 : (x - 1) * (x + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact hx.2.1 (sub_eq_zero.1 h4)
    · exact hx.2.2 (eq_neg_of_add_eq_zero_left h4)
  have hCQ : ∀ c : Ck, ι (c : ModGL τ (fixSubfield σ)) ∈ CQ σ i := by
    intro c
    rw [CQ_eq_map]
    exact ⟨c, c.2, rfl⟩
  have hfixCQ : ∀ c : Ck,
      frobGL σ (ι (c : ModGL τ (fixSubfield σ))) = ι (c : ModGL τ (fixSubfield σ)) :=
    fun c => frobGL_eq_self_of_mem_CQ' σ i (hCQ c)
  have hCmem : ∀ c : Ck, ι (c : ModGL τ (fixSubfield σ)) ∈ C := by
    intro c
    show ι (c : ModGL τ (fixSubfield σ)) ∈ rootSpan τ L (componentRoots χ i)
    exact map_baseChangeGL_rootSpan_le (fixSubfield σ).subtype (componentRoots χ i)
      ⟨c, c.2, rfl⟩
  have hfc : ∀ c : Ck, f c = z * ι (c : ModGL τ (fixSubfield σ)) * z⁻¹ := by
    intro c
    show (MulAut.conj z) (ι (c : ModGL τ (fixSubfield σ))) =
      z * ι (c : ModGL τ (fixSubfield σ)) * z⁻¹
    rw [MulAut.conj_apply]
  have hfC : ∀ c : Ck, f c ∈ C := by
    intro c
    rw [hfc c]
    exact (hnorm (ι (c : ModGL τ (fixSubfield σ)))).1 (hCmem c)
  have step_val : ∀ y : ModGL τ L, S.D.step y = S.D.n * S.D.Φ y * S.D.n⁻¹ := by
    intro y
    show (MulAut.conj S.D.n) (S.D.Φ y) = S.D.n * S.D.Φ y * S.D.n⁻¹
    rw [MulAut.conj_apply]
  have hfmodel : ∀ c : Ck, f c ∈ S.D.model := by
    intro c
    have hstepfix : S.D.step (f c) = f c := by
      have happ := hz (ι (c : ModGL τ (fixSubfield σ))) (hCmem c)
      rw [hfixCQ c, ← hfc c] at happ
      exact happ
    exact S.D.mem_model.2 ⟨rootSpan_le_adjointGroup L (componentRoots χ i) (hfC c),
      (step_val (f c)).symm.trans hstepfix⟩
  have hfΓ : ∀ c : Ck, f c ∈ S.Γ :=
    map_mem_commutator_of_perfect hperf f S.D.model hfmodel
  refine ⟨?_, ?_⟩
  · intro a b h
    have h1 : ι (a : ModGL τ (fixSubfield σ)) = ι (b : ModGL τ (fixSubfield σ)) :=
      (MulAut.conj z).injective (by
        show (MulAut.conj z) (ι (a : ModGL τ (fixSubfield σ))) =
          (MulAut.conj z) (ι (b : ModGL τ (fixSubfield σ)))
        exact h)
    have h2 : (a : ModGL τ (fixSubfield σ)) = (b : ModGL τ (fixSubfield σ)) :=
      baseChangeGL_injective (fixSubfield σ).subtype h1
    exact Subtype.ext h2
  · refine le_antisymm ?_ ?_
    · rintro _ ⟨c, rfl⟩
      exact map_mem_commutator_of_perfect hperf f (C ⊓ S.Γ) (fun c => ⟨hfC c, hfΓ c⟩) c
    · rw [Subgroup.commutator_le]
      intro x hx y hy
      have hxstep : S.D.step x = x := by
        have hxmodel : x ∈ S.D.model := (Subgroup.commutator_le_self S.D.model) hx.2
        exact (step_val x).trans (S.D.mem_model.1 hxmodel).2
      have hystep : S.D.step y = y := by
        have hymodel : y ∈ S.D.model := (Subgroup.commutator_le_self S.D.model) hy.2
        exact (step_val y).trans (S.D.mem_model.1 hymodel).2
      have hgC : z⁻¹ * x * z ∈ C := by
        show z⁻¹ * x * z ∈ componentRootSpan L χ i
        exact (hnorm (z⁻¹ * x * z)).2 (by
          have h : z * (z⁻¹ * x * z) * z⁻¹ = x := by group
          rw [h]; exact hx.1)
      have hg'C : z⁻¹ * y * z ∈ C := by
        show z⁻¹ * y * z ∈ componentRootSpan L χ i
        exact (hnorm (z⁻¹ * y * z)).2 (by
          have h : z * (z⁻¹ * y * z) * z⁻¹ = y := by group
          rw [h]; exact hy.1)
      have hgfix : frobGL σ (z⁻¹ * x * z) = z⁻¹ * x * z := by
        have happ := hz (z⁻¹ * x * z) hgC
        have h1 : z * (z⁻¹ * x * z) * z⁻¹ = x := by group
        rw [h1, hxstep] at happ
        have h2 : z * frobGL σ (z⁻¹ * x * z) * z⁻¹ = z * (z⁻¹ * x * z) * z⁻¹ := by
          rw [← happ, h1]
        calc frobGL σ (z⁻¹ * x * z)
            = z⁻¹ * (z * frobGL σ (z⁻¹ * x * z) * z⁻¹) * z := by group
          _ = z⁻¹ * (z * (z⁻¹ * x * z) * z⁻¹) * z := by rw [h2]
          _ = z⁻¹ * x * z := by group
      have hg'fix : frobGL σ (z⁻¹ * y * z) = z⁻¹ * y * z := by
        have happ := hz (z⁻¹ * y * z) hg'C
        have h1 : z * (z⁻¹ * y * z) * z⁻¹ = y := by group
        rw [h1, hystep] at happ
        have h2 : z * frobGL σ (z⁻¹ * y * z) * z⁻¹ = z * (z⁻¹ * y * z) * z⁻¹ := by
          rw [← happ, h1]
        calc frobGL σ (z⁻¹ * y * z)
            = z⁻¹ * (z * frobGL σ (z⁻¹ * y * z) * z⁻¹) * z := by group
          _ = z⁻¹ * (z * (z⁻¹ * y * z) * z⁻¹) * z := by rw [h2]
          _ = z⁻¹ * y * z := by group
      have hZy : frobGL σ (z⁻¹ * x * z) * (z⁻¹ * x * z)⁻¹ ∈ (⊥ : Subgroup (ModGL τ L)) := by
        simp [hgfix]
      have hZy' : frobGL σ (z⁻¹ * y * z) * (z⁻¹ * y * z)⁻¹ ∈ (⊥ : Subgroup (ModGL τ L)) := by
        simp [hg'fix]
      have hyspan : z⁻¹ * x * z ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)) := by
        show z⁻¹ * x * z ∈ rootSpan τ L (unionRoots χ ({i} : Set (KernelComponent χ)))
        rw [unionRoots_singleton]
        exact hgC
      have hy'span : z⁻¹ * y * z ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)) := by
        show z⁻¹ * y * z ∈ rootSpan τ L (unionRoots χ ({i} : Set (KernelComponent χ)))
        rw [unionRoots_singleton]
        exact hg'C
      have hcomm : ⁅z⁻¹ * x * z, z⁻¹ * y * z⁆ ∈ CQ σ i :=
        commutator_mem_CQ (σ := σ) (i := i) hs (Z := ⊥)
          (fun w hw a _ => by rw [Subgroup.mem_bot.1 hw]; simp)
          hyspan hy'span hZy hZy'
      rw [CQ_eq_map] at hcomm
      obtain ⟨c, hc, hceq⟩ := Subgroup.mem_map.1 hcomm
      refine MonoidHom.mem_range.2 ⟨⟨c, hc⟩, ?_⟩
      have hconj : f ⟨c, hc⟩ = (MulAut.conj z).toMonoidHom ⁅z⁻¹ * x * z, z⁻¹ * y * z⁆ := by
        show (MulAut.conj z).toMonoidHom (ι c) = _
        rw [show ι c = baseChangeGL (fixSubfield σ).subtype c from rfl, hceq]
      rw [hconj, map_commutatorElement]
      change ⁅MulAut.conj z (z⁻¹ * x * z), MulAut.conj z (z⁻¹ * y * z)⁆ = ⁅x, y⁆
      rw [MulAut.conj_apply, MulAut.conj_apply,
        show z * (z⁻¹ * x * z) * z⁻¹ = x by group,
        show z * (z⁻¹ * y * z) * z⁻¹ = y by group]

end CFSG.StandardType.F4ExplicitPos.FixedCover
end
end
end
end
end
end

end

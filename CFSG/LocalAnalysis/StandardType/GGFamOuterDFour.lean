module

public import CFSG.LocalAnalysis.StandardType.GGFamD4Pin
public import CFSG.LocalAnalysis.StandardType.GGFamIsolation
public import CFSG.LocalAnalysis.StandardType.GGFamRatComp
public import CFSG.LocalAnalysis.StandardType.GGFamTameTransfer
public import CFSG.LocalAnalysis.StandardType.GGExcCompSLDefs
public import CFSG.LocalAnalysis.StandardType.GGFamD4Index
public import CFSG.LocalAnalysis.StandardType.GGFamProperComponent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgRank4
public import CFSG.ClassicalInvolution.Q3.Q3TWWMinus
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCoreAssembly
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Plane
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Red
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4All
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Top
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTFieldCenter
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesRoots
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotMainSetup
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapCoverConj
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOneMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner
public import CFSG.Quasithin.Background.C1PackS15212C
public import CFSG.Quasithin.Background.F918H5
public import CFSG.Quasithin.Background.GoldschmidtS146RBend1
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructFieldExt
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructPGL
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructSimple
public import CFSG.Quasithin.EmptyFaithful.S14610Q1
public import CFSG.Quasithin.EmptyFaithful.S14610Top
public import CFSG.Quasithin.EmptyFaithful.S146F4
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S152Y15
public import CFSG.Quasithin.EmptyFaithful.S152Y19
public import CFSG.Quasithin.EmptyFaithful.S153E59A
public import CFSG.Quasithin.Recognition.ModelBridges
public import CFSG.Quasithin.Vol2.Ch1EightFourChar2
public import CFSG.Quasithin.Vol2.Ch3Sec3InspF618Tools
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3315R
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323B
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X
public import CFSG.RankThree.PartOne.KEXC.Basic
public import CFSG.RankThree.PartOne.TCX.Ree.Perm

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE

theorem fam_l154r4_of_d4_selected
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ)
    (b : Fin τ.rank → Lˣ) (j : KernelComponent (rootCharHom b))
    (hsel : componentRoots (rootCharHom b) j = componentRoots χ i)
    (v : WeylGroup τ)
    (hpin : componentRoots χ i =
      (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    (hρΨ : ∀ γ ∈ componentRoots χ i, S.ρ γ ∈ componentRoots χ i)
    (hout : ¬ twistInner (componentRoots χ i) (S.ρ : (Fin τ.rank → ℤ) → _)) :
    ∃ f : ℕ, ringChar L ^ f = S.D.q ∧
      CFSG.LocalAnalysis.GLTheoremA.K155X.L154R4Model (ringChar L) f
        ↥(rationalComponentM S.ρ S.Γ χ i) := by
  have hpinb : componentRoots (rootCharHom b) j =
      (fun α => v • α) '' parabolicRoots τ (d4Nodes τ) := by
    rw [hsel]; exact hpin
  have hρb : ∀ γ ∈ componentRoots (rootCharHom b) j,
      S.ρ γ ∈ componentRoots (rootCharHom b) j := by
    intro γ hγ
    rw [hsel] at hγ ⊢
    exact hρΨ γ hγ
  have houtb : ¬ twistInner (componentRoots (rootCharHom b) j)
      (S.ρ : (Fin τ.rank → ℤ) → _) := by
    rw [← hsel] at hout
    exact hout
  have hcomp : rationalComponent S.ρ S.Γ (rootCharHom b) j =
      rationalComponentM S.ρ S.Γ χ i :=
    (rationalComponentM_eq S.ρ S.Γ (rootCharHom b) j).symm.trans
      (rationalComponentM_eq_of_componentRoots_eq (ρ := S.ρ) (Γ := S.Γ)
        (χ := rootCharHom b) (χ' := χ) (i := j) (j := i) hsel)
  have hs_b : componentOrbitLength S.ρ (componentRoots (rootCharHom b) j) = 1 :=
    componentOrbitLength_eq_one
      ((finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1) hρb
  have h1b : ¬ twistInner (componentRoots (rootCharHom b) j)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom b) j)]) := by
    rw [hs_b, Function.iterate_one]
    exact houtb
  rcases hτ with rfl | rfl | rfl
  ·
    obtain ⟨w, hn⟩ := S.D.n_weyl
    obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
    rcases hP with rfl | ⟨t, ht, rfl⟩
    · have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
        ext1 g
        rw [hΦ, one_mul, inv_one, mul_one]
      obtain ⟨f, hf, hM⟩ :=
        CFSG.LocalAnalysis.GLTheoremA.K155X.l154r4_rationalComponent_of_d4_outer d4Base_E6
          d4TrialityLayer_E6 (d4SwapLayer_E6 e6FixDNAll_proved)
          CFSG.LocalAnalysis.GLTheoremA.K155X.l154r4_trialityLayer_E6
          CFSG.LocalAnalysis.GLTheoremA.K155X.l154r4_swapLayer_E6 S hFr hΦ' hn
          (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ' hn hγ) j v hpinb hρb h1b
      exact ⟨f, hf, by rw [hcomp] at hM; exact hM⟩
    · obtain ⟨f, hf, hM⟩ :=
        CFSG.LocalAnalysis.GLTheoremA.K155X.l154r4_rationalComponent_of_d4_twE6 S
          ⟨t, ht, Fr, hFr, hΦ⟩ j v hpinb hρb houtb
      exact ⟨f, hf, by rw [hcomp] at hM; exact hM⟩
  ·
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E7
    obtain ⟨w, hn⟩ := S.D.n_weyl
    obtain ⟨f, hf, hM⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.K155X.l154r4_rationalComponent_of_d4_outer d4Base_E7
        CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E7
        (d4SwapLayer_E7 e6FixDNAll_proved)
        CFSG.LocalAnalysis.GLTheoremA.K155X.l154r4_trialityLayer_E7
        CFSG.LocalAnalysis.GLTheoremA.K155X.l154r4_swapLayer_E7 S hFr hΦ hn
        (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) j v hpinb hρb h1b
    exact ⟨f, hf, by rw [hcomp] at hM; exact hM⟩
  ·
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E8
    obtain ⟨w, hn⟩ := S.D.n_weyl
    obtain ⟨f, hf, hM⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.K155X.l154r4_rationalComponent_of_d4_outer d4Base_E8
        CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E8
        (d4SwapLayer_E8 e6FixDNAll_proved)
        CFSG.LocalAnalysis.GLTheoremA.K155X.l154r4_trialityLayer_E8
        CFSG.LocalAnalysis.GLTheoremA.K155X.l154r4_swapLayer_E8 S hFr hΦ hn
        (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) j v hpinb hρb h1b
    exact ⟨f, hf, by rw [hcomp] at hM; exact hM⟩

theorem fam_outerD_four_selected_data
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type}
    {a : ι → Fin τ.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (i : KernelComponent (famCharHom a))
    (hr : compRank (componentRoots (famCharHom a) i) = 4)
    (hc : (componentRoots (famCharHom a) i).ncard = 24)
    (hout : ¬ twistInner (componentRoots (famCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (famCharHom a) i)])) :
    ∃ (b : Fin τ.rank → Lˣ) (j : KernelComponent (rootCharHom b)) (v : WeylGroup τ),
      componentRoots (rootCharHom b) j = componentRoots (famCharHom a) i ∧
      componentRoots (famCharHom a) i =
        (fun α => v • α) '' parabolicRoots τ (d4Nodes τ) ∧
      (∀ γ ∈ componentRoots (famCharHom a) i, S.ρ γ ∈ componentRoots (famCharHom a) i) ∧
      componentOrbitLength S.ρ (componentRoots (famCharHom a) i) = 1 ∧
      ¬ twistInner (componentRoots (famCharHom a) i) (S.ρ : (Fin τ.rank → ℤ) → _) := by
  have h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1 := by
    refine exists_nontrivial_member_of_component_rank_lt (τ := τ) hτ a i ?_
    rw [hr]
    rcases hτ with rfl | rfl | rfl <;> decide
  have hχp : ∀ γ, IsRoot τ γ → (famCharHom a) (Multiplicative.ofAdd γ) ^ p = 1 := by
    intro γ hγ
    funext u
    show rootChar (a u) γ ^ p = 1
    exact rootChar_pow_eq_one_of_forall (hap u) γ
  have hχ1 : ∃ γ, IsRoot τ γ ∧ (famCharHom a) (Multiplicative.ofAdd γ) ≠ 1 := by
    obtain ⟨u, hu⟩ := h1
    obtain ⟨γ, hγ, hne⟩ := exists_rootChar_ne_one hu
    exact ⟨γ, hγ, fun h => hne (congrFun h u)⟩
  have hρ : ∀ γ ∈ kernelRoots (famCharHom a), S.ρ γ ∈ kernelRoots (famCharHom a) :=
    fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ
  have himg : S.ρ '' componentRoots (famCharHom a) i = componentRoots (famCharHom a) i :=
    image_componentRoots_eq_of_d4_family hτ S hp hp2 hχp hχ1 hρ i hr hc
  have hρΨ : ∀ γ ∈ componentRoots (famCharHom a) i,
      S.ρ γ ∈ componentRoots (famCharHom a) i := by
    intro γ hγ
    rw [← himg]
    exact ⟨γ, hγ, rfl⟩
  have hs : componentOrbitLength S.ρ (componentRoots (famCharHom a) i) = 1 :=
    componentOrbitLength_eq_one
      ((finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1) hρΨ
  have hout' : ¬ twistInner (componentRoots (famCharHom a) i)
      (S.ρ : (Fin τ.rank → ℤ) → _) := by
    rw [hs, Function.iterate_one] at hout
    exact hout
  obtain ⟨N, b, j, hN, hN2, hbN, hsel⟩ := exists_isolating_element hτ a hp hp2 hap i
  have hNL : (N : L) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne hN (by rw [ringChar.eq L 2]; exact Ne.symm hN2)
  obtain ⟨v, hpinb⟩ :=
    d4_selected_pin_of_prime hτ S hN hNL b hbN j (by rw [hsel]; exact hr)
      (by rw [hsel]; exact hc)
  have hpin : componentRoots (famCharHom a) i =
      (fun α => v • α) '' parabolicRoots τ (d4Nodes τ) := by
    rw [← hsel]; exact hpinb
  exact ⟨b, j, v, hsel, hpin, hρΨ, hs, hout'⟩

theorem langFamRatFieldSL_outerD_four
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type}
    {a : ι → Fin τ.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (i : KernelComponent (famCharHom a))
    (hr : compRank (componentRoots (famCharHom a) i) = 4)
    (hc : (componentRoots (famCharHom a) i).ncard = 24)
    (hout : ¬ twistInner (componentRoots (famCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (famCharHom a) i)]))
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i)) :
    CFSG.StandardType.GGCompFieldAtSL
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i))
      (rationalComponentM S.ρ S.Γ (famCharHom a) i) := by
  obtain ⟨b, j, v, hsel, hpin, hρΨ, hs, hout'⟩ :=
    fam_outerD_four_selected_data hτ S hp hp2 hT hap i hr hc hout
  obtain ⟨f, hf, hM⟩ :=
    fam_l154r4_of_d4_selected hτ S (famCharHom a) i b j hsel v hpin hρΨ hout'
  have hq' : CFSG.Open.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) :=
    ⟨hq.1.commutator_eq_top, hq.2.1⟩
  rw [ringChar.eq L 2] at hf hM
  rw [hs, pow_one, ← hf]
  rcases hM with hm | hm
  · exact CFSG.StandardType.ggCompFieldAtSL_of_lieModel hq' hm (by decide)
  · exact CFSG.StandardType.ggCompFieldAtSL_of_lieModel hq' hm (by decide)

end CFSG.StandardType.TableCRes

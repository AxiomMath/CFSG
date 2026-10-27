module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE7
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUE8
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyTorus
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSU
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.AlgebraicGroups.ConnectedToralLang
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
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
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
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
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
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
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate2
public import Certificates.Kernel.SporSch.Th.Plane2320

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Classical2
open scoped MatrixGroups

private theorem langRatBF_kac_normal_form
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {m : ℕ}
    (hm : 0 < m) (hmL : (m : L) ≠ 0) {K : KacData τ} (hK : K.Facts)
    {a : Fin τ.rank → Lˣ} (hTm : rootDiagUnit τ a ^ m = 1) :
    ∃ (v : WeylGroup τ) (μ : Fin τ.rank → ℤ), K.IsNormal m μ ∧
      ∀ i : KernelComponent (rootCharHom a), ∃ x, K.IsZ m μ x ∧
        componentRoots (rootCharHom a) i = (fun α => v • α) '' K.rootsOf (K.comp m μ x) := by
  have : NeZero (m : L) := ⟨hmL⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L m
  have hu : IsUnit ζ := hζ.isUnit hm.ne'
  exact K.exists_smul_rootsOf hK hm (ζ := hu.unit) (by simpa using hζ) a
    (pow_eq_one_of_rootDiagUnit_pow hTm)

private theorem langRatBF_frame_of_order_m
    {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (K : KacData τ) (hK : K.Facts) {E : List (ℕ × ℕ)} {tp : ℕ → ℕ → List ℕ}
    (hT : IsTreePaths (τ.rank + 1) E tp)
    (hadj : ∀ x y : Option (Fin τ.rank), K.Adj x y ↔ (nodeIdx x, nodeIdx y) ∈ E)
    {cands : List (List ℕ)}
    (hcheck : ((List.range (τ.rank + 1)).sublists.all fun zl =>
      !(fun _ : List ℕ => true) zl ||
        zl.all fun x => cands.any (sameSet (compIdx (τ.rank + 1) tp zl x))) = true)
    (hlt : ∀ c ∈ cands, ∀ w ∈ c, w < τ.rank + 1)
    (hcard : ∀ c ∈ cands, (c.map (idxNode (r := τ.rank))).toFinset.card = c.length)
    {paths : List (List (Option (Fin τ.rank)))}
    (hcount : ∀ c ∈ cands, 2 ≤ c.length →
      kacCount τ K.θ (c.map (idxNode (r := τ.rank))).toFinset = c.length * (c.length + 1) →
        ∃ P ∈ paths, sameSet c (P.map nodeIdx) = true)
    (hpaths : ∀ P ∈ paths, P.Nodup ∧ 2 ≤ P.length ∧
      (∀ c d : Fin P.length, iform (K.extRoot (P.get c)) (K.extRoot (P.get d)) = chainGram c d) ∧
      ∀ (c : Fin P.length) (h : (c : ℕ) + 1 < P.length),
        (nodeIdx (P.get c), nodeIdx (P.get ⟨c + 1, h⟩)) ∈ E)
    {L : Type} [Field L] [IsAlgClosed L]
    (hframes : ∀ x y : Option (Fin τ.rank), (nodeIdx x, nodeIdx y) ∈ E →
      ∃ (ρ : SL(3, L) →* ModGL τ L) (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ),
        CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧ σ 0 1 = K.extRoot x ∧ σ 1 2 = K.extRoot y)
    {m : ℕ} (hm : 0 < m) (hmL : (m : L) ≠ 0)
    {a : Fin τ.rank → Lˣ} (hTm : rootDiagUnit τ a ^ m = 1)
    (i : KernelComponent (rootCharHom a))
    (h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)) :
    ∃ (ν : ℕ) (ψ : SL(ν, L) →* ModGL τ L) (σ : Fin ν → Fin ν → Fin τ.rank → ℤ), 3 ≤ ν ∧
      IsSLFrame ψ σ ∧ (∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * 1) ∧
        componentRoots (rootCharHom a) i = frameRoots σ := by
  classical
  obtain ⟨v, μ, -, hall⟩ := langRatBF_kac_normal_form hm hmL hK hTm
  obtain ⟨x, hx, hi⟩ := hall i
  obtain ⟨c, hc, hcomp⟩ := K.exists_comp_eq_of_check hT hadj (adm := fun _ => true) hcheck rfl hx
  set C : Finset (Option (Fin τ.rank)) := (c.map (idxNode (r := τ.rank))).toFinset with hCdef
  have hCset : K.comp m μ x = (C : Set (Option (Fin τ.rank))) := by
    rw [hcomp]
    ext y
    simp only [Set.mem_ofPred_eq, hCdef, List.coe_toFinset, List.mem_map]
    constructor
    · intro hy
      exact ⟨nodeIdx y, hy, idxNode_nodeIdx y⟩
    · rintro ⟨w, hw, rfl⟩
      rw [nodeIdx_idxNode (hlt c hc w hw)]
      exact hw
  have hCp : ∃ y, y ∉ C := by
    obtain ⟨y, hy⟩ := exists_not_mem_comp K hm μ x
    exact ⟨y, fun h => hy (by rw [hCset]; exact h)⟩
  have hi' : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' K.rootsOf (C : Set (Option (Fin τ.rank))) := by
    rw [hi, hCset]
  have hrank : compRank (componentRoots (rootCharHom a) i) = c.length := by
    rw [hi', compRank_image, compRank_rootsOf K hK hCp, hcard c hc]
  have hncard : (componentRoots (rootCharHom a) i).ncard =
      kacCount τ K.θ (c.map (idxNode (r := τ.rank))).toFinset := by
    rw [hi', ncard_image_smul, ncard_rootsOf K hK hCp]
  rw [hrank] at h2 hn
  rw [hncard] at hn
  obtain ⟨P, hP, hsame⟩ := hcount c hc h2 hn
  obtain ⟨hnd, hlen, hG, hedges⟩ := hpaths P hP
  have hCP : (C : Set (Option (Fin τ.rank))) = Set.range P.get := by
    rw [Set.range_list_get, ← hCset, hcomp]
    ext y
    simp only [Set.mem_ofPred_eq]
    rw [mem_iff_of_sameSet hsame, List.mem_map]
    constructor
    · rintro ⟨z, hz, hzy⟩
      rwa [← nodeIdx_injective hzy]
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hA2 : ∀ (k : Fin P.length) (h : (k : ℕ) + 1 < P.length), ∃ (ρ : SL(3, L) →* ModGL τ L)
      (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ), CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧
        σ 0 1 = K.extRoot (P.get k) ∧ σ 1 2 = K.extRoot (P.get ⟨k + 1, h⟩) :=
    fun k h => hframes _ _ (hedges k h)
  obtain ⟨ψ, σ, hψ, hσ⟩ := exists_frame_of_path hτ K (List.nodup_iff_injective_get.1 hnd) hG hA2 v
  refine ⟨P.length + 1, ψ, σ, by omega, hψ, fun a b hab => ?_, ?_⟩
  · rw [mul_one]
    exact CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ (hψ.isRoot a b hab)
  · rw [hi', hCP, hσ]

theorem langRatB_frame_exists
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] {m : ℕ}
    (hmL : (m : L) ≠ 0) {a : Fin τ.rank → Lˣ} (hTm : rootDiagUnit τ a ^ m = 1)
    (i : KernelComponent (rootCharHom a)) (h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)) :
    ∃ (ν : ℕ) (ψ : SL(ν, L) →* ModGL τ L) (σ : Fin ν → Fin ν → Fin τ.rank → ℤ),
      3 ≤ ν ∧ IsSLFrame ψ σ ∧ (∀ x y, x ≠ y → iform (σ x y) (σ x y) = 2 * 1) ∧
        componentRoots (rootCharHom a) i = frameRoots σ := by
  have hm : 0 < m := Nat.pos_of_ne_zero fun h => hmL (by simp [h])
  rcases hτ with rfl | rfl
  · exact langRatBF_frame_of_order_m (Or.inr (Or.inr (Or.inl rfl)))
      kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card e7_count e7_paths e7_frames
      hm hmL hTm i h2 hn
  · exact langRatBF_frame_of_order_m (Or.inr (Or.inr (Or.inr rfl)))
      kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card e8_count e8_paths e8_frames
      hm hmL hTm i h2 hn

end CFSG.StandardType.LangRat

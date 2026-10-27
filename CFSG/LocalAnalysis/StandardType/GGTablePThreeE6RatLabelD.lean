module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabel
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDMain
import CFSG.LocalAnalysis.StandardType.GGExclNoIso
import CFSG.RankThree.PartOne.KD4T.Certs
import Certificates.Certificate115
import Certificates.Certificate116
import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rank1
import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Generic
import CFSG.ClassicalInvolution.Models.TwistedPairs
import CFSG.ClassicalInvolution.WeakCT.SU4SpinMinusBridge
import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDChain
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDDatum
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDExport
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDKlein
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDMinus
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighDefs
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBRows
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBShape
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTClass
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTRows
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOneMinus
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner
import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
import CFSG.RankThree.PartOne.KE.E7FiveBlock
import CFSG.RankThree.PartOne.KE.E8D4Family
import CFSG.RankThree.PartTwo.Sec8.Item87Proof84

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section InnerD

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPTwoDMain
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE CFSG.Timmesfeld
  CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw
open scoped MatrixGroups Matrix

private def RecogD
 (p Q : ℕ) (C : Type) [Group C] (r : ℕ) : Prop :=
  commutator C = ⊤ ∧ ∃ f : ℕ, LieModel (C ⧸ Subgroup.center C) .POmegaPlus r p f ∧ p ^ f = Q

private theorem langRat_isQuasisimple
 {Q : Type} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.Open.IsQuasisimple Q :=
  ⟨Group.isPerfect_def.1 h.1, h.2.1⟩

private theorem recogD_of_range
 {p Q r : ℕ} {X G : Type} [Group X] [Group G]
    (h : RecogD p Q X r) (Ψ : X →* G) (hker : Ψ.ker ≤ Subgroup.center X)
    {H : Subgroup G} (hrange : Ψ.range = H) : RecogD p Q ↥H r := by
  obtain ⟨hperf, f, hmodel, hpow⟩ := h
  have hmem : ∀ x, Ψ x ∈ H := fun x => hrange ▸ ⟨x, rfl⟩
  let g : X →* ↥H := Ψ.codRestrict H hmem
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ : y ∈ Ψ.range := hrange ▸ hy
    exact ⟨x, Subtype.ext hx⟩
  have hgk : g.ker ≤ Subgroup.center X := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact congrArg Subtype.val hx
  obtain ⟨e⟩ := nonempty_centralQuotient_mulEquiv hperf g hg hgk
  exact ⟨commutator_eq_top_of_surjective_innerRecog hperf g hg,
    f, LieModel.of_mulEquiv e hmodel, hpow⟩

private theorem recogD_innerRecogOver_D
    {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {n : ℕ}
    (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 0 < f)
    (hK : Nat.card K = p ^ f) {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ)
    (hroot : ∀ b, IsRoot τ (β b)) (l : Fin n → ι)
    (hgram : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin n, edgeD n i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    RecogD p (p ^ f) ↥(rootSpan τ K (rootsOfFam β (Set.range l))) n := by
  classical
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeD n) hgram hframe
  have hadm : StatedLieAdmissible .POmegaPlus n p f := ⟨hp, hf, hn⟩
  obtain ⟨-, -, -, hqs, -, hmodel⟩ := weakCT_spinPlus_of_frame hadm (by omega) hK U
    hgen hcomm hρ hψ
  exact ⟨hqs.1.commutator_eq_top, f, hmodel, rfl⟩

private theorem recogD_ratCat_of_innerRecogOver
    {τ : Tag} {L : Type}
    [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {ta : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ ta ∈ S.D.torus) (i : KernelComponent (rootCharHom ta))
    (hinner : twistInner (componentRoots (rootCharHom ta) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom ta) i)]))
    {r : ℕ}
    (hrec : ∀ K : Subfield L, Finite ↥K →
      Nat.card ↥K = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) →
      RecogD (ringChar L) (Nat.card ↥K) ↥(componentRootSpan K (rootCharHom ta) i) r) :
    RecogD (ringChar L)
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i))
      ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) r := by
  classical
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  obtain ⟨σ, hfin, hcard, f, hf1, hker, hf2⟩ := exists_inner_cover S hT i hinner
  have hrecσ := hrec (fixSubfield σ) hfin hcard
  have hCperf : ⁅componentRootSpan (fixSubfield σ) (rootCharHom ta) i,
      componentRootSpan (fixSubfield σ) (rootCharHom ta) i⁆ =
      componentRootSpan (fixSubfield σ) (rootCharHom ta) i :=
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hrecσ.1)
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom ta) i :=
    le_antisymm (hf2 hCperf) hf1
  rw [hcard] at hrecσ
  exact recogD_of_range hrecσ f hker hRf

private theorem recogD_ratCat_of_tree
    {τ : Tag} (K : KacData τ) {L : Type}
    [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hTor : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    {r : ℕ} (v : WeylGroup τ) {n : ℕ} (l : Fin n → Option (Fin τ.rank))
    (hroots : componentRoots (rootCharHom a) i = (fun α => v • α) '' K.rootsOf (Set.range l))
    (hrec : ∀ (K' : Type) [Field K'] [Finite K'] (p f : ℕ), p.Prime → 0 < f →
      Nat.card K' = p ^ f →
      RecogD p (p ^ f) ↥(rootSpan τ K' (rootsOfFam (fun x => v • K.extRoot x) (Set.range l))) r) :
    RecogD (ringChar L)
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) r := by
  classical
  refine recogD_ratCat_of_innerRecogOver S hTor i hinner (fun K' hK' _ => ?_)
  set β : Option (Fin τ.rank) → Fin τ.rank → ℤ := fun x => v • K.extRoot x with hβ
  have hsmulcombo : ∀ n' : Option (Fin τ.rank) → ℕ, v • K.combo n' = ∑ x, (n' x : ℤ) • β x := by
    intro n'
    unfold KacData.combo
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun x _ => smul_comm v ((n' x : ℕ) : ℤ) (K.extRoot x)
  have hset : (fun α => v • α) '' K.rootsOf (Set.range l) = rootsOfFam β (Set.range l) := by
    ext γ
    constructor
    · rintro ⟨γ₀, ⟨hr0, n', hn', hγ⟩, rfl⟩
      refine ⟨IsRoot.smul hr0 v, n', hn', ?_⟩
      rcases hγ with rfl | rfl
      · exact Or.inl (hsmulcombo n')
      · exact Or.inr (by show v • (-K.combo n') = _; rw [smul_neg, hsmulcombo])
    · rintro ⟨hr, n', hn', hγ⟩
      refine ⟨v⁻¹ • γ, ⟨IsRoot.smul hr v⁻¹, n', hn', ?_⟩, smul_inv_smul v γ⟩
      rcases hγ with rfl | rfl
      · left
        rw [← hsmulcombo, inv_smul_smul]
      · right
        rw [smul_neg, ← hsmulcombo, inv_smul_smul]
  have hcomp : componentRootSpan K' (rootCharHom a) i =
      rootSpan τ K' (rootsOfFam β (Set.range l)) := by
    show rootSpan τ K' (componentRoots (rootCharHom a) i) = _
    rw [hroots, hset]
  rw [hcomp]
  haveI : Fintype ↥K' := Fintype.ofFinite ↥K'
  haveI : CharP ↥K' (ringChar ↥K') := ringChar.charP ↥K'
  obtain ⟨f, hprime, hcardK⟩ := FiniteField.card ↥K' (ringChar ↥K')
  have hring : ringChar ↥K' = ringChar L := ringChar_subfield' K'
  rw [hring] at hprime hcardK
  have hK'card : Nat.card ↥K' = ringChar L ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcardK]
  rw [hK'card]
  exact hrec ↥K' (ringChar L) f hprime f.pos hK'card

private theorem recogD_ratCat_of_dClass
    {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : KacData τ)
    (hK : K.Facts) {E : List (ℕ × ℕ)} {tp : ℕ → ℕ → List ℕ}
    (hT : IsTreePaths (τ.rank + 1) E tp)
    (hadj : ∀ x y : Option (Fin τ.rank), K.Adj x y ↔ (nodeIdx x, nodeIdx y) ∈ E)
    {cands : List (List ℕ)}
    (hcheck : ((List.range (τ.rank + 1)).sublists.all fun zl =>
      !(fun _ : List ℕ => true) zl ||
        zl.all fun x => cands.any (sameSet (compIdx (τ.rank + 1) tp zl x))) = true)
    (hlt : ∀ c ∈ cands, ∀ w ∈ c, w < τ.rank + 1)
    (hcard : ∀ c ∈ cands, (c.map (idxNode (r := τ.rank))).toFinset.card = c.length)
    {trees : List (List (Option (Fin τ.rank)))}
    (hcount : ∀ c ∈ cands, 4 ≤ c.length →
      kacCount τ K.θ (c.map (idxNode (r := τ.rank))).toFinset = 2 * c.length * (c.length - 1) →
        ∃ P ∈ trees, sameSet c (P.map nodeIdx) = true)
    (htrees : ∀ P ∈ trees, P.Nodup ∧ 4 ≤ P.length ∧
      (∀ c d : Fin P.length, c ≠ d → ¬ edgeD P.length c d → ¬ edgeD P.length d c →
        iform (K.extRoot (P.get c)) (K.extRoot (P.get d)) = 0) ∧
      ∀ c d : Fin P.length, edgeD P.length c d →
        (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ E)
    (hframes : ∀ {F : Type} [Field F] (x y : Option (Fin τ.rank)),
      (nodeIdx x, nodeIdx y) ∈ E →
        ∃ (ρ : SL(3, F) →* ModGL τ F) (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ),
          CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧ σ 0 1 = K.extRoot x ∧
            σ 1 2 = K.extRoot y)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ} (hTor : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RecogD (ringChar L)
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
      (compRank (componentRoots (rootCharHom a) i)) := by
  classical
  obtain ⟨v, n, l, hn4, -, hroots, hnon, hE, hnc⟩ :=
    exists_tree_of_class' K hK hT hadj hcheck hlt hcard edgeD 4 (fun n => 2 * n * (n - 1))
      hcount htrees (fun _ => True) (fun _ _ => trivial) S hp hpL hTp i h4 hn
  rw [← hnc]
  refine recogD_ratCat_of_tree K S hTor i hinner (r := n) v l hroots ?_
  intro K' _ _ p' f hp' hf hK'
  exact recogD_innerRecogOver_D hτ hn4 hp' hf hK' (fun x => v • K.extRoot x)
    (fun b => IsRoot.smul (K.isRoot_extRoot b) v) l
    (fun c d hcd h1 h2 => by
      show iform (v • K.extRoot (l c)) (v • K.extRoot (l d)) = 0
      rw [iform_smul]
      exact hnon c d hcd h1 h2)
    (treeFrames K hframes v l (edgeD n) hE)

private theorem recogD_E6_inner
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) {p : ℕ} (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E6 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hD : 4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard =
        2 * compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) - 1))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RecogD (ringChar L)
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
      (compRank (componentRoots (rootCharHom a) i)) := by
  classical
  exact recogD_ratCat_of_dClass (Or.inr (Or.inl rfl)) kacE6 facts_E6 e6_tree e6_adj e6_check
    e6_lt e6_card e6_dcount e6_dtrees (fun {F} _ x y h => e6_frames x y h) S hp hpL hT hTp i
    hD.1 hD.2 hinner

private theorem recogD_to_label
 {L : Type} [Field L] {C : Type} [Group C] {Q r : ℕ}
    (hchar : ringChar L = 2) (hq : CFSG.IsQuasisimple C) (h : RecogD (ringChar L) Q C r) :
    ∃ lab : LargeEvenLabel, 2 ^ lab.n = Q ∧ lab.tag = .D ∧ lab.rank = r ∧
      LargeEvenInLambda2 lab ∧ GGHasLabel lab (C ⧸ Subgroup.center C) := by
  obtain ⟨-, f, hmodel, hpow⟩ := h
  rw [hchar] at hmodel hpow
  have hZ : Subgroup.center (C ⧸ Subgroup.center C) = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.SporadicRank.center_quotient_center_eq_bot
      (langRat_isQuasisimple hq)
  obtain ⟨lab, hlab, htag, hrank, -, hdeg, hraw⟩ :=
    exists_label_rawDatum_of_lieModel hZ hmodel
  obtain ⟨htagD, hrank_ne⟩ := tag_eq_D_of_markTag_eq_POmegaPlus htag
  have hdeg' : lab.n = f := by
    rw [← hdeg]
    simp [markDeg, htagD]
  have hrank' : lab.rank = r := by
    rw [← hrank]
    simp [markRank, htagD, hrank_ne]
  exact ⟨lab, by rw [hdeg', hpow], htagD, hrank', hlab, hraw⟩

end InnerD

theorem rationalLabel_innerD_E6

    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) {p : ℕ} (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E6 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hD : 4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard =
        2 * compRank (componentRoots (rootCharHom a) i) * (compRank (componentRoots (rootCharHom a) i) - 1))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)]))
    (hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ∃ lab : LargeEvenLabel, 2 ^ lab.n = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
      lab.tag = .D ∧ lab.rank = compRank (componentRoots (rootCharHom a) i) ∧ RationalLabelIs S i lab := by
  have hchar : ringChar L = 2 := ringChar.eq L 2
  exact recogD_to_label hchar hQS (recogD_E6_inner S hp hpL hT hTp i hD hinner)

end CFSG.StandardType.TablePThreeKG

end

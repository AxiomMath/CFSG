module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabel
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacE
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc2
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDMain
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacDAll
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacEAll
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.RecogE
import CFSG.LocalAnalysis.StandardType.GGExclNoIso
import CFSG.RankThree.PartOne.KD4T.Certs
import Certificates.Certificate115
import Certificates.Certificate116
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUFrame
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E8D4Family
import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rank1
import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Generic
import CFSG.ClassicalInvolution.Q3.Q3TWWMinus
import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4All
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
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
import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
import CFSG.RankThree.PartOne.KEXC.Basic
import CFSG.RankThree.PartOne.TCX.Ree.Perm
import CFSG.RankThree.PartTwo.Sec8.Item87Proof84

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

section CertProofs

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

private def RecogT (p Q : ℕ) (C : Type) [Group C] (t : CFSG.Open.StatedLieTag) (r : ℕ) : Prop :=
  commutator C = ⊤ ∧ ∃ f : ℕ, LieModel (C ⧸ Subgroup.center C) t r p f ∧ p ^ f = Q

private theorem recogT_isQuasisimple {Q : Type} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.Open.IsQuasisimple Q :=
  ⟨Group.isPerfect_def.1 h.1, h.2.1⟩

private theorem recogT_of_range {p Q : ℕ} {t : CFSG.Open.StatedLieTag} {r : ℕ}
    {X G : Type} [Group X] [Group G]
    (h : RecogT p Q X t r) (Ψ : X →* G) (hker : Ψ.ker ≤ Subgroup.center X)
    {H : Subgroup G} (hrange : Ψ.range = H) : RecogT p Q ↥H t r := by
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

private theorem recogT_innerRecogOver_D
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
    RecogT p (p ^ f) ↥(rootSpan τ K (rootsOfFam β (Set.range l))) .POmegaPlus n := by
  classical
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeD n) hgram hframe
  have hadm : StatedLieAdmissible .POmegaPlus n p f := ⟨hp, hf, hn⟩
  obtain ⟨-, -, -, hqs, -, hmodel⟩ := weakCT_spinPlus_of_frame hadm (by omega) hK U
    hgen hcomm hρ hψ
  exact ⟨hqs.1.commutator_eq_top, f, hmodel, rfl⟩

private theorem recogT_innerRecogOver_E6
    {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (hK : Nat.card K = p ^ f)
    {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ) (hroot : ∀ b, IsRoot τ (β b))
    (l : Fin 6 → ι)
    (hgram : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin 6, edgeE 6 i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    RecogT p (p ^ f) ↥(rootSpan τ K (rootsOfFam β (Set.range l))) .E6 0 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeE 6) hgram hframe
  have hadm : StatedLieAdmissible .E6 0 p f := ⟨hp, hf, rfl⟩
  obtain ⟨-, -, -, hqs, -, hmodel⟩ := weakCT_e6_of_frame p f hadm hK U hgen hcomm hρ hψ
  exact ⟨hqs.1.commutator_eq_top, f, hmodel, rfl⟩

private theorem recogT_innerRecogOver_E7
    {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (hK : Nat.card K = p ^ f)
    {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ) (hroot : ∀ b, IsRoot τ (β b))
    (l : Fin 7 → ι)
    (hgram : ∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin 7, edgeE 7 i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    RecogT p (p ^ f) ↥(rootSpan τ K (rootsOfFam β (Set.range l))) .E7 0 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeE 7) hgram hframe
  have hadm : StatedLieAdmissible .E7 0 p f := ⟨hp, hf, rfl⟩
  obtain ⟨-, -, -, hqs, -, hmodel⟩ := weakCT_e7_of_frame p f hadm hK U hgen hcomm hρ hψ
  exact ⟨hqs.1.commutator_eq_top, f, hmodel, rfl⟩

private theorem recogT_innerRecogOver_E8
    {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (hK : Nat.card K = p ^ f)
    {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ) (hroot : ∀ b, IsRoot τ (β b))
    (l : Fin 8 → ι)
    (hgram : ∀ i j : Fin 8, i ≠ j → ¬ edgeE 8 i j → ¬ edgeE 8 j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin 8, edgeE 8 i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    RecogT p (p ^ f) ↥(rootSpan τ K (rootsOfFam β (Set.range l))) .E8 0 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeE 8) hgram hframe
  have hadm : StatedLieAdmissible .E8 0 p f := ⟨hp, hf, rfl⟩
  obtain ⟨-, -, -, hqs, -, hmodel⟩ := weakCT_e8_of_frame p f hadm hK U hgen hcomm hρ hψ
  exact ⟨hqs.1.commutator_eq_top, f, hmodel, rfl⟩

private theorem recogT_ratCat_of_innerRecogOver
    {τ : Tag} {L : Type}
    [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {ta : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ ta ∈ S.D.torus) (i : KernelComponent (rootCharHom ta))
    (hinner : twistInner (componentRoots (rootCharHom ta) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom ta) i)]))
    {t : CFSG.Open.StatedLieTag} {r : ℕ}
    (hrec : ∀ K : Subfield L, Finite ↥K →
      Nat.card ↥K = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) →
      RecogT (ringChar L) (Nat.card ↥K) ↥(componentRootSpan K (rootCharHom ta) i) t r) :
    RecogT (ringChar L)
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i))
      ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) t r := by
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
  exact recogT_of_range hrecσ f hker hRf

private theorem recogT_ratCat_of_tree
    {τ : Tag} (K : KacData τ)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ} (hTor : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    {t : CFSG.Open.StatedLieTag} {r : ℕ}
    (v : WeylGroup τ) {n : ℕ} (l : Fin n → Option (Fin τ.rank))
    (hroots : componentRoots (rootCharHom a) i = (fun α => v • α) '' K.rootsOf (Set.range l))
    (hrec : ∀ (K' : Type) [Field K'] [Finite K'] (p f : ℕ), p.Prime → 0 < f →
      Nat.card K' = p ^ f →
      RecogT p (p ^ f)
        ↥(rootSpan τ K' (rootsOfFam (fun x => v • K.extRoot x) (Set.range l))) t r) :
    RecogT (ringChar L)
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) t r := by
  classical
  refine recogT_ratCat_of_innerRecogOver S hTor i hinner (fun K' hK' _ => ?_)
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

private theorem recogT_ratCat_of_dClass
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
    RecogT (ringChar L)
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
      .POmegaPlus (compRank (componentRoots (rootCharHom a) i)) := by
  classical
  obtain ⟨v, n, l, hn4, -, hroots, hnon, hE, hnc⟩ :=
    exists_tree_of_class' K hK hT hadj hcheck hlt hcard edgeD 4 (fun n => 2 * n * (n - 1))
      hcount htrees (fun _ => True) (fun _ _ => trivial) S hp hpL hTp i h4 hn
  rw [← hnc]
  refine recogT_ratCat_of_tree K S hTor i hinner (t := .POmegaPlus) (r := n) v l hroots ?_
  intro K' _ _ p' f hp' hf hK'
  exact recogT_innerRecogOver_D hτ hn4 hp' hf hK' (fun x => v • K.extRoot x)
    (fun b => IsRoot.smul (K.isRoot_extRoot b) v) l
    (fun c d hcd h1 h2 => by
      show iform (v • K.extRoot (l c)) (v • K.extRoot (l d)) = 0
      rw [iform_smul]
      exact hnon c d hcd h1 h2)
    (treeFrames K hframes v l (edgeD n) hE)

private theorem recogT_ratCat_of_eClass
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
    (hcount : ∀ c ∈ cands, 6 ≤ c.length →
      kacCount τ K.θ (c.map (idxNode (r := τ.rank))).toFinset = eRootCount c.length →
        ∃ P ∈ trees, sameSet c (P.map nodeIdx) = true)
    (htrees : ∀ P ∈ trees, P.Nodup ∧ 6 ≤ P.length ∧
      (∀ c d : Fin P.length, c ≠ d → ¬ edgeE P.length c d → ¬ edgeE P.length d c →
        iform (K.extRoot (P.get c)) (K.extRoot (P.get d)) = 0) ∧
      ∀ c d : Fin P.length, edgeE P.length c d →
        (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ E)
    (hlen : ∀ P ∈ trees, P.length = 6 ∨ P.length = 7 ∨ P.length = 8)
    (hframes : ∀ {F : Type} [Field F] (x y : Option (Fin τ.rank)),
      (nodeIdx x, nodeIdx y) ∈ E →
        ∃ (ρ : SL(3, F) →* ModGL τ F) (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ),
          CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧ σ 0 1 = K.extRoot x ∧
            σ 1 2 = K.extRoot y)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ} (hTor : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h6 : 6 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      eRootCount (compRank (componentRoots (rootCharHom a) i)))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RecogT (ringChar L)
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) .E6 0 ∨
    RecogT (ringChar L)
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) .E7 0 ∨
    RecogT (ringChar L)
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) .E8 0 := by
  classical
  obtain ⟨v, n, l, hn6, hQ, hroots, hnon, hE⟩ :=
    exists_tree_of_class K hK hT hadj hcheck hlt hcard edgeE 6 eRootCount hcount htrees
      (fun n => n = 6 ∨ n = 7 ∨ n = 8) hlen S hp hpL hTp i h6 hn
  rcases hQ with rfl | rfl | rfl
  · left
    refine recogT_ratCat_of_tree K S hTor i hinner (t := .E6) (r := 0) v l hroots ?_
    intro K' _ _ p' f hp' hf hK'
    have hgr : ∀ c d : Fin 6, c ≠ d → ¬ edgeE 6 c d → ¬ edgeE 6 d c →
        iform ((fun x => v • K.extRoot x) (l c)) ((fun x => v • K.extRoot x) (l d)) = 0 := by
      intro c d hcd h1 h2
      show iform (v • K.extRoot (l c)) (v • K.extRoot (l d)) = 0
      rw [iform_smul]
      exact hnon c d hcd h1 h2
    exact recogT_innerRecogOver_E6 hτ hp' hf hK' (fun x => v • K.extRoot x)
      (fun b => IsRoot.smul (K.isRoot_extRoot b) v) l hgr
      (treeFrames K hframes v l (edgeE 6) hE)
  · right; left
    refine recogT_ratCat_of_tree K S hTor i hinner (t := .E7) (r := 0) v l hroots ?_
    intro K' _ _ p' f hp' hf hK'
    have hgr : ∀ c d : Fin 7, c ≠ d → ¬ edgeE 7 c d → ¬ edgeE 7 d c →
        iform ((fun x => v • K.extRoot x) (l c)) ((fun x => v • K.extRoot x) (l d)) = 0 := by
      intro c d hcd h1 h2
      show iform (v • K.extRoot (l c)) (v • K.extRoot (l d)) = 0
      rw [iform_smul]
      exact hnon c d hcd h1 h2
    exact recogT_innerRecogOver_E7 hτ hp' hf hK' (fun x => v • K.extRoot x)
      (fun b => IsRoot.smul (K.isRoot_extRoot b) v) l hgr
      (treeFrames K hframes v l (edgeE 7) hE)
  · right; right
    refine recogT_ratCat_of_tree K S hTor i hinner (t := .E8) (r := 0) v l hroots ?_
    intro K' _ _ p' f hp' hf hK'
    have hgr : ∀ c d : Fin 8, c ≠ d → ¬ edgeE 8 c d → ¬ edgeE 8 d c →
        iform ((fun x => v • K.extRoot x) (l c)) ((fun x => v • K.extRoot x) (l d)) = 0 := by
      intro c d hcd h1 h2
      show iform (v • K.extRoot (l c)) (v • K.extRoot (l d)) = 0
      rw [iform_smul]
      exact hnon c d hcd h1 h2
    exact recogT_innerRecogOver_E8 hτ hp' hf hK' (fun x => v • K.extRoot x)
      (fun b => IsRoot.smul (K.isRoot_extRoot b) v) l hgr
      (treeFrames K hframes v l (edgeE 8) hE)

private theorem recogD_E7_inner
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E7 L p₀) {p : ℕ} (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E7.rank → Lˣ} (hT : rootDiagUnit Tag.E7 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E7 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hD : 4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard =
        2 * compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) - 1))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RecogT (ringChar L)
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
      .POmegaPlus (compRank (componentRoots (rootCharHom a) i)) :=
  recogT_ratCat_of_dClass (Or.inr (Or.inr (Or.inl rfl))) kacE7 facts_E7 e7_tree e7_adj
    e7_check e7_lt e7_card e7_dcount e7_dtrees (fun {F} _ x y h => e7_frames x y h) S hp hpL
    hT hTp i hD.1 hD.2 hinner

private theorem recogD_E8_inner
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E8 L p₀) {p : ℕ} (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E8.rank → Lˣ} (hT : rootDiagUnit Tag.E8 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E8 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hD : 4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard =
        2 * compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) - 1))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RecogT (ringChar L)
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
      .POmegaPlus (compRank (componentRoots (rootCharHom a) i)) :=
  recogT_ratCat_of_dClass (Or.inr (Or.inr (Or.inr rfl))) kacE8 facts_E8 e8_tree e8_adj
    e8_check e8_lt e8_card e8_dcount e8_dtrees (fun {F} _ x y h => e8_frames x y h) S hp hpL
    hT hTp i hD.1 hD.2 hinner

private theorem tag_eq_E6_of_markTag {lab : LargeEvenLabel} (h : markTag lab = .E6) :
    lab.tag = .E6 := by
  obtain ⟨tg, r, n⟩ := lab
  revert h
  cases tg <;> simp [markTag] <;> split_ifs <;> simp_all

private theorem tag_eq_E7_of_markTag {lab : LargeEvenLabel} (h : markTag lab = .E7) :
    lab.tag = .E7 := by
  obtain ⟨tg, r, n⟩ := lab
  revert h
  cases tg <;> simp [markTag] <;> split_ifs <;> simp_all

private theorem tag_eq_E8_of_markTag {lab : LargeEvenLabel} (h : markTag lab = .E8) :
    lab.tag = .E8 := by
  obtain ⟨tg, r, n⟩ := lab
  revert h
  cases tg <;> simp [markTag] <;> split_ifs <;> simp_all

private theorem tag_eq_twE6_of_markTag {lab : LargeEvenLabel} (h : markTag lab = .twistedE6) :
    lab.tag = .twE6 := by
  obtain ⟨tg, r, n⟩ := lab
  revert h
  cases tg <;> simp [markTag] <;> split_ifs <;> simp_all

private theorem recogD_to_label
    {L : Type} [Field L] {C : Type} [Group C] {Q r : ℕ}
    (hchar : ringChar L = 2) (hq : CFSG.IsQuasisimple C)
    (h : RecogT (ringChar L) Q C .POmegaPlus r) :
    ∃ lab : LargeEvenLabel, 2 ^ lab.n = Q ∧ lab.tag = .D ∧ lab.rank = r ∧
      LargeEvenInLambda2 lab ∧ GGHasLabel lab (C ⧸ Subgroup.center C) := by
  obtain ⟨-, f, hmodel, hpow⟩ := h
  rw [hchar] at hmodel hpow
  have hZ : Subgroup.center (C ⧸ Subgroup.center C) = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.SporadicRank.center_quotient_center_eq_bot
      (recogT_isQuasisimple hq)
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

private theorem markDeg_eq_n_of_tag_eq {lab : LargeEvenLabel}
    (h : lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .twE6) :
    markDeg lab = lab.n := by
  obtain ⟨tg, r, n⟩ := lab
  change tg = .E6 ∨ tg = .E7 ∨ tg = .E8 ∨ tg = .twE6 at h
  rcases h with h | h | h | h <;> (subst h; rfl)

private theorem recogT_to_label_tag
    {L : Type} [Field L] {C : Type} [Group C] {Q : ℕ}
    {t : CFSG.Open.StatedLieTag} {tg : LargeEvenLieTag}
    (htag : ∀ {lab : LargeEvenLabel}, markTag lab = t → lab.tag = tg)
    (hdeg : ∀ {lab : LargeEvenLabel}, lab.tag = tg → markDeg lab = lab.n)
    (hchar : ringChar L = 2) (hq : CFSG.IsQuasisimple C)
    (h : RecogT (ringChar L) Q C t 0) :
    ∃ lab : LargeEvenLabel, 2 ^ lab.n = Q ∧ lab.tag = tg ∧
      LargeEvenInLambda2 lab ∧ GGHasLabel lab (C ⧸ Subgroup.center C) := by
  obtain ⟨-, f, hmodel, hpow⟩ := h
  rw [hchar] at hmodel hpow
  have hZ : Subgroup.center (C ⧸ Subgroup.center C) = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.SporadicRank.center_quotient_center_eq_bot
      (recogT_isQuasisimple hq)
  obtain ⟨lab, hlab, hmk, -, -, hdeg', hraw⟩ :=
    exists_label_rawDatum_of_lieModel hZ hmodel
  have htag' : lab.tag = tg := htag hmk
  have hn : lab.n = f := by
    rw [← hdeg']
    exact (hdeg htag').symm
  exact ⟨lab, by rw [hn, hpow], htag', hlab, hraw⟩

private theorem recogE_to_label
    {L : Type} [Field L] {C : Type} [Group C] {Q : ℕ}
    (hchar : ringChar L = 2) (hq : CFSG.IsQuasisimple C)
    (h : RecogT (ringChar L) Q C .E6 0 ∨ RecogT (ringChar L) Q C .E7 0 ∨
      RecogT (ringChar L) Q C .E8 0) :
    ∃ lab : LargeEvenLabel, 2 ^ lab.n = Q ∧
      (lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8) ∧ LargeEvenInLambda2 lab ∧
      GGHasLabel lab (C ⧸ Subgroup.center C) := by
  rcases h with h | h | h
  · obtain ⟨lab, hn, htag, hlab, hraw⟩ :=
      recogT_to_label_tag (t := .E6) (tg := .E6)
        (fun {_} h => tag_eq_E6_of_markTag h)
        (fun {_} h => markDeg_eq_n_of_tag_eq (Or.inl h)) hchar hq h
    exact ⟨lab, hn, Or.inl htag, hlab, hraw⟩
  · obtain ⟨lab, hn, htag, hlab, hraw⟩ :=
      recogT_to_label_tag (t := .E7) (tg := .E7)
        (fun {_} h => tag_eq_E7_of_markTag h)
        (fun {_} h => markDeg_eq_n_of_tag_eq (Or.inr (Or.inl h))) hchar hq h
    exact ⟨lab, hn, Or.inr (Or.inl htag), hlab, hraw⟩
  · obtain ⟨lab, hn, htag, hlab, hraw⟩ :=
      recogT_to_label_tag (t := .E8) (tg := .E8)
        (fun {_} h => tag_eq_E8_of_markTag h)
        (fun {_} h => markDeg_eq_n_of_tag_eq (Or.inr (Or.inr (Or.inl h)))) hchar hq h
    exact ⟨lab, hn, Or.inr (Or.inr htag), hlab, hraw⟩

private theorem recogTwE6_to_label
    {L : Type} [Field L] {C : Type} [Group C] {Q : ℕ}
    (hchar : ringChar L = 2) (hq : CFSG.IsQuasisimple C)
    (h : RecogT (ringChar L) Q C .twistedE6 0) :
    ∃ lab : LargeEvenLabel, 2 ^ lab.n = Q ∧ lab.tag = .twE6 ∧
      LargeEvenInLambda2 lab ∧ GGHasLabel lab (C ⧸ Subgroup.center C) :=
  recogT_to_label_tag (t := .twistedE6) (tg := .twE6)
    (fun {_} h => tag_eq_twE6_of_markTag h)
    (fun {_} h => markDeg_eq_n_of_tag_eq (Or.inr (Or.inr (Or.inr h)))) hchar hq h

theorem rationalLabel_innerD_E78
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {p : ℕ} (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hD : 4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard =
        2 * compRank (componentRoots (rootCharHom a) i) * (compRank (componentRoots (rootCharHom a) i) - 1))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)]))
    (hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ∃ lab : LargeEvenLabel, 2 ^ lab.n = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
      lab.tag = .D ∧ lab.rank = compRank (componentRoots (rootCharHom a) i) ∧ RationalLabelIs S i lab := by
  have hchar : ringChar L = 2 := ringChar.eq L 2
  rcases hτ with rfl | rfl
  · exact recogD_to_label hchar hQS (recogD_E7_inner S hp hpL hT hTp i hD hinner)
  · exact recogD_to_label hchar hQS (recogD_E8_inner S hp hpL hT hTp i hD hinner)

theorem rationalLabel_innerE_E78
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {p : ℕ} (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hE : 6 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = eRootCount (compRank (componentRoots (rootCharHom a) i)))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)]))
    (hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ∃ lab : LargeEvenLabel, 2 ^ lab.n = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
      (lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8) ∧ RationalLabelIs S i lab := by
  have hchar : ringChar L = 2 := ringChar.eq L 2
  rcases hτ with rfl | rfl
  · exact recogE_to_label hchar hQS
      (recogT_ratCat_of_eClass (Or.inr (Or.inr (Or.inl rfl))) kacE7 facts_E7 e7_tree e7_adj
        e7_check e7_lt e7_card e7_ecount e7_etrees e7_elen (fun {F} _ x y h => e7_frames x y h)
        S hp hpL hT hTp i hE.1 hE.2 hinner)
  · exact recogE_to_label hchar hQS
      (recogT_ratCat_of_eClass (Or.inr (Or.inr (Or.inr rfl))) kacE8 facts_E8 e8_tree e8_adj
        e8_check e8_lt e8_card e8_ecount e8_etrees e8_elen (fun {F} _ x y h => e8_frames x y h)
        S hp hpL hT hTp i hE.1 hE.2 hinner)

theorem rationalLabel_outerE_E78
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {p : ℕ} (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hE : 6 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = eRootCount (compRank (componentRoots (rootCharHom a) i)))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)]))
    (hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ∃ lab : LargeEvenLabel, 2 ^ lab.n = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
      lab.tag = .twE6 ∧ RationalLabelIs S i lab := by
  have hchar : ringChar L = 2 := ringChar.eq L 2
  have hm : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
    S.componentOrbitLength_eq_one_of_five_leT hT i (by have := hE.1; omega)
  rcases hτ with rfl | rfl
  · obtain ⟨f, -, hq, hlie⟩ :=
      lieModel_rationalComponent_of_outer_E7 S hp hpL hT hTp i hE.1 hE.2 hout
    refine recogTwE6_to_label hchar hQS ⟨hQS.1.commutator_eq_top, f, hlie, ?_⟩
    rw [hm, pow_one]
    exact hq
  · obtain ⟨f, -, hq, hlie⟩ :=
      lieModel_rationalComponent_of_outer_E8 S hp hpL hT hTp i hE.1 hE.2 hout
    refine recogTwE6_to_label hchar hQS ⟨hQS.1.commutator_eq_top, f, hlie, ?_⟩
    rw [hm, pow_one]
    exact hq

end CertProofs

end CFSG.StandardType.TablePThreeKG

end

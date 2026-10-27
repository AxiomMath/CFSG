module

public import CFSG.LocalAnalysis.StandardType.GGExcCompSLDefs
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate1952
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13659
public import Certificates.Certificate13660
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc
import CFSG.LocalAnalysis.StandardType.GGCompFieldLieModel
import CFSG.RankThree.PartOne.KD4T.Certs
import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
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
import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
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

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE CFSG.Timmesfeld
  CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw
open scoped MatrixGroups Matrix

private def langRatFISL_Recog (p Q : ℕ) (C : Type) [Group C] : Prop :=
  commutator C = ⊤ ∧ ∃ (t : StatedLieTag) (n f : ℕ),
    LieModel (C ⧸ Subgroup.center C) t n p f ∧ p ^ f = Q ∧
      (t = .PSL ∨ t = .PSU ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨
      t = .twistedE6 ∨ t = .trialityD4)

private theorem langRatFISL_open_isQuasisimple {Q : Type} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.Open.IsQuasisimple Q :=
  ⟨Group.isPerfect_def.1 h.1, h.2.1⟩

private theorem langRatFISL_recog_of_range {p Q : ℕ} {X G : Type} [Group X] [Group G]
    (h : langRatFISL_Recog p Q X) (Ψ : X →* G) (hker : Ψ.ker ≤ Subgroup.center X)
    {H : Subgroup G} (hrange : Ψ.range = H) : langRatFISL_Recog p Q ↥H := by
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
  obtain ⟨t, n, f, hmodel, hpow, ht⟩ := h.2
  obtain ⟨e⟩ := nonempty_centralQuotient_mulEquiv h.1 g hg hgk
  exact ⟨commutator_eq_top_of_surjective_innerRecog h.1 g hg,
    ⟨t, n, f, LieModel.of_mulEquiv e hmodel, hpow, ht⟩⟩

private theorem langRatFISL_innerRecogOver_D {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {n : ℕ}
    (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 0 < f)
    (hK : Nat.card K = p ^ f) {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ)
    (hroot : ∀ b, IsRoot τ (β b)) (l : Fin n → ι)
    (hgram : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin n, edgeD n i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    langRatFISL_Recog p (p ^ f) ↥(rootSpan τ K (rootsOfFam β (Set.range l))) := by
  classical
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeD n) hgram hframe
  have hadm : StatedLieAdmissible .POmegaPlus n p f := ⟨hp, hf, hn⟩
  obtain ⟨-, -, -, hqs, -, hmodel⟩ := weakCT_spinPlus_of_frame hadm (by omega) hK U
    hgen hcomm hρ hψ
  exact ⟨hqs.1.commutator_eq_top,
    ⟨.POmegaPlus, n, f, hmodel, rfl, by decide⟩⟩

private theorem langRatFISL_innerRecogOver_E6 {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (hK : Nat.card K = p ^ f)
    {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ) (hroot : ∀ b, IsRoot τ (β b))
    (l : Fin 6 → ι)
    (hgram : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin 6, edgeE 6 i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    langRatFISL_Recog p (p ^ f) ↥(rootSpan τ K (rootsOfFam β (Set.range l))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeE 6) hgram hframe
  have hadm : StatedLieAdmissible .E6 0 p f := ⟨hp, hf, rfl⟩
  obtain ⟨-, -, -, hqs, -, hmodel⟩ := weakCT_e6_of_frame p f hadm hK U hgen hcomm hρ hψ
  exact ⟨hqs.1.commutator_eq_top, ⟨.E6, 0, f, hmodel, rfl, by decide⟩⟩

private theorem langRatFISL_innerRecogOver_E7 {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (hK : Nat.card K = p ^ f)
    {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ) (hroot : ∀ b, IsRoot τ (β b))
    (l : Fin 7 → ι)
    (hgram : ∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin 7, edgeE 7 i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    langRatFISL_Recog p (p ^ f) ↥(rootSpan τ K (rootsOfFam β (Set.range l))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeE 7) hgram hframe
  have hadm : StatedLieAdmissible .E7 0 p f := ⟨hp, hf, rfl⟩
  obtain ⟨-, -, -, hqs, -, hmodel⟩ := weakCT_e7_of_frame p f hadm hK U hgen hcomm hρ hψ
  exact ⟨hqs.1.commutator_eq_top, ⟨.E7, 0, f, hmodel, rfl, by decide⟩⟩

private theorem langRatFISL_innerRecogOver_E8 {τ : Tag}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (hK : Nat.card K = p ^ f)
    {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ) (hroot : ∀ b, IsRoot τ (β b))
    (l : Fin 8 → ι)
    (hgram : ∀ i j : Fin 8, i ≠ j → ¬ edgeE 8 i j → ¬ edgeE 8 j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin 8, edgeE 8 i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    langRatFISL_Recog p (p ^ f) ↥(rootSpan τ K (rootsOfFam β (Set.range l))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeE 8) hgram hframe
  have hadm : StatedLieAdmissible .E8 0 p f := ⟨hp, hf, rfl⟩
  obtain ⟨-, -, -, hqs, -, hmodel⟩ := weakCT_e8_of_frame p f hadm hK U hgen hcomm hρ hψ
  exact ⟨hqs.1.commutator_eq_top, ⟨.E8, 0, f, hmodel, rfl, by decide⟩⟩

private theorem langRatFISL_ratCat_of_innerRecogOver {τ : Tag} {L : Type}
    [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {ta : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ ta ∈ S.D.torus) (i : KernelComponent (rootCharHom ta))
    (hinner : twistInner (componentRoots (rootCharHom ta) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom ta) i)]))
    (hrec : ∀ K : Subfield L, Finite ↥K →
      Nat.card ↥K = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) →
      langRatFISL_Recog (ringChar L) (Nat.card ↥K)
        ↥(componentRootSpan K (rootCharHom ta) i)) :
    langRatFISL_Recog (ringChar L)
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i))
      ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) := by
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
  exact langRatFISL_recog_of_range hrecσ f hker hRf

private theorem langRatFISL_ratCat_of_tree {τ : Tag} (K : KacData τ) {L : Type}
    [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hTor : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (v : WeylGroup τ) {n : ℕ} (l : Fin n → Option (Fin τ.rank))
    (hroots : componentRoots (rootCharHom a) i = (fun α => v • α) '' K.rootsOf (Set.range l))
    (hrec : ∀ (K' : Type) [Field K'] [Finite K'] (p f : ℕ), p.Prime → 0 < f →
      Nat.card K' = p ^ f →
      langRatFISL_Recog p (p ^ f)
        ↥(rootSpan τ K' (rootsOfFam (fun x => v • K.extRoot x) (Set.range l)))) :
    langRatFISL_Recog (ringChar L)
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  refine langRatFISL_ratCat_of_innerRecogOver S hTor i hinner (fun K' hK' _ => ?_)
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

private theorem langRatFISL_ratCat_of_dClass {τ : Tag}
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
    langRatFISL_Recog (ringChar L)
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  obtain ⟨v, n, l, hn4, -, hroots, hnon, hE⟩ :=
    exists_tree_of_class K hK hT hadj hcheck hlt hcard edgeD 4 (fun n => 2 * n * (n - 1))
      hcount htrees (fun _ => True) (fun _ _ => trivial) S hp hpL hTp i h4 hn
  refine langRatFISL_ratCat_of_tree K S hTor i hinner v l hroots ?_
  intro K' _ _ p' f hp' hf hK'
  exact langRatFISL_innerRecogOver_D hτ hn4 hp' hf hK' (fun x => v • K.extRoot x)
    (fun b => IsRoot.smul (K.isRoot_extRoot b) v) l
    (fun c d hcd h1 h2 => by
      show iform (v • K.extRoot (l c)) (v • K.extRoot (l d)) = 0
      rw [iform_smul]
      exact hnon c d hcd h1 h2)
    (treeFrames K hframes v l (edgeD n) hE)

private theorem langRatFISL_ratCat_of_eClass {τ : Tag}
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
    langRatFISL_Recog (ringChar L)
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  obtain ⟨v, n, l, hn6, hQ, hroots, hnon, hE⟩ :=
    exists_tree_of_class K hK hT hadj hcheck hlt hcard edgeE 6 eRootCount hcount htrees
      (fun n => n = 6 ∨ n = 7 ∨ n = 8) hlen S hp hpL hTp i h6 hn
  refine langRatFISL_ratCat_of_tree K S hTor i hinner v l hroots ?_
  intro K' _ _ p' f hp' hf hK'
  have hgr : ∀ c d : Fin n, c ≠ d → ¬ edgeE n c d → ¬ edgeE n d c →
      iform ((fun x => v • K.extRoot x) (l c)) ((fun x => v • K.extRoot x) (l d)) = 0 := by
    intro c d hcd h1 h2
    show iform (v • K.extRoot (l c)) (v • K.extRoot (l d)) = 0
    rw [iform_smul]
    exact hnon c d hcd h1 h2
  have hfr := treeFrames K hframes v l (edgeE n) hE (F := K')
  have hroot : ∀ b, IsRoot τ ((fun x => v • K.extRoot x) b) :=
    fun b => IsRoot.smul (K.isRoot_extRoot b) v
  rcases hQ with rfl | rfl | rfl
  · exact langRatFISL_innerRecogOver_E6 hτ hp' hf hK' (fun x => v • K.extRoot x) hroot l hgr hfr
  · exact langRatFISL_innerRecogOver_E7 hτ hp' hf hK' (fun x => v • K.extRoot x) hroot l hgr hfr
  · exact langRatFISL_innerRecogOver_E8 hτ hp' hf hK' (fun x => v • K.extRoot x) hroot l hgr hfr

private theorem langRatFISL_inner_nonA_E6 {L : Type} [Field L] [IsAlgClosed L]
    {p₀ p : ℕ} (S : LangSetup Tag.E6 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E6.rank → Lˣ} (hTor : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E6 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    langRatFISL_Recog (ringChar L)
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
    exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S hp hpL hTp i
  have hshape := e6_shape c hc hlen
  rw [← hncard, ← hrank] at hshape
  rcases hshape with hA | hD | hE
  · exact (hnonA hA).elim
  · exact langRatFISL_ratCat_of_dClass (Or.inr (Or.inl rfl)) kacE6 facts_E6 e6_tree e6_adj
      e6_check e6_lt e6_card e6_dcount e6_dtrees (fun {F} _ x y h => e6_frames x y h) S hp hpL
      hTor hTp i hD.1 hD.2 hinner
  · exact langRatFISL_ratCat_of_eClass (Or.inr (Or.inl rfl)) kacE6 facts_E6 e6_tree e6_adj
      e6_check e6_lt e6_card e6_ecount e6_etrees e6_elen (fun {F} _ x y h => e6_frames x y h) S hp
      hpL hTor hTp i hE.1 hE.2 hinner

private theorem langRatFISL_inner_nonA_E7 {L : Type} [Field L] [IsAlgClosed L]
    {p₀ p : ℕ} (S : LangSetup Tag.E7 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E7.rank → Lˣ} (hTor : rootDiagUnit Tag.E7 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E7 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    langRatFISL_Recog (ringChar L)
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
    exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S hp hpL hTp i
  have hshape := e7_shape c hc hlen
  rw [← hncard, ← hrank] at hshape
  rcases hshape with hA | hD | hE
  · exact (hnonA hA).elim
  · exact langRatFISL_ratCat_of_dClass (Or.inr (Or.inr (Or.inl rfl))) kacE7 facts_E7 e7_tree e7_adj
      e7_check e7_lt e7_card e7_dcount e7_dtrees (fun {F} _ x y h => e7_frames x y h) S hp hpL
      hTor hTp i hD.1 hD.2 hinner
  · exact langRatFISL_ratCat_of_eClass (Or.inr (Or.inr (Or.inl rfl))) kacE7 facts_E7 e7_tree e7_adj
      e7_check e7_lt e7_card e7_ecount e7_etrees e7_elen (fun {F} _ x y h => e7_frames x y h) S hp
      hpL hTor hTp i hE.1 hE.2 hinner

private theorem langRatFISL_inner_nonA_E8 {L : Type} [Field L] [IsAlgClosed L]
    {p₀ p : ℕ} (S : LangSetup Tag.E8 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E8.rank → Lˣ} (hTor : rootDiagUnit Tag.E8 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E8 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    langRatFISL_Recog (ringChar L)
      (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
    exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S hp hpL hTp i
  have hshape := e8_shape c hc hlen
  rw [← hncard, ← hrank] at hshape
  rcases hshape with hA | hD | hE
  · exact (hnonA hA).elim
  · exact langRatFISL_ratCat_of_dClass (Or.inr (Or.inr (Or.inr rfl))) kacE8 facts_E8 e8_tree e8_adj
      e8_check e8_lt e8_card e8_dcount e8_dtrees (fun {F} _ x y h => e8_frames x y h) S hp hpL
      hTor hTp i hD.1 hD.2 hinner
  · exact langRatFISL_ratCat_of_eClass (Or.inr (Or.inr (Or.inr rfl))) kacE8 facts_E8 e8_tree e8_adj
      e8_check e8_lt e8_card e8_ecount e8_etrees e8_elen (fun {F} _ x y h => e8_frames x y h) S hp
      hpL hTor hTp i hE.1 hE.2 hinner

theorem langRatFieldSL_inner
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ j, a j ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hnA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hq : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    GGCompFieldAtSL (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  rcases hτ with rfl | rfl | rfl
  · have hstrong := langRatFISL_inner_nonA_E6 S hp hpL hT hTp i hnA hinner
    obtain ⟨t, n, f, hmodel, hpow, ht⟩ := hstrong.2
    have hchar : ringChar L = 2 := ringChar.eq L 2
    rw [hchar] at hmodel hpow
    rw [← hpow]
    exact ggCompFieldAtSL_of_lieModel (X := rationalComponent S.ρ S.Γ (rootCharHom a) i)
      (langRatFISL_open_isQuasisimple hq) hmodel ht
  · have hstrong := langRatFISL_inner_nonA_E7 S hp hpL hT hTp i hnA hinner
    obtain ⟨t, n, f, hmodel, hpow, ht⟩ := hstrong.2
    have hchar : ringChar L = 2 := ringChar.eq L 2
    rw [hchar] at hmodel hpow
    rw [← hpow]
    exact ggCompFieldAtSL_of_lieModel (X := rationalComponent S.ρ S.Γ (rootCharHom a) i)
      (langRatFISL_open_isQuasisimple hq) hmodel ht
  · have hstrong := langRatFISL_inner_nonA_E8 S hp hpL hT hTp i hnA hinner
    obtain ⟨t, n, f, hmodel, hpow, ht⟩ := hstrong.2
    have hchar : ringChar L = 2 := ringChar.eq L 2
    rw [hchar] at hmodel hpow
    rw [← hpow]
    exact ggCompFieldAtSL_of_lieModel (X := rationalComponent S.ρ S.Γ (rootCharHom a) i)
      (langRatFISL_open_isQuasisimple hq) hmodel ht

end CFSG.StandardType.LangRat

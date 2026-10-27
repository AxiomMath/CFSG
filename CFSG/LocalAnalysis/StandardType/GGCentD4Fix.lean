module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneInput
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentGraphShape
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentGraphPGU
public import CFSG.LocalAnalysis.StandardType.GGL45FixA2Comp
public import CFSG.LocalAnalysis.StandardType.GGL45FixA2Arith
public import CFSG.LocalAnalysis.StandardType.GGL45FixA2UniFix
public import CFSG.LocalAnalysis.StandardType.GGTriD4ComponentsPGLDer
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearProj
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityBridgeSecond
public import CFSG.RankThree.PartTwo.Sec21.LangTwisted3ProofD4Even
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.Goldschmidt.Steps.G310Comp
public import CFSG.Goldschmidt.Steps.G37QuotX
public import CFSG.Goldschmidt.Steps.G3aGlue
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4Outer
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.Cover
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.FamilyProved
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorDataCongr
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyFG
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.LieType.SeitzGeneration.Hyper
public import CFSG.LieType.SeitzGeneration.HyperBridge
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA3pSurvivor
public import CFSG.LocalAnalysis.AGLEmbedding.GapROneBS
public import CFSG.LocalAnalysis.AGLEmbedding.J3InSitu
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSide
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenAssembly
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3FourGenData
public import CFSG.LocalAnalysis.AGLEmbedding.MonomialWeightsOne
public import CFSG.LocalAnalysis.AGLEmbedding.ReeData
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Frontier3
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLTorus
public import CFSG.RankThree.PartOne.FOCD.G2OddQPlus
public import CFSG.RankThree.PartOne.FOCD.PRank
public import CFSG.RankThree.PartOne.KC.UnitaryDefining
public import CFSG.RankThree.PartOne.N143.LowTwoRankSplit
public import CFSG.RankThree.PartOne.N143.SectionCenter
public import CFSG.RankThree.PartOne.N143.SectionRankBound
public import CFSG.RankThree.PartOne.N143.SectionRankProof
public import CFSG.RankThree.PartOne.N143.SectionRankSplit
public import CFSG.RankThree.PartOne.SEITZ11.G2OddFinal
public import CFSG.RankThree.PartOne.SEITZ7.D4Wire
public import CFSG.RankThree.PartOne.SEITZ7.SzPairK
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofSec19
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofSec4
public import CFSG.RankThree.PartTwo.Sec4.E27.FixReeF4
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzOther
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzRest
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RowsProofSeitzSz

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.StandardType.Triality CFSG.RankThree.PartTwo.Sec8
open CFSG.RankThree.PartTwo
open CFSG.PGLModel (projImage)

@[expose] def NTPD4Labels {X : Type} [Group X] (q : ℕ) (Kc : Subgroup X) : Prop :=
  (q ≠ 2 → ∃ f : ℕ, 2 ^ f = q ∧
      (LieModel (↥Kc ⧸ Subgroup.center ↥Kc) .G2 0 2 f ∨
        LieModel (↥Kc ⧸ Subgroup.center ↥Kc) .PSL 3 2 f ∨
        LieModel (↥Kc ⧸ Subgroup.center ↥Kc) .PSU 3 2 f)) ∧
    (q = 2 → Nat.card Kc = 6048 ∧ Nat.card (↥Kc ⧸ Subgroup.center ↥Kc) = 6048)

private theorem d4f_ntpD4Labels_of_mulEquiv {X X' : Type} [Group X] [Group X']
    (q : ℕ) {Kc : Subgroup X} {Kc' : Subgroup X'} (e : ↥Kc ≃* ↥Kc')
    (h : NTPD4Labels q Kc') : NTPD4Labels q Kc := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hq => ?_, fun hq => ?_⟩
  · obtain ⟨f, hf, hmod⟩ := h1 hq
    have eq : (↥Kc ⧸ Subgroup.center ↥Kc) ≃*
        (↥Kc' ⧸ Subgroup.center ↥Kc') :=
      QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
    refine ⟨f, hf, ?_⟩
    rcases hmod with h | h | h
    · exact Or.inl (LieModel.of_mulEquiv eq.symm h)
    · exact Or.inr (Or.inl (LieModel.of_mulEquiv eq.symm h))
    · exact Or.inr (Or.inr (LieModel.of_mulEquiv eq.symm h))
  · obtain ⟨hc, hcc⟩ := h2 hq
    have eq : (↥Kc ⧸ Subgroup.center ↥Kc) ≃*
        (↥Kc' ⧸ Subgroup.center ↥Kc') :=
      QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
    exact ⟨(Nat.card_congr e.toEquiv).trans hc, (Nat.card_congr eq.toEquiv).trans hcc⟩

private theorem d4f_lieModel_g2_of_component
    {X : Type} [Group X] {C Q : Subgroup X} {k : Type} [Field k] [Finite k] {f₀ : ℕ}
    (hk : Nat.card k = 2 ^ f₀) (hf₀ : 2 ≤ f₀)
    (E : ↥C ≃* ↥(adjointGroup Tag.G2 k)) (hQ : IsComponentOf Q C) :
    LieModel (↥Q ⧸ Subgroup.center ↥Q) .G2 0 2 f₀ := by
  have hk3 : 3 ≤ Nat.card k := by
    rw [hk]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) hf₀
  have hperf :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.isPerfect_adjointGroup
      Tag.G2 k (fun _ => hk3)
  obtain ⟨hs, -⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.isSimpleGroup_adjointGroup_of_perfect
      Tag.G2 k hperf
  let T : ↥⁅C, C⁆ ≃* ↥(adjointGroup Tag.G2 k) :=
    (ggCommutatorEquiv C).trans
      ((ggCommutatorCongr E).trans
        ((MulEquiv.subgroupCongr hperf.commutator_eq_top).trans Subgroup.topEquiv))
  obtain ⟨Qe⟩ := gffa2_component_equiv T hs (CFSG.Assembly.isComponentOf_iff_open.2 hQ)
  have hraw := ggG2_rawDatum (n := f₀) hf₀ hk Qe
  have hlab : CFSG.Assembly.LargeEvenInLambda2
      (⟨.G2, 0, f₀⟩ : CFSG.Assembly.LargeEvenLabel) :=
    ⟨le_trans (by norm_num) hf₀, rfl, hf₀⟩
  obtain ⟨-, hmark⟩ := ggMarking_of_rawDatum (lab := ⟨.G2, 0, f₀⟩) hlab rfl hraw
  obtain ⟨lab, -, R, _, I, F, θ, -, -, hPeq, hm⟩ :=
    largeEvenMarking_exists_markedModel hmark
  subst hPeq
  have hmq : MarkedModel (⟨.G2, 0, f₀⟩ : CFSG.Assembly.LargeEvenLabel)
      (↥Q ⧸ Subgroup.center ↥Q) :=
    MarkedModel.of_mulEquiv θ.symm hm
  simpa only [MarkedModel, markTag, markRank, markChar, markDeg] using hmq

private theorem d4f_card_g2der_of_component
    {X : Type} [Group X] {C Q : Subgroup X} {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2)
    (E : ↥C ≃* ↥(adjointGroup Tag.G2 k)) (hQ : IsComponentOf Q C) :
    Nat.card Q = 6048 ∧ Nat.card (↥Q ⧸ Subgroup.center ↥Q) = 6048 := by
  obtain ⟨hDs, hDcard⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ExcCopy.g2Two_derived_exc hk
  let T : ↥⁅C, C⁆ ≃* ↥(commutator ↥(adjointGroup Tag.G2 k)) :=
    (ggCommutatorEquiv C).trans (ggCommutatorCongr E)
  obtain ⟨Qe⟩ := gffa2_component_equiv T hDs (CFSG.Assembly.isComponentOf_iff_open.2 hQ)
  have hraw := ggG2der_rawDatum (Y := ↥Q) hk
    (Qe.trans (ggCommutatorEquiv (adjointGroup Tag.G2 k)).symm)
  have hlab : CFSG.Assembly.LargeEvenInLambda2
      (⟨.G2der, 0, 1⟩ : CFSG.Assembly.LargeEvenLabel) := ⟨le_rfl, rfl, rfl⟩
  obtain ⟨hZ, -⟩ := ggMarking_of_rawDatum (lab := ⟨.G2der, 0, 1⟩) hlab rfl hraw
  have hcard : Nat.card ↥Q = 6048 := (Nat.card_congr Qe.toEquiv).trans hDcard
  refine ⟨hcard, ?_⟩
  have hqcard : Nat.card (↥Q ⧸ Subgroup.center ↥Q) = 6048 :=
    (Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientBot (G := ↥Q))).toEquiv).trans hcard
  simpa using hqcard

private theorem d4f_three_dvd_two_pow_sub_one {n : ℕ} (hn : Even n) : 3 ∣ 2 ^ n - 1 := by
  obtain ⟨k, rfl⟩ := hn
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hpow : 2 ^ (k + 1 + (k + 1)) = 4 * 2 ^ (k + k) := by
      rw [show k + 1 + (k + 1) = k + k + 2 by ring, pow_add]
      norm_num
      ring
    rw [hpow]
    obtain ⟨c, hc⟩ := ih
    have hge : 1 ≤ 2 ^ (k + k) := Nat.one_le_two_pow
    exact ⟨4 * c + 1, by omega⟩

private theorem d4f_lieModel_psl_of_component
    {X : Type} [Group X] {C Q : Subgroup X} {n : ℕ} (hn2 : 2 ≤ n)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ n)
    (E : ↥C ≃* ↥(projImage (Sec4.glPi true 3 (2 ^ n) F)))
    (hQ : IsComponentOf Q C) :
    LieModel (↥Q ⧸ Subgroup.center ↥Q) .PSL 3 2 n := by
  obtain ⟨E'⟩ := gffa2_commutator_equiv E
  obtain ⟨T₀⟩ := ggTriD4_pgl_derived_equiv hn2 hF
  let T : ↥⁅C, C⁆ ≃* CFSG.Assembly.LargeEvenProj
      (CFSG.Assembly.LargeEvenSLGroup (Fin 3) F) := E'.trans T₀
  have hs : IsSimpleGroup (CFSG.Assembly.LargeEvenProj
      (CFSG.Assembly.LargeEvenSLGroup (Fin 3) F)) :=
    LinearFieldFix.isSimpleGroup_proj (d := 3) (by norm_num) F
  have hnab : ∃ a b : CFSG.Assembly.LargeEvenProj
      (CFSG.Assembly.LargeEvenSLGroup (Fin 3) F), a * b ≠ b * a :=
    LinearFieldFix.exists_noncomm_proj (d := 3) (by norm_num) F
  obtain ⟨Qe⟩ := gffa2_component_equiv T hs (CFSG.Assembly.isComponentOf_iff_open.2 hQ)
  have hlab : CFSG.Assembly.LargeEvenInLambda2 (⟨.A, 2, n⟩ : CFSG.Assembly.LargeEvenLabel) :=
    ⟨le_trans (by norm_num) hn2, by norm_num, fun h => absurd h (by norm_num)⟩
  have hdatum : CFSG.Assembly.LargeEvenRawDatum (⟨.A, 2, n⟩ : CFSG.Assembly.LargeEvenLabel)
      fun R₀ _ _ _ => IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧
        Nonempty (↥Q ≃* R₀) := by
    dsimp only [CFSG.Assembly.LargeEvenRawDatum]
    exact ⟨F, inferInstance, inferInstance, hF, hs, hnab, ⟨Qe⟩⟩
  obtain ⟨-, hmark⟩ := ggMarking_of_rawDatum (lab := ⟨.A, 2, n⟩) hlab rfl hdatum
  obtain ⟨lab, -, R, _, I, F', θ, -, -, hPeq, hm⟩ := largeEvenMarking_exists_markedModel hmark
  subst hPeq
  have hmQ : MarkedModel (⟨.A, 2, n⟩ : CFSG.Assembly.LargeEvenLabel)
      (↥Q ⧸ Subgroup.center ↥Q) := MarkedModel.of_mulEquiv θ.symm hm
  simpa only [MarkedModel, markTag, markRank, markChar, markDeg] using hmQ

private theorem d4f_lieModel_psu_of_component
    {X : Type} [Group X] {C Q : Subgroup X} {n : ℕ} (hn2 : 2 ≤ n)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2)
    (E : ↥C ≃* ↥(projImage (Sec4.glPi false 3 (2 ^ n) F)))
    (hQ : IsComponentOf Q C) :
    LieModel (↥Q ⧸ Subgroup.center ↥Q) .PSU 3 2 n := by
  obtain ⟨E'⟩ := gffa2_commutator_equiv E
  obtain ⟨T₀⟩ := ggTriD4_pgu_derived_equiv hn2 hF
  let T : ↥⁅C, C⁆ ≃* CFSG.Assembly.LargeEvenProj
      (CFSG.Assembly.LargeEvenSUGroup (Fin 3) F (2 ^ n)) := E'.trans T₀
  obtain ⟨hs, hnab⟩ := gffa2_unitary_simple_nonab hn2 hF
  obtain ⟨Qe⟩ := gffa2_component_equiv T hs (CFSG.Assembly.isComponentOf_iff_open.2 hQ)
  have hlab : CFSG.Assembly.LargeEvenInLambda2 (⟨.twA, 2, n⟩ : CFSG.Assembly.LargeEvenLabel) :=
    ⟨le_trans (by norm_num) hn2, by norm_num, fun _ => hn2⟩
  have hdatum : CFSG.Assembly.LargeEvenRawDatum (⟨.twA, 2, n⟩ : CFSG.Assembly.LargeEvenLabel)
      fun R₀ _ _ _ => IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧
        Nonempty (↥Q ≃* R₀) := by
    dsimp only [CFSG.Assembly.LargeEvenRawDatum]
    exact ⟨F, inferInstance, inferInstance, hF, hs, hnab, ⟨Qe⟩⟩
  obtain ⟨-, hmark⟩ := ggMarking_of_rawDatum (lab := ⟨.twA, 2, n⟩) hlab rfl hdatum
  obtain ⟨lab, -, R, _, I, F', θ, -, -, hPeq, hm⟩ := largeEvenMarking_exists_markedModel hmark
  subst hPeq
  have hmQ : MarkedModel (⟨.twA, 2, n⟩ : CFSG.Assembly.LargeEvenLabel)
      (↥Q ⧸ Subgroup.center ↥Q) := MarkedModel.of_mulEquiv θ.symm hm
  simpa only [MarkedModel, markTag, markRank, markChar, markDeg] using hmQ

private theorem d4f_ntpD4Labels_of_lieModel {X : Type} [Group X] {f₀ : ℕ} (hf₀ : 2 ≤ f₀)
    {Kc : Subgroup X}
    (h : LieModel (↥Kc ⧸ Subgroup.center ↥Kc) .G2 0 2 f₀ ∨
         LieModel (↥Kc ⧸ Subgroup.center ↥Kc) .PSL 3 2 f₀ ∨
         LieModel (↥Kc ⧸ Subgroup.center ↥Kc) .PSU 3 2 f₀) :
    NTPD4Labels (2 ^ f₀) Kc := by
  refine ⟨fun _ => ⟨f₀, rfl, h⟩, fun hq => ?_⟩
  have h2 : 2 ^ 2 ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) hf₀
  rw [hq] at h2
  norm_num at h2

private theorem d4f_ntpD4Labels_of_card {X : Type} [Group X] {f₀ : ℕ} (hf₀ : f₀ = 1)
    {Kc : Subgroup X}
    (hcard : Nat.card Kc = 6048) (hcardq : Nat.card (↥Kc ⧸ Subgroup.center ↥Kc) = 6048) :
    NTPD4Labels (2 ^ f₀) Kc := by
  subst hf₀
  rw [pow_one]
  exact ⟨fun hq => (hq rfl).elim, fun _ => ⟨hcard, hcardq⟩⟩

private noncomputable def d4f_restrict_fixed_equiv
    {G : Type} [Group G]
    {X : Type} [Group X] {R : Subgroup X} {n : X}
    (hnR : ∀ r ∈ R, n * r * n⁻¹ ∈ R)
    (e : ↥R ≃* G)
    {β : MulAut G}
    (he : ∀ r : ↥R, e ⟨n * r * n⁻¹, hnR r r.2⟩ = β (e r)) :
    ↥((R ⊓ Subgroup.centralizer ({n} : Set X)).subgroupOf R) ≃* ↥(ggFix β) := by
  let M : Subgroup X := R ⊓ Subgroup.centralizer ({n} : Set X)
  let M' : Subgroup ↥R := M.subgroupOf R
  have hmap : M'.map e.toMonoidHom = ggFix β := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      rw [mem_ggFix]
      have hxM : x.1 ∈ M := (Subgroup.mem_subgroupOf).1 hx
      have hxR : x.1 ∈ R := (Subgroup.mem_inf.1 hxM).1
      have hxC : x.1 ∈ Subgroup.centralizer ({n} : Set X) := (Subgroup.mem_inf.1 hxM).2
      have hxn : x.1 * n = n * x.1 := by
        simpa using (Subgroup.mem_centralizer_singleton_iff.1 hxC)
      have hconj : n * x.1 * n⁻¹ = x.1 := by
        rw [← hxn]
        group
      rw [← hxy]
      change β (e x) = e x
      rw [← he x]
      exact congrArg e (Subtype.ext hconj)
    · intro hy
      rw [mem_ggFix] at hy
      obtain ⟨x, hx⟩ := e.surjective y
      have hxR : x.1 ∈ R := x.2
      have hxC : x.1 ∈ Subgroup.centralizer ({n} : Set X) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h := he x
        rw [hx] at h
        rw [hy] at h
        have h' : n * x.1 * n⁻¹ = x.1 := congrArg Subtype.val (e.injective (h.trans hx.symm))
        calc x.1 * n = (n * x.1 * n⁻¹) * n := by rw [h']
          _ = n * x.1 := by group
      have hxM : x.1 ∈ M := Subgroup.mem_inf.2 ⟨hxR, hxC⟩
      exact ⟨x, (Subgroup.mem_subgroupOf).2 hxM, hx⟩
  exact (Subgroup.equivMapOfInjective M' e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr hmap)

private noncomputable def d4f_restrict_fixed_equiv'
    {G : Type} [Group G]
    {X : Type} [Group X] {R : Subgroup X} {n : X}
    (hnR : ∀ r ∈ R, n * r * n⁻¹ ∈ R)
    (e : ↥R ≃* G)
    {β : MulAut G}
    (he : ∀ r : ↥R, e ⟨n * r * n⁻¹, hnR r r.2⟩ = β (e r)) :
    ↥(R ⊓ Subgroup.centralizer ({n} : Set X)) ≃* ↥(ggFix β) :=
  (Subgroup.subgroupOfEquivOfLe inf_le_left).symm.trans (d4f_restrict_fixed_equiv hnR e he)

private theorem d4f_ntpD4Labels_of_graphAut
    {F : Type} [Field F] [Finite F] [CharP F 2] {f₀ : ℕ}
    (hF : Nat.card F = 2 ^ f₀) (hf₀ : 1 ≤ f₀)
    {γ' : Om8 F} (hβ3' : (MulAut.conj γ' * theta : MulAut (Om8 F)) ^ 3 = 1)
    {Q : Subgroup ↥(ggFix (MulAut.conj γ' * theta : MulAut (Om8 F)))}
    (hQ : CFSG.Open.IsComponentOf Q ⊤) :
    NTPD4Labels (2 ^ f₀) Q := by
  rcases ggD4OddCent_graphClass γ' hβ3' with ⟨g, hg⟩ | hne
  ·
    have hθ : (theta : MulAut (Om8 F)) = theta * AutOm.fieldAutP 4 1 := by
      rw [map_one, mul_one]
    let eG2 : ↥(ggFix (theta : MulAut (Om8 F))) ≃* ↥(adjointGroup Tag.G2 F) :=
      ((MulEquiv.subgroupCongr (congrArg ggFix hθ)).trans (TriBridge.ggFixEquiv (K := F) 1)).trans
        (CFSG.RankThree.PartTwo.KFacts.d4FixedG2Equiv F (CharP.cast_eq_zero F 2))
    have hfixeq : ggFix (MulAut.conj γ' * theta : MulAut (Om8 F)) =
        (ggFix (theta : MulAut (Om8 F))).map (MulAut.conj g).toMonoidHom := by
      rw [hg, OrdPTriLayer.ggFix_mul_mul_inv]
    let E : ↥(ggFix (MulAut.conj γ' * theta : MulAut (Om8 F))) ≃*
        ↥(adjointGroup Tag.G2 F) :=
      (MulEquiv.subgroupCongr hfixeq).trans
        ((Subgroup.equivMapOfInjective (ggFix theta) (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective).symm.trans eG2)
    let E' : ↥(⊤ : Subgroup ↥(ggFix (MulAut.conj γ' * theta : MulAut (Om8 F)))) ≃*
        ↥(adjointGroup Tag.G2 F) := Subgroup.topEquiv.trans E
    by_cases hf1 : f₀ = 1
    · have hk2 : Nat.card F = 2 := by rw [hF, hf1]; norm_num
      obtain ⟨hc1, hc2⟩ := d4f_card_g2der_of_component hk2 E' hQ
      exact d4f_ntpD4Labels_of_card hf1 hc1 hc2
    · have hf2 : 2 ≤ f₀ := by omega
      exact d4f_ntpD4Labels_of_lieModel hf2
        (Or.inl (d4f_lieModel_g2_of_component hF hf2 E' hQ))
  ·
    obtain ⟨eGC⟩ := hne
    by_cases hodd : Odd f₀
    · by_cases hf1 : f₀ = 1
      · exfalso
        subst hf1
        obtain ⟨K, _, _, hK, ⟨ePU⟩⟩ := ggD4OddCent_secondCent_isoPGU hodd hF
        have hsolvK : Group.IsSolvable ↥(projImage (Sec4.glPi false 3 (2 ^ 1) K)) :=
          ggTriD4_pgu_two_solvable (n := 1) rfl hK
        have hsolvGC : Group.IsSolvable ↥(graphCentralizer TwistTag.D4.tag F
            (d4TrialityY0 F * (diagramMap TwistTag.D4 F)⁻¹)) := by
          haveI := hsolvK
          exact Group.isSolvable_of_isSolvable_injective (f := ePU.toMonoidHom)
            ePU.injective
        have hsolvQ : Group.IsSolvable
            ↥(ggFix (MulAut.conj γ' * theta : MulAut (Om8 F))) := by
          haveI := hsolvGC
          exact Group.isSolvable_of_isSolvable_injective (f := eGC.toMonoidHom) eGC.injective
        have hsolvTop : Group.IsSolvable
            ↥(⊤ : Subgroup ↥(ggFix (MulAut.conj γ' * theta : MulAut (Om8 F)))) := by
          haveI := hsolvQ
          exact Group.isSolvable_of_isSolvable_injective
            (f := Subgroup.topEquiv.toMonoidHom)
            (fun x y h => Subgroup.topEquiv.injective (by simpa using h))
        exact (gffa2_false_of_solvable hsolvTop
          (CFSG.Assembly.isComponentOf_iff_open.2 hQ)).elim
      · have hf3 : 3 ≤ f₀ := by obtain ⟨k, hk⟩ := hodd; omega
        have hf2 : 2 ≤ f₀ := by omega
        obtain ⟨K, _, _, hK, ⟨ePU⟩⟩ := ggD4OddCent_secondCent_isoPGU hodd hF
        let E : ↥(ggFix (MulAut.conj γ' * theta : MulAut (Om8 F))) ≃*
            ↥(projImage (Sec4.glPi false 3 (2 ^ f₀) K)) := eGC.trans ePU
        let E' : ↥(⊤ : Subgroup ↥(ggFix (MulAut.conj γ' * theta : MulAut (Om8 F)))) ≃*
            ↥(projImage (Sec4.glPi false 3 (2 ^ f₀) K)) := Subgroup.topEquiv.trans E
        exact d4f_ntpD4Labels_of_lieModel hf2
          (Or.inr (Or.inr (d4f_lieModel_psu_of_component hf2 hK E' hQ)))
    · have heven : Even f₀ := Nat.not_odd_iff_even.mp hodd
      have hf2 : 2 ≤ f₀ := by obtain ⟨k, hk⟩ := heven; omega
      have h3 : 3 ∣ Nat.card F - 1 := by
        rw [hF]
        exact d4f_three_dvd_two_pow_sub_one heven
      obtain ⟨ePGL⟩ := TriBridge.ggD4SecondCentPGLInput_holds F h3
      let E0 : ↥(projImage (Sec4.glPi true 3 (2 ^ f₀) F)) ≃*
          Matrix.ProjGenLinGroup (Fin 3) F :=
        (MulEquiv.subgroupCongr
          (LangTwisted3Proof.projImage_glPi_true_eq_top (2 ^ f₀) F)).trans Subgroup.topEquiv
      let E : ↥(ggFix (MulAut.conj γ' * theta : MulAut (Om8 F))) ≃*
          ↥(projImage (Sec4.glPi true 3 (2 ^ f₀) F)) := eGC.trans (ePGL.trans E0.symm)
      let E' : ↥(⊤ : Subgroup ↥(ggFix (MulAut.conj γ' * theta : MulAut (Om8 F)))) ≃*
          ↥(projImage (Sec4.glPi true 3 (2 ^ f₀) F)) := Subgroup.topEquiv.trans E
      exact d4f_ntpD4Labels_of_lieModel hf2
        (Or.inr (Or.inl (d4f_lieModel_psl_of_component hf2 hF E' hQ)))

theorem ntpD4_fix_untwisted
    {F : Type} [Field F] [Finite F] [CharP F 2] {f₀ : ℕ} (hF : Nat.card F = 2 ^ f₀) (hf₀ : 1 ≤ f₀)
    {X : Type} [Group X] (R : Subgroup X) (n : X) (hnR : ∀ r ∈ R, n * r * n⁻¹ ∈ R)
    (hn3 : n ^ 3 = 1) (e : ↥R ≃* Om8 F)
    (hγ : ∃ (γ : Om8 F) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧
      ∀ r : ↥R, e ⟨n * r * n⁻¹, hnR r r.2⟩ = (MulAut.conj γ * theta ^ ε : MulAut (Om8 F)) (e r))
    (Kc : Subgroup X) (hKc : IsComponentOf Kc (R ⊓ Subgroup.centralizer ({n} : Set X))) :
    NTPD4Labels (2 ^ f₀) Kc := by
  obtain ⟨γ, ε, hε, hβ⟩ := hγ
  have hnN : n ∈ Subgroup.normalizer R := by
    haveI : Finite (Om8 F) := inferInstance
    haveI : Finite ↥R := Finite.of_injective (e : ↥R → Om8 F) e.injective
    rw [Subgroup.mem_normalizer_iff]
    intro r
    refine ⟨fun hr => hnR r hr, fun hr => ?_⟩
    have hle : R.map (MulAut.conj n).toMonoidHom ≤ R := fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      exact hnR y hy
    have hcard : Nat.card (R.map (MulAut.conj n).toMonoidHom) = Nat.card R :=
      (Nat.card_congr (Subgroup.equivMapOfInjective R (MulAut.conj n).toMonoidHom
        (MulAut.conj n).injective).toEquiv).symm
    have heq : R.map (MulAut.conj n).toMonoidHom = R :=
      Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
    have hmem : n * r * n⁻¹ ∈ R.map (MulAut.conj n).toMonoidHom := by
      rw [heq]
      exact hr
    obtain ⟨s, hs, hsr⟩ := hmem
    have hsr' : n * s * n⁻¹ = n * r * n⁻¹ := hsr
    have hsr'' : s = r := by
      have h := congrArg (fun x => n⁻¹ * x * n) hsr'
      simpa [mul_assoc] using h
    rwa [← hsr'']
  let φ : MulAut ↥R := Subgroup.normalizerMonoidHom R ⟨n, hnN⟩
  have hφapply : ∀ r : ↥R, φ r = ⟨n * r * n⁻¹, hnR r r.2⟩ := fun r =>
    Subtype.ext (Subgroup.normalizerMonoidHom_apply_apply_coe R ⟨n, hnN⟩ r)
  have hcongr : MulAut.congr e φ = (MulAut.conj γ * theta ^ ε : MulAut (Om8 F)) := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨r, rfl⟩ := e.surjective y
    have hcr : (MulAut.congr e φ) (e r) = e (φ r) := by
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hcr, hφapply r]
    exact hβ r
  have hφ3 : φ ^ 3 = 1 := by
    change (Subgroup.normalizerMonoidHom R ⟨n, hnN⟩) ^ 3 = 1
    rw [← map_pow,
      show (⟨n, hnN⟩ : Subgroup.normalizer R) ^ 3 = 1 from Subtype.ext (by simpa using hn3),
      map_one]
  have hβ3 : (MulAut.conj γ * theta ^ ε : MulAut (Om8 F)) ^ 3 = 1 := by
    rw [← hcongr, ← map_pow, hφ3, map_one]
  let M : Subgroup X := R ⊓ Subgroup.centralizer ({n} : Set X)
  have hKcM : CFSG.Open.IsComponentOf (Kc.subgroupOf M) (⊤ : Subgroup ↥M) :=
    CFSG.Goldschmidt.G3a.isComponentOf_subgroupOf hKc
  have hMtop : ∀ {β : MulAut (Om8 F)} (eM : ↥M ≃* ↥(ggFix β)),
      (⊤ : Subgroup ↥M).map eM.toMonoidHom = ⊤ := by
    intro β eM
    rw [eq_top_iff]
    rintro y -
    obtain ⟨x, rfl⟩ := eM.surjective y
    exact ⟨x, Subgroup.mem_top x, rfl⟩
  rcases hε with rfl | hεneg
  ·
    have hβ3' : (MulAut.conj γ * theta : MulAut (Om8 F)) ^ 3 = 1 := by
      simpa using hβ3
    have hggFix : ggFix (MulAut.conj γ * theta ^ (1 : ℤ) : MulAut (Om8 F)) =
        ggFix (MulAut.conj γ * theta : MulAut (Om8 F)) := by rw [zpow_one]
    let eM : ↥M ≃* ↥(ggFix (MulAut.conj γ * theta : MulAut (Om8 F))) :=
      (d4f_restrict_fixed_equiv' hnR e hβ).trans (MulEquiv.subgroupCongr hggFix)
    have hQ : CFSG.Open.IsComponentOf ((Kc.subgroupOf M).map eM.toMonoidHom) ⊤ := by
      have h := CFSG.Goldschmidt.G310.isComponentOf_map_mulEquiv eM hKcM
      rwa [hMtop eM] at h
    have hNTP := d4f_ntpD4Labels_of_graphAut hF hf₀ hβ3' hQ
    exact d4f_ntpD4Labels_of_mulEquiv (2 ^ f₀)
      ((Subgroup.subgroupOfEquivOfLe hKc.1).symm.trans
        (Subgroup.equivMapOfInjective (Kc.subgroupOf M) eM.toMonoidHom eM.injective)) hNTP
  ·
    subst hεneg
    have hconj_mul : ∀ (a : Om8 F) (f : MulAut (Om8 F)),
        MulAut.conj (f a) * f = f * MulAut.conj a := by
      intro a f
      refine MulEquiv.ext fun x => ?_
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
    have h1 : (MulAut.conj (theta γ⁻¹) * theta : MulAut (Om8 F)) =
        theta * MulAut.conj γ⁻¹ := hconj_mul γ⁻¹ theta
    have h2 : (MulAut.conj γ * theta ^ (-1 : ℤ) : MulAut (Om8 F))⁻¹ =
        theta * MulAut.conj γ⁻¹ := by
      rw [zpow_neg, zpow_one, mul_inv_rev, inv_inv, ← map_inv (MulAut.conj) γ]
    have hβ' : (MulAut.conj (theta γ⁻¹) * theta : MulAut (Om8 F)) =
        (MulAut.conj γ * theta ^ (-1 : ℤ) : MulAut (Om8 F))⁻¹ := h1.trans h2.symm
    have hβ3' : (MulAut.conj (theta γ⁻¹) * theta : MulAut (Om8 F)) ^ 3 = 1 := by
      rw [hβ', inv_pow, hβ3, inv_one]
    have hggFix : ggFix (MulAut.conj γ * theta ^ (-1 : ℤ) : MulAut (Om8 F)) =
        ggFix (MulAut.conj (theta γ⁻¹) * theta : MulAut (Om8 F)) := by
      rw [← OrdPTriLayer.ggFix_inv (MulAut.conj γ * theta ^ (-1 : ℤ) : MulAut (Om8 F)),
        hβ'.symm]
    let eM : ↥M ≃* ↥(ggFix (MulAut.conj (theta γ⁻¹) * theta : MulAut (Om8 F))) :=
      (d4f_restrict_fixed_equiv' hnR e hβ).trans (MulEquiv.subgroupCongr hggFix)
    have hQ : CFSG.Open.IsComponentOf ((Kc.subgroupOf M).map eM.toMonoidHom) ⊤ := by
      have h := CFSG.Goldschmidt.G310.isComponentOf_map_mulEquiv eM hKcM
      rwa [hMtop eM] at h
    have hNTP := d4f_ntpD4Labels_of_graphAut hF hf₀ hβ3' hQ
    exact d4f_ntpD4Labels_of_mulEquiv (2 ^ f₀)
      ((Subgroup.subgroupOfEquivOfLe hKc.1).symm.trans
        (Subgroup.equivMapOfInjective (Kc.subgroupOf M) eM.toMonoidHom eM.injective)) hNTP

private theorem d4f_isComponentProperty_P {f₀ : ℕ} :
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.IsComponentProperty
      (fun X _ => NTPD4Labels (2 ^ f₀) (⊤ : Subgroup X)) where
  of_mulEquiv := by
    intro X Y _ _ e h
    exact d4f_ntpD4Labels_of_mulEquiv (2 ^ f₀)
      (Subgroup.topEquiv.trans (e.symm.trans Subgroup.topEquiv.symm)) h

private theorem d4f_compsWith_P_adjointG2
    {f₀ : ℕ} (hf₀ : 1 ≤ f₀)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ f₀) :
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsWith
      (fun X _ => NTPD4Labels (2 ^ f₀) (⊤ : Subgroup X)) ↥(adjointGroup Tag.G2 F) := by
  intro K hK
  by_cases hf1 : f₀ = 1
  · have hk2 : Nat.card F = 2 := by rw [hF, hf1]; norm_num
    obtain ⟨hc1, hc2⟩ := d4f_card_g2der_of_component hk2 Subgroup.topEquiv hK
    exact d4f_ntpD4Labels_of_mulEquiv (2 ^ f₀) Subgroup.topEquiv
      (d4f_ntpD4Labels_of_card hf1 hc1 hc2)
  · have hf2 : 2 ≤ f₀ := by omega
    have hmod : LieModel (↥K ⧸ Subgroup.center ↥K) .G2 0 2 f₀ :=
      d4f_lieModel_g2_of_component hF hf2
        (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥(adjointGroup Tag.G2 F)) ≃*
          ↥(adjointGroup Tag.G2 F)) hK
    exact d4f_ntpD4Labels_of_mulEquiv (2 ^ f₀)
      (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥K) ≃* ↥K)
      (d4f_ntpD4Labels_of_lieModel hf2 (Or.inl hmod))

private theorem d4f_compsWith_P_projImage
    {f₀ : ℕ} (hf₀ : 1 ≤ f₀)
    {F : Type} [Field F] [Finite F] (π : Bool) (hπ : π = true → 2 < 2 ^ f₀)
    (hF : Nat.card F = Sec4.piCard π (2 ^ f₀)) :
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsWith
      (fun X _ => NTPD4Labels (2 ^ f₀) (⊤ : Subgroup X))
      ↥(projImage (Sec4.glPi π 3 (2 ^ f₀) F)) := by
  intro K hK
  by_cases hf1 : f₀ = 1
  · have hπfalse : π = false := by
      cases π with
      | false => rfl
      | true => exact absurd (hπ rfl) (by rw [hf1]; norm_num)
    subst hπfalse
    subst hf1
    have hF' : Nat.card F = (2 ^ 1) ^ 2 := by simpa [Sec4.piCard] using hF
    have hsolv : Group.IsSolvable ↥(projImage (Sec4.glPi false 3 (2 ^ 1) F)) :=
      ggTriD4_pgu_two_solvable (n := 1) rfl hF'
    have hsolvTop : Group.IsSolvable
        ↥(⊤ : Subgroup ↥(projImage (Sec4.glPi false 3 (2 ^ 1) F))) := by
      haveI := hsolv
      exact Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.topEquiv.toMonoidHom)
        (fun x y h => Subgroup.topEquiv.injective (by simpa using h))
    have hK' : CFSG.Assembly.IsComponentOf K
        (⊤ : Subgroup ↥(projImage (Sec4.glPi false 3 (2 ^ 1) F))) :=
      CFSG.Assembly.isComponentOf_iff_open.2 hK
    exact (gffa2_false_of_solvable
      (X := ↥(projImage (Sec4.glPi false 3 (2 ^ 1) F))) hsolvTop hK').elim
  · have hf2 : 2 ≤ f₀ := by omega
    cases π with
    | false =>
      have hF' : Nat.card F = (2 ^ f₀) ^ 2 := by simpa [Sec4.piCard] using hF
      have hmod := d4f_lieModel_psu_of_component hf2 hF' Subgroup.topEquiv hK
      exact d4f_ntpD4Labels_of_mulEquiv (2 ^ f₀) Subgroup.topEquiv
        (d4f_ntpD4Labels_of_lieModel hf2 (Or.inr (Or.inr hmod)))
    | true =>
      have hF' : Nat.card F = 2 ^ f₀ := by simpa [Sec4.piCard] using hF
      have hmod := d4f_lieModel_psl_of_component hf2 hF' Subgroup.topEquiv hK
      exact d4f_ntpD4Labels_of_mulEquiv (2 ^ f₀) Subgroup.topEquiv
        (d4f_ntpD4Labels_of_lieModel hf2 (Or.inr (Or.inl hmod)))

theorem ntpD4_fix_triality
    {f₀ : ℕ} (hf₀ : 1 ≤ f₀) {K₃ : Type} [Field K₃] [Finite K₃]
    (hK₃ : Nat.card K₃ = (2 ^ f₀) ^ 3) (Fr : K₃ ≃+* K₃) (hFr : ∀ c, Fr c = c ^ (2 ^ f₀))
    {X : Type} [Group X] (R : Subgroup X) (n : X) (hnR : ∀ r ∈ R, n * r * n⁻¹ ∈ R)
    (hn3 : n ^ 3 = 1)
    (e : ↥R ≃* ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom))
    (hout : ¬ ∃ r₀ : ↥R, ∀ r : ↥R, (⟨n * r * n⁻¹, hnR r r.2⟩ : ↥R) = r₀ * r * r₀⁻¹)
    (Kc : Subgroup X) (hKc : IsComponentOf Kc (R ⊓ Subgroup.centralizer ({n} : Set X))) :
    NTPD4Labels (2 ^ f₀) Kc := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnN : n ∈ Subgroup.normalizer R := by
    haveI : Finite (↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)) := inferInstance
    haveI : Finite ↥R :=
      Finite.of_injective (e : ↥R → ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom))
        e.injective
    rw [Subgroup.mem_normalizer_iff]
    intro r
    refine ⟨fun hr => hnR r hr, fun hr => ?_⟩
    have hle : R.map (MulAut.conj n).toMonoidHom ≤ R := fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      exact hnR y hy
    have hcard : Nat.card (R.map (MulAut.conj n).toMonoidHom) = Nat.card R :=
      (Nat.card_congr (Subgroup.equivMapOfInjective R (MulAut.conj n).toMonoidHom
        (MulAut.conj n).injective).toEquiv).symm
    have heq : R.map (MulAut.conj n).toMonoidHom = R :=
      Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
    have hmem : n * r * n⁻¹ ∈ R.map (MulAut.conj n).toMonoidHom := by
      rw [heq]
      exact hr
    obtain ⟨s, hs, hsr⟩ := hmem
    have hsr' : n * s * n⁻¹ = n * r * n⁻¹ := hsr
    have hsr'' : s = r := by
      have h := congrArg (fun x => n⁻¹ * x * n) hsr'
      simpa [mul_assoc] using h
    rwa [← hsr'']
  let ψ : MulAut ↥R := Subgroup.normalizerMonoidHom R ⟨n, hnN⟩
  have hψapply : ∀ r : ↥R, ψ r = ⟨n * r * n⁻¹, hnR r r.2⟩ := fun r =>
    Subtype.ext (Subgroup.normalizerMonoidHom_apply_apply_coe R ⟨n, hnN⟩ r)
  have hψ3 : ψ ^ 3 = 1 := by
    change (Subgroup.normalizerMonoidHom R ⟨n, hnN⟩) ^ 3 = 1
    rw [← map_pow,
      show (⟨n, hnN⟩ : Subgroup.normalizer R) ^ 3 = 1 from Subtype.ext (by simpa using hn3),
      map_one]
  let φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) := MulAut.congr e ψ
  have hφ3 : φ ^ 3 = 1 := by
    change (MulAut.congr e ψ) ^ 3 = 1
    rw [← map_pow, hψ3, map_one]
  have hφ : φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range := by
    intro hmem
    obtain ⟨g, hg⟩ := hmem
    apply hout
    refine ⟨e.symm g, fun r => ?_⟩
    apply e.injective
    rw [← hψapply r, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    change e (ψ r) = (MulAut.conj g) (e r)
    rw [hg]
    change e (ψ r) = e (ψ (e.symm (e r)))
    rw [MulEquiv.symm_apply_apply]
  have he : ∀ r : ↥R, e ⟨n * r * n⁻¹, hnR r r.2⟩ = φ (e r) := by
    intro r
    have h1 : e ⟨n * r * n⁻¹, hnR r r.2⟩ = e (ψ r) := by rw [hψapply r]
    rw [h1]
    change e (ψ r) = e (ψ (e.symm (e r)))
    rw [MulEquiv.symm_apply_apply]
  let M : Subgroup X := R ⊓ Subgroup.centralizer ({n} : Set X)
  have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup φ = ggFix φ :=
    Subgroup.ext fun _ => Iff.rfl
  let eM : ↥M ≃* ↥(CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup φ) :=
    (d4f_restrict_fixed_equiv' hnR e he).trans (MulEquiv.subgroupCongr hfix.symm)
  have hKcM : CFSG.Open.IsComponentOf (Kc.subgroupOf M) (⊤ : Subgroup ↥M) :=
    CFSG.Goldschmidt.G3a.isComponentOf_subgroupOf hKc
  have hMtop : (⊤ : Subgroup ↥M).map eM.toMonoidHom = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨x, rfl⟩ := eM.surjective y
    exact ⟨x, Subgroup.mem_top x, rfl⟩
  have hQ : CFSG.Open.IsComponentOf ((Kc.subgroupOf M).map eM.toMonoidHom) ⊤ := by
    have h := CFSG.Goldschmidt.G310.isComponentOf_map_mulEquiv eM hKcM
    rwa [hMtop] at h
  have hcomps : CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsWith
      (fun X _ => NTPD4Labels (2 ^ f₀) (⊤ : Subgroup X))
      ↥(CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup φ) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.compsWith_triality_outer
      d4f_isComponentProperty_P (ℓ := 2) (f := f₀)
      (by intro h; exact False.elim (absurd h (by norm_num)))
      (fun {F} _ _ hF => d4f_compsWith_P_adjointG2 hf₀ hF)
      (fun {F} _ _ π hπ hF => d4f_compsWith_P_projImage hf₀ π hπ hF)
      (by norm_num) hf₀ hK₃ Fr hFr φ hφ3 hφ
  have hNTP : NTPD4Labels (2 ^ f₀) ((Kc.subgroupOf M).map eM.toMonoidHom) :=
    d4f_ntpD4Labels_of_mulEquiv (2 ^ f₀) Subgroup.topEquiv.symm (hcomps _ hQ)
  exact d4f_ntpD4Labels_of_mulEquiv (2 ^ f₀)
    ((Subgroup.subgroupOfEquivOfLe hKc.1).symm.trans
      (Subgroup.equivMapOfInjective (Kc.subgroupOf M) eM.toMonoidHom eM.injective)) hNTP

end CFSG.StandardType.NTPlane

end

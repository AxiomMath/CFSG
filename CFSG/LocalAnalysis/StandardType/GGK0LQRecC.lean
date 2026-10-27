module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPF4B2Two
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactSp
public import CFSG.HardMathSupport.Dickson.Bal207.FamF42Levi
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLeviToral
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusFrame
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.Seitz.Defs
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Inputs
public import CFSG.Monster.GMS.Fi23Gen
public import CFSG.Monster.GMS.Fi23GenIso
public import CFSG.Monster.GMS.Fi23GenSix
public import CFSG.Monster.GMS.LeechCoh
public import CFSG.Monster.GMS.LeechCohGroup
public import CFSG.Monster.GMS.S365Center
public import CFSG.Monster.GMS.S37
public import CFSG.Monster.GMS.S4Assembly
public import CFSG.Monster.GMS.S4CohB
public import CFSG.Monster.GMS.S5Inputs
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartTwo.Sec8.Item87Proof84
public import CFSG.Sporadic.Co1.Module.Co2Stab
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.M24
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import Certificates.Certificate10050
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate16005
public import Certificates.Certificate16041
public import Certificates.Certificate17002
public import Certificates.Certificate17951
public import Certificates.Certificate2098
public import Certificates.Certificate2103
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate2139
public import Certificates.Certificate2140
public import Certificates.Certificate2323
public import Certificates.Certificate3044
public import Certificates.Certificate3122
public import Certificates.Certificate3123
public import Certificates.Certificate3130
public import Certificates.Certificate3133
public import Certificates.Certificate3134
public import Certificates.Certificate3136
public import Certificates.Certificate3137
public import Certificates.Certificate3176
public import Certificates.Certificate3179
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8117
public import Certificates.Certificate9124

public section

namespace CFSG.StandardType.GGK0LQ

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.ComponentClassification.CatLeafProof
  CFSG.HardMathSupport.Dickson.Bal207.FamF42
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSExactSp

private theorem lqRecC_cover_levi
    {J : Set (Fin (Tag.rank .F4))} (hJ : J = f4LeviB3 ∨ J = f4LeviC3)
    {K : Type} [Field K] [Finite K] [CharP K 2] {N : ℕ} (hN : 0 < N)
    (hK : Nat.card K = 2 ^ N) :
    ∃ Ψ : StatedSp 3 K →* ModGL Tag.F4 K, Ψ.ker ≤ Subgroup.center (StatedSp 3 K) ∧
      Ψ.range = subsystemGroup .F4 K J := by
  rcases hJ with rfl | rfl
  · by_cases hK4 : 4 ≤ Nat.card K
    · exact exists_sp3_cover_f4_B3_even hN hK hK4
    · exact exists_sp3Hom_f4_B3_two (CompsPF4Small.card_eq_two_of_lt_four hN hK hK4)
  · exact exists_sp3Hom_f4_C3 Nat.prime_two hN hK

private theorem lqRecC_spRange_smul
    {K : Type} [Field K] (v : WeylGroup Tag.F4) {J : Set (Fin (Tag.rank .F4))}
    {Ψ : StatedSp 3 K →* ModGL Tag.F4 K}
    (hker : Ψ.ker ≤ Subgroup.center (StatedSp 3 K))
    (hrange : Ψ.range = subsystemGroup .F4 K J) :
    ∃ Ψ' : StatedSp 3 K →* ModGL Tag.F4 K, Ψ'.ker ≤ Subgroup.center (StatedSp 3 K) ∧
      Ψ'.range = rootSpan Tag.F4 K ((fun α => v • α) '' parabolicRoots Tag.F4 J) := by
  refine ⟨(MulAut.conj (canonicalRep (coxeterSystem Tag.F4) K v)).toMonoidHom.comp Ψ,
    fun x hx => hker ?_, ?_⟩
  · rw [MonoidHom.mem_ker] at hx ⊢
    exact (MulAut.conj (canonicalRep (coxeterSystem Tag.F4) K v)).injective
      (hx.trans (map_one _).symm)
  · have hsub : subsystemGroup Tag.F4 K J = rootSpan Tag.F4 K (parabolicRoots Tag.F4 J) :=
      CFSG.RankThree.Chevalley.subsystemGroup_eq_iSup_rootSubgroup (τ := Tag.F4) (J := J) K
    rw [MonoidHom.range_comp, hrange, hsub]
    exact (canonical_weyl_root_transport Tag.F4 K).1 v (parabolicRoots Tag.F4 J)
      (fun α hα => hα.1)

private theorem lqRecC_surj_of_cover
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {σ : L ≃+* L}
    {f : ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) →* ModGL Tag.F4 L}
    (hf1 : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ f.range)
    (hker : f.ker ≤ Subgroup.center ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i))
    (hf2 : ⁅componentRootSpan (fixSubfield σ) (rootCharHom a) i,
        componentRootSpan (fixSubfield σ) (rootCharHom a) i⁆ =
        componentRootSpan (fixSubfield σ) (rootCharHom a) i →
      f.range ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i)
    {Ψ : StatedSp 3 ↥(fixSubfield σ) →* ModGL Tag.F4 ↥(fixSubfield σ)}
    (hΨk : Ψ.ker ≤ Subgroup.center (StatedSp 3 ↥(fixSubfield σ)))
    (hΨr : Ψ.range = componentRootSpan (fixSubfield σ) (rootCharHom a) i)
    (hperfSp : commutator (StatedSp 3 ↥(fixSubfield σ)) = ⊤) :
    ∃ g : StatedSp 3 ↥(fixSubfield σ) →* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i),
      Function.Surjective g ∧ g.ker ≤ Subgroup.center (StatedSp 3 ↥(fixSubfield σ)) := by
  classical
  have hCperf : ⁅componentRootSpan (fixSubfield σ) (rootCharHom a) i,
      componentRootSpan (fixSubfield σ) (rootCharHom a) i⁆ =
      componentRootSpan (fixSubfield σ) (rootCharHom a) i := by
    rw [← hΨr, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hperfSp]
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    le_antisymm (hf2 hCperf) hf1
  let g0 : StatedSp 3 ↥(fixSubfield σ) →*
      ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) :=
    Ψ.codRestrict _ (fun x => by rw [← hΨr]; exact ⟨x, rfl⟩)
  have hg0surj : Function.Surjective g0 := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ : y ∈ Ψ.range := hΨr ▸ hy
    exact ⟨x, Subtype.ext hx⟩
  have hg0ker : g0.ker ≤ Subgroup.center (StatedSp 3 ↥(fixSubfield σ)) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    exact hΨk (by rw [MonoidHom.mem_ker]; exact congrArg Subtype.val hx)
  let g : StatedSp 3 ↥(fixSubfield σ) →*
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (f.comp g0).codRestrict _ (fun x => by rw [← hRf]; exact ⟨g0 x, rfl⟩)
  have hgsurj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨c, hc⟩ : y ∈ f.range := hRf ▸ hy
    obtain ⟨x, rfl⟩ := hg0surj c
    exact ⟨x, Subtype.ext hc⟩
  have hgker : g.ker ≤ Subgroup.center (StatedSp 3 ↥(fixSubfield σ)) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : f (g0 x) = 1 := congrArg Subtype.val hx
    have h2 : g0 x ∈ Subgroup.center
        ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) := hker h1
    rw [← comap_center_of_surjective hperfSp g0 hg0surj hg0ker]
    exact h2
  exact ⟨g, hgsurj, hgker⟩

private theorem lqRecC_model_of_surj
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {σ : L ≃+* L}
    (hfin : Finite ↥(fixSubfield σ)) {N : ℕ} (hKcard : Nat.card ↥(fixSubfield σ) = 2 ^ N)
    {g : StatedSp 3 ↥(fixSubfield σ) →* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)}
    (hg : Function.Surjective g) (hgk : g.ker ≤ Subgroup.center (StatedSp 3 ↥(fixSubfield σ)))
    (hperfSp : commutator (StatedSp 3 ↥(fixSubfield σ)) = ⊤) :
    StatedClassicalModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .PSp 3 2 N := by
  haveI : Finite ↥(fixSubfield σ) := hfin
  haveI : Fintype ↥(fixSubfield σ) := Fintype.ofFinite ↥(fixSubfield σ)
  have hNpos : 0 < N := by
    by_contra h
    rw [Nat.eq_zero_of_not_pos h, pow_zero] at hKcard
    have h2 := Finite.one_lt_card (α := ↥(fixSubfield σ))
    rw [hKcard] at h2
    omega
  obtain ⟨e1⟩ := nonempty_centralQuotient_mulEquiv hperfSp g hg hgk
  let e2 := QuotientGroup.quotientMulEquivOfEq
    (CFSG.LieType.Universal.Symplectic.center_eq 3 ↥(fixSubfield σ))
  exact ⟨⟨Nat.prime_two, hNpos, by norm_num, by simp⟩, ↥(fixSubfield σ), inferInstance,
    inferInstance, hKcard, ⟨e1.symm.trans e2⟩⟩

private theorem lqRecC_hasLabel_of_model {X : Type} [Group X] {n N : ℕ}
    (h : CFSG.Open.StatedClassicalModel X .PSp n 2 N) : GGHasLabel ⟨.C, n, N⟩ X := by
  obtain ⟨-, K, hF, hfin, hcard, ⟨e⟩⟩ := h
  exact ⟨K, hF, hfin, hcard, ⟨e⟩⟩

theorem lq_rec_C
    {τ : Tag} (hτ : τ = .F4)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (h3 : compRank (componentRoots (rootCharHom a) i) = 3)
    (hn : (componentRoots (rootCharHom a) i).ncard = 18)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    {N : ℕ} (hN : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ^ N) :
    GGHasLabel ⟨.C, compRank (componentRoots (rootCharHom a) i), N⟩
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  subst hτ
  classical
  have hp2 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exfalso
      apply hpL
      rw [h]
      exact CharP.cast_eq_zero L 2
    · exact h
  have hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)) := by
    rintro ⟨-, h⟩
    rw [h3, hn] at h
    norm_num at h
  rcases f4_nonA_casesP2 hp hp2 S hpL hTp h1 i hnonA with
    ⟨v, _, hr, _⟩ | ⟨v, J, hJ, hroots, _, _⟩
  · omega
  · obtain ⟨σ, hfin, hcard, f, hf1, hker, hf2⟩ := exists_inner_cover S hT i hinner
    haveI : Finite ↥(fixSubfield σ) := hfin
    haveI : Fintype ↥(fixSubfield σ) := Fintype.ofFinite ↥(fixSubfield σ)
    haveI : CharP ↥(fixSubfield σ) 2 :=
      ((fixSubfield σ).subtype.charP_iff (fixSubfield σ).subtype_injective 2).2 inferInstance
    have hKcard : Nat.card ↥(fixSubfield σ) = 2 ^ N := by rw [hcard, hN]
    have hNpos : 0 < N := by
      by_contra h
      rw [Nat.eq_zero_of_not_pos h, pow_zero] at hKcard
      have h2 := Finite.one_lt_card (α := ↥(fixSubfield σ))
      rw [hKcard] at h2
      omega
    have hperfSp : commutator (StatedSp 3 ↥(fixSubfield σ)) = ⊤ :=
      (spFactorFacts_holds ↥(fixSubfield σ) 3 (by norm_num)
        (by simp [← Nat.card_eq_fintype_card, hKcard])).perfect
    obtain ⟨Ψ0, hk0, hr0⟩ := lqRecC_cover_levi hJ hNpos hKcard
    obtain ⟨Ψ, hΨk, hΨr0⟩ := lqRecC_spRange_smul v hk0 hr0
    have hcomp : componentRootSpan (fixSubfield σ) (rootCharHom a) i =
        rootSpan Tag.F4 ↥(fixSubfield σ) ((fun α => v • α) '' parabolicRoots Tag.F4 J) := by
      show rootSpan Tag.F4 ↥(fixSubfield σ) (componentRoots (rootCharHom a) i) = _
      rw [hroots]
    rw [← hcomp] at hΨr0
    obtain ⟨g, hg, hgk⟩ := lqRecC_surj_of_cover (f := f) S i hf1 hker hf2 hΨk hΨr0 hperfSp
    rw [h3]
    exact lqRecC_hasLabel_of_model (lqRecC_model_of_surj S i hfin hKcard hg hgk hperfSp)

end CFSG.StandardType.GGK0LQ

end

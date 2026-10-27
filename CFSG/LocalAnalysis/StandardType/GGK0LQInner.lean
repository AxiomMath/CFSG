module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame.SmallField
import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.Foundations
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate1952
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcField
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSplit
import CFSG.HardMathSupport.Timmesfeld.LangTorus.Assembly
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
import CFSG.LieType.AlgebraicGroups.ConnectedToralLang
import CFSG.LieType.Chevalley.OrdinaryRootCentralizerGeneration

public section

namespace CFSG.StandardType.GGK0LQ

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open scoped commutatorElement

private theorem lk0xlqinner_smallFieldInner_not_rank_one
    {τ : Tag} {K : Type} [Field K] [Finite K]
    {M : Type} [CommGroup M] (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ)
    {p : ℕ} (hp : p.Prime) (hp5 : τ = .G2 → 5 ≤ p)
    (hχp : ∀ γ, IsRoot τ γ → χ (Multiplicative.ofAdd γ) ^ p = 1)
    (hχ1 : ∃ γ, IsRoot τ γ ∧ χ (Multiplicative.ofAdd γ) ≠ 1) (hK : Nat.card K ≤ 3)
    (hbig : ∃ α ∈ componentRoots χ i, ∃ δ ∈ componentRoots χ i, δ ≠ α ∧ δ ≠ -α) :
    CFSG.IsQuasisimple ↥(⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ :
        Subgroup (ModGL τ K)) ∧
      (Nat.card K = 2 ∨
        ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ = componentRootSpan K χ i) := by
  classical
  haveI := Fintype.ofFinite K
  have hcard2 : 2 ≤ Nat.card K := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  have hτ : ∀ τ : Tag, τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    intro τ; cases τ <;> simp
  rcases hτ τ with rfl | rfl | h | h | h | h
  · exfalso
    obtain ⟨α, hα, δ, hδ, h1, h2⟩ := hbig
    rcases g2_component_rank_one χ hp (hp5 rfl) hχp hχ1 i α hα δ hδ with h | h
    · exact h1 h
    · exact h2 h
  ·
    have hK23 : Nat.card K = 2 ∨ Nat.card K = 3 := by omega
    rcases hK23 with hc | hc
    · have hK2 := eq_zero_or_one_of_card_two hc
      by_cases hA2 : ∃ α ∈ componentRoots χ i, ∃ δ ∈ componentRoots χ i, δ ≠ α ∧ δ ≠ -α ∧
          CFSG.LieType.Steinberg.Adjoint.iform α α = CFSG.LieType.Steinberg.Adjoint.iform δ δ ∧
          CFSG.LieType.Steinberg.Adjoint.iform α δ ≠ 0
      · exact conclusion_of_perfect i (isPerfect_componentRootSpan_F4_two hK2 i hA2)
      · push Not at hA2
        obtain ⟨s, l, hss, hll, hsl, hΨ⟩ := eq_b2Block_of_noA2 i hbig hA2
        exact ⟨b2_two_derived_quasisimple hK2 i hss hll hsl hΨ, Or.inl hc⟩
    · exact conclusion_of_perfect i
        (isPerfect_componentRootSpan_F4_of_two_ne_zero (two_ne_zero_of_card_three hc) i hbig)
  all_goals
    exact conclusion_of_perfect i (isPerfect_componentRootSpan_simplyLaced (by simp [h]) i hbig)

theorem lq_inner_solvable_of_rank_one
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (hp : p.Prime)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .inner) (hp5 : τ = .G2 → 5 ≤ p)
    (hQ : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) < 4)
    (hrank : ∀ α ∈ componentRoots (rootCharHom a) i, ∀ δ ∈ componentRoots (rootCharHom a) i,
      δ = α ∨ δ = -α) :
    Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have : NeZero s := ⟨hs0.ne'⟩
  have hinner := twistInner_of_twistKind_eq_innerT S
    CFSG.HardMathSupport.Timmesfeld.RootAut.rootAutIsWeyl_holds hT i hkind
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwistT S hT i hs0 hinner
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * s)) := fun c => by rw [hσ, hq, ← pow_mul]
  have hQ' : r ^ (e * s) < 4 := by rw [pow_mul, ← hq]; exact hQ
  obtain ⟨hfinset, hcardset⟩ := ncard_pow_eq_self (L := L) r (e * s) (Nat.mul_pos he hs0)
  have hset : (fixSubfield σ : Set L) = {c : L | c ^ (r ^ (e * s)) = c} := by
    ext c
    show c ∈ fixSubfield σ ↔ _
    rw [mem_fixSubfield, hσ']
    rfl
  have hfinK : Finite (fixSubfield σ) := by
    have h1 : (fixSubfield σ : Set L).Finite := by rw [hset]; exact hfinset
    exact h1.to_subtype
  have hKcard : Nat.card (fixSubfield σ) = r ^ (e * s) := by
    have h1 : Nat.card (fixSubfield σ) = (fixSubfield σ : Set L).ncard :=
      Nat.card_coe_set_eq (fixSubfield σ : Set L)
    rw [h1, hset, hcardset]
  have hKle : Nat.card (fixSubfield σ) ≤ 3 := by rw [hKcard]; omega
  have hsL : ∃ u : Lˣ, u ^ 2 ≠ 1 := by
    obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset L)
    have hc0 : c ≠ 0 := fun h => hc (by simp [h])
    refine ⟨Units.mk0 c hc0, fun h => hc ?_⟩
    have h2 : c ^ 2 = 1 := by simpa using congrArg (fun x : Lˣ => (x : L)) h
    have h3 : (c - 1) * (c + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h | h
    · simp [sub_eq_zero.1 h]
    · simp [eq_neg_of_add_eq_zero_left h]
  set C := componentRootSpan (fixSubfield σ) (rootCharHom a) i with hCdef
  obtain ⟨f₁, hf₁1, -, -⟩ :=
    rationalComponent_eq_range_componentRootSpanT S hT i hs hmin σ z hnorm hz hsL
  have hCsolv : Group.IsSolvable ↥C :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isSolvable_componentRootSpan_of_rank_one
      hKle i hrank
  have : Group.IsSolvable ↥f₁.range := Group.isSolvable_of_surjective f₁.rangeRestrict_surjective
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hf₁1)
    (Subgroup.inclusion_injective hf₁1)

theorem lq_inner_quasisimple_of_not_rank_one
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (hp : p.Prime)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .inner) (hp5 : τ = .G2 → 5 ≤ p)
    (hQ : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) < 4)
    (hbig : ∃ α ∈ componentRoots (rootCharHom a) i, ∃ δ ∈ componentRoots (rootCharHom a) i,
      δ ≠ α ∧ δ ≠ -α) :
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have : NeZero s := ⟨hs0.ne'⟩
  have hinner := twistInner_of_twistKind_eq_innerT S
    CFSG.HardMathSupport.Timmesfeld.RootAut.rootAutIsWeyl_holds hT i hkind
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwistT S hT i hs0 hinner
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * s)) := fun c => by rw [hσ, hq, ← pow_mul]
  have hQ' : r ^ (e * s) < 4 := by rw [pow_mul, ← hq]; exact hQ
  obtain ⟨hfinset, hcardset⟩ := ncard_pow_eq_self (L := L) r (e * s) (Nat.mul_pos he hs0)
  have hset : (fixSubfield σ : Set L) = {c : L | c ^ (r ^ (e * s)) = c} := by
    ext c
    show c ∈ fixSubfield σ ↔ _
    rw [mem_fixSubfield, hσ']
    rfl
  have hfinK : Finite (fixSubfield σ) := by
    have h1 : (fixSubfield σ : Set L).Finite := by rw [hset]; exact hfinset
    exact h1.to_subtype
  have hKcard : Nat.card (fixSubfield σ) = r ^ (e * s) := by
    have h1 : Nat.card (fixSubfield σ) = (fixSubfield σ : Set L).ncard :=
      Nat.card_coe_set_eq (fixSubfield σ : Set L)
    rw [h1, hset, hcardset]
  have hKle : Nat.card (fixSubfield σ) ≤ 3 := by rw [hKcard]; omega
  have hsL : ∃ u : Lˣ, u ^ 2 ≠ 1 := by
    obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset L)
    have hc0 : c ≠ 0 := fun h => hc (by simp [h])
    refine ⟨Units.mk0 c hc0, fun h => hc ?_⟩
    have h2 : c ^ 2 = 1 := by simpa using congrArg (fun x : Lˣ => (x : L)) h
    have h3 : (c - 1) * (c + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h | h
    · simp [sub_eq_zero.1 h]
    · simp [eq_neg_of_add_eq_zero_left h]
  set C := componentRootSpan (fixSubfield σ) (rootCharHom a) i with hCdef
  obtain ⟨hDQ, hD⟩ := lk0xlqinner_smallFieldInner_not_rank_one (rootCharHom a) i hp hp5
      (fun γ hγ => rootChar_pow_eq_one_of_pow hTp hγ)
      (by obtain ⟨γ, hγ, hne⟩ := exists_rootChar_ne_one ha1; exact ⟨γ, hγ, hne⟩) hKle hbig
  have hY : ∀ g g' : ModGL τ L, g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) →
      g' ∈ rootSpan τ L (componentRoots (rootCharHom a) i) →
      frobGL σ g * g⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z →
      frobGL σ g' * g'⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z →
      ⁅g, g'⁆ ∈ (⁅C, C⁆).map (baseChangeGL (fixSubfield σ).subtype) := by
    intro g g' hg hg' hgZ hgZ'
    rcases hD with hD2 | hDC
    · have hF : ∀ d : L, σ d = d → d ≠ 0 → d = 1 := by
        intro d hd hd0
        let : Fintype (fixSubfield σ) := Fintype.ofFinite _
        have hcard : Fintype.card (fixSubfield σ) = 2 := by
          rw [← Nat.card_eq_fintype_card]; exact hD2
        have hdK : d ∈ fixSubfield σ := hd
        have h1 := FiniteField.pow_card_sub_one_eq_one (⟨d, hdK⟩ : fixSubfield σ)
          (fun h => hd0 (congrArg Subtype.val h))
        rw [hcard] at h1
        simpa using congrArg Subtype.val h1
      have := orbit_commutator_mem_commutator_CQT S hT i hs hmin σ hsL hF hg hg' hgZ hgZ'
      rwa [CQ_eq_map, ← Subgroup.map_commutator] at this
    · have := orbit_commutator_mem_CQT S hT i hs hmin σ hsL hg hg' hgZ hgZ'
      rwa [CQ_eq_map, ← hDC] at this
  obtain ⟨f, hf1, hker, hf2⟩ := rationalComponent_eq_rangeT S hT i hs hmin σ z hnorm hz
    ⁅C, C⁆ (Subgroup.commutator_le_self _ |>.trans le_rfl) hY
  have hperfD : ⁅⁅C, C⁆, ⁅C, C⁆⁆ = ⁅C, C⁆ := Subgroup.isPerfect_iff.1 hDQ.1
  rw [le_antisymm hf1 (hf2 hperfD)]
  exact isQuasisimple_range_of_ker_le_center hDQ f hker

end CFSG.StandardType.GGK0LQ

end

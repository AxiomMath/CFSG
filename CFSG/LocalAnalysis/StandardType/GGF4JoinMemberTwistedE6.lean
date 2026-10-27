module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatJoinF4
public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoCommon
public import CFSG.LocalAnalysis.StandardType.GGSelectedTwistedE6Scalar
public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoExcCore
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6U1aRootSub
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitTwE6Tag
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.LinLift
public import CFSG.LocalAnalysis.StandardType.GGSelectedLongExpTwo
import CFSG.LieType.CurtisTits.TwistedE6
import CFSG.LieType.Steinberg.TwistedE6.Generation
import CFSG.ClassicalInvolution.ModelFacts.Families

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open scoped commutatorElement

theorem GGPresentsG0.center_card_dvd_three_twistedE6
    {G : Type} [Group G] {G₀ : Subgroup G} {n f : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* G}
    (hpres : GGPresentsG0 G₀ (ggU .twistedE6 n f).D .twistedE6 n f ψ) :
    Nat.card (Subgroup.center ↥G₀) ∣ 3 := by
  let ψ₀ : (ggU .twistedE6 n f).K →* ↥G₀ :=
    ψ.codRestrict G₀ (fun a => hpres.2.1.1 ▸ MonoidHom.mem_range.2 ⟨a, rfl⟩)
  have hsurj : Function.Surjective ψ₀ := by
    intro y
    have hy : (y : G) ∈ ψ.range := by rw [hpres.2.1.1]; exact y.2
    obtain ⟨a, ha⟩ := hy
    exact ⟨a, Subtype.ext ha⟩
  have hker : ψ₀.ker ≤ Subgroup.center (ggU .twistedE6 n f).K := by
    intro a ha
    apply hpres.2.1.2
    have ha₀ : ψ₀ a = 1 := ha
    exact congrArg Subtype.val ha₀
  rw [CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.center_eq_map_center
    hsurj hker hpres.2.2.1]
  exact (Subgroup.card_map_dvd _ ψ₀).trans
    (TwE6Nonsplit.center_card_dvd_three f hpres.1.1.2.1)

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.GGFinModel
  CFSG.StandardType.LieKnownR2.ExcPos CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

theorem nonempty_twistedE6_actor_frame
    {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x z : G}
    {L D J : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2)
    {n f : ℕ} (ψ : (ggU .twistedE6 n f).K →* G)
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU .twistedE6 n f).D .twistedE6 n f ψ)
    (hz : z ∈ ggG0 p B x L D J) (hzp : z ^ p = 1) :
    Nonempty (ExcLangFrame .twistedE6 n f p ψ (ggG0 p B x L D J)
      (Subgroup.zpowers z) (Subgroup.zpowers z) z) := by
  have hdiag : GGPsiInnerDiag (ggU .twistedE6 n f).D ψ z :=
    ggPsiInnerDiag_of_mem_range _ (by rw [hpres.2.1.1]; exact hz)
  have hN : z ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G) :=
    (ggG0 p B x L D J).le_normalizer hz
  have hexc : GGExcFive .twistedE6 := by simp [GGExcFive]
  have hmono : CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt
      (langTag .twistedE6) p := by
    change CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialToralAt (langTag .E6) p
    exact FieldTwoExc.monomialToralAt_langTag (t := .E6) (Or.inl rfl) hp hp2
  exact FieldTwoExc.nonempty_excLangFrame_zpowers_of_normalizer
    hexc hp hp2 hpres hdiag hzp hN hmono

theorem eq_ggG0_of_isComponentOf_of_twistedE6_central
    {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x z : G}
    {L D J X : Subgroup G} {n f : ℕ} (ψ : (ggU .twistedE6 n f).K →* G)
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU .twistedE6 n f).D .twistedE6 n f ψ)
    (hX : CFSG.Assembly.IsComponentOf X (ggG0 p B x L D J ⊓ Subgroup.centralizer ({z} : Set G)))
    (hcentral : z ∈ Subgroup.centralizer (ggG0 p B x L D J : Set G)) :
    X = ggG0 p B x L D J := by
  obtain rfl : n = 0 := hpres.1.1.2.2
  have hG0 : CFSG.Assembly.IsQuasisimple (ggG0 p B x L D J) := by
    have hU : CFSG.IsQuasisimple (ggU .twistedE6 0 f).K :=
      CFSG.LieType.CurtisTits.isQuasisimple_twistedE6 2 f hpres.1.1.2.1
    have h := CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_range_of_ker_le_center
      hU ψ hpres.2.1.2
    erw [hpres.2.1.1] at h
    exact ⟨h.1.commutator_eq_top, h.2.1⟩
  have hle : ggG0 p B x L D J ≤ Subgroup.centralizer ({z} : Set G) := by
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 hcentral g hg)
  rw [inf_eq_left.2 hle] at hX
  exact Line63.H5.eq_of_isComponentOf_of_isQuasisimple hX hG0

theorem exists_selected_twistedE6_of_central
    {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x z : G}
    {L D J X : Subgroup G} {n f : ℕ} (ψ : (ggU .twistedE6 n f).K →* G)
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU .twistedE6 n f).D .twistedE6 n f ψ)
    (hX : CFSG.Assembly.IsComponentOf X (ggG0 p B x L D J ⊓ Subgroup.centralizer ({z} : Set G)))
    (hcentral : z ∈ Subgroup.centralizer (ggG0 p B x L D J : Set G)) :
    ∃ S : Subgroup G, MemberSelectedSL2At X S ∧ PresentedSelectedSL2At ψ S := by
  obtain rfl : n = 0 := hpres.1.1.2.2
  have hXe := eq_ggG0_of_isComponentOf_of_twistedE6_central ψ hpres hX hcentral
  obtain ⟨model, -⟩ :=
    CFSG.ClassicalInvolution.Phan.PhanE.exists_selectedSL2Model_twistedE6_fixed
      hpres.1.1.2.1 (1 : Fin 6) rfl
  refine ⟨(ψ.comp model.phi).range,
    ⟨.twistedE6, 0, f, ψ, hpres.1.1, hpres.1.2, hpres.2.1.2,
      hpres.2.1.1.trans hXe.symm, GaloisField 2 f, inferInstance, inferInstance, inferInstance,
      _, model, rfl⟩,
    GaloisField 2 f, inferInstance, inferInstance, inferInstance, _, model, 1, ?_⟩
  have hconj : ψ.comp (MulAut.conj (1 : (ggU .twistedE6 0 f).K)).toMonoidHom = ψ := by
    refine MonoidHom.ext fun u => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      one_mul, inv_one, mul_one]
  rw [hconj]

theorem exists_twistedE6_member_class
    {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x z : G}
    {L D J X : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2)
    {n f : ℕ} (ψ : (ggU .twistedE6 n f).K →* G)
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU .twistedE6 n f).D .twistedE6 n f ψ)
    (hz : z ∈ ggG0 p B x L D J) (hzp : z ^ p = 1) (hXG0 : X ≤ ggG0 p B x L D J)
    (hXc : CFSG.Assembly.IsComponentOf X (Subgroup.centralizer ({z} : Set G)))
    (hnc : z ∉ Subgroup.centralizer (ggG0 p B x L D J : Set G)) :
    ∃ F : ExcLangFrame .twistedE6 n f p ψ (ggG0 p B x L D J)
      (Subgroup.zpowers z) (Subgroup.zpowers z) z,
      rootDiagUnit (langTag .twistedE6) (F.coord z) ∈ F.setup.D.torus ∧
      (∀ j, F.coord z j ^ p = 1) ∧ rootDiagUnit (langTag .twistedE6) (F.coord z) ≠ 1 ∧
      ∃ i : KernelComponent (rootCharHom (F.coord z)),
        CFSG.IsQuasisimple (rationalComponent F.setup.ρ F.setup.Γ (rootCharHom (F.coord z)) i) ∧
        (X.subgroupOf (ggG0 p B x L D J)).map F.η =
          rationalComponent F.setup.ρ F.setup.Γ (rootCharHom (F.coord z)) i := by
  obtain ⟨F⟩ := nonempty_twistedE6_actor_frame hp hp2 ψ hpres hz hzp
  have hN : Subgroup.zpowers z ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) :=
    Subgroup.zpowers_le.2 ((ggG0 p B x L D J).le_normalizer hz)
  obtain ⟨hT, hap, hne, i, hqs, hL⟩ :=
    ExcLangFrame.exists_class_of_noncentral_of_ne_G2 (t := .twistedE6) (by simp [langTag])
      hp hp2 hN F hXG0 hXc hnc
  exact ⟨F, hT, hap, hne, i, hqs, hL⟩

open CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.ModelFacts

theorem presentedSelectedSL2At_twistedE6_long
    {G : Type} [Group G] {n f : ℕ} (hf : 1 ≤ f)
    (ψ : (ggU .twistedE6 n f).K →* G)
    {β : Fin (ggU .twistedE6 n f).D.rank → ℤ}
    (hβ : GGLongRoot (ggU .twistedE6 n f).D β) (u : (ggU .twistedE6 n f).K) :
    PresentedSelectedSL2At ψ
      (ggRootSub (ggU .twistedE6 n f).D ψ β u ⊔
        ggRootSub (ggU .twistedE6 n f).D ψ (-β) u) := by
  let D := (ggU .twistedE6 n f).D
  let θ := CFSG.LieType.Steinberg.Exceptional.frobQ 2 f
  have hθ : ∀ c, θ (θ c) = c :=
    CFSG.LieType.Steinberg.Exceptional.frobQ_frobQ 2 f hf
  have hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup
      (CFSG.LieType.Steinberg.TwistedE6.nHat θ)
      (CFSG.LieType.Steinberg.TwistedE6.hHat (GaloisField 2 (2 * f)) θ) :=
    CFSG.LieType.Steinberg.TwistedE6.twistedDatum_isCTGroupDatum θ hθ
      (CFSG.LieType.Steinberg.TwistedE6.iSup_twistedDatum_rootGroup θ hθ)
  have hirr : IsIrreducible D.cartan := isIrreducible_F4
  have hdiv : D.divisible = ∅ := ggU_divisible_twistedE6 n f
  let α : Fin D.rank → ℤ := CFSG.LieType.Steinberg.TwistedE6.proj (Pi.single (1 : Fin 6) 1)
  have hα : GGLongRoot D α :=
    CFSG.ClassicalInvolution.Phan.PhanE.twistedE6_fixed_simple_long 1 rfl
  obtain ⟨model, hmodel⟩ :=
    CFSG.ClassicalInvolution.Phan.PhanE.exists_selectedSL2Model_twistedE6_fixed hf (1 : Fin 6) rfl
  exact SiegelPair.presentedSelectedSL2At_ggRootSub_of_longModel ψ hct hirr hdiv
    (SiegelPair.isLongestRoot_of_ggLongRoot hirr hdiv hα) model hmodel.1
    (SiegelPair.isLongestRoot_of_ggLongRoot hirr hdiv hβ) u

theorem ggActualMember_twistedE6_selected
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs L D J X : Subgroup G} {x : G}
    (hcfg : GGConfig p B Bs x L D J) {n f : ℕ}
    (ψ : (ggU .twistedE6 n f).K →* G)
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU .twistedE6 n f).D .twistedE6 n f ψ)
    (horigin : (X = L ∧ x ∈ ggG0 p B x L D J) ∨
      ∃ y : G, GGNbr p B x D J y X ∧ y ∈ ggG0 p B x L D J)
    (hmark : LargeEvenMarking ↥X (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) :
    ∃ S : Subgroup G, MemberSelectedSL2At X S ∧ PresentedSelectedSL2At ψ S := by
  obtain rfl : n = 0 := hpres.1.1.2.2
  obtain ⟨hp, hp2, -⟩ := (hcfg.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  have hq : CFSG.Assembly.IsQuasisimple ↥X := isQuasisimple_of_largeEvenMarking hmark
  obtain ⟨z, hz, hzG, hzp, hXC⟩ := ggActualMember_internal_component hcfg horigin hq
  by_cases hcentral : z ∈ Subgroup.centralizer (ggG0 p B x L D J : Set G)
  · exact exists_selected_twistedE6_of_central ψ hpres hXC hcentral
  have hXc : CFSG.Assembly.IsComponentOf X (Subgroup.centralizer ({z} : Set G)) := by
    rcases hz with ⟨rfl, rfl⟩ | hNb
    · exact hcfg.1.2.2.2.2.2.2.1.2.2.2.1
    · exact ⟨hNb.1.2.2.2.2.1.1, hNb.1.2.2.2.2.1.2.1, hq⟩
  have hXG0 : X ≤ ggG0 p B x L D J := hXC.1.trans inf_le_left
  obtain ⟨F, hT, hap, h1, i, hqs, hL⟩ :=
    exists_twistedE6_member_class hp hp2 ψ hpres hzG hzp hXG0 hXc hcentral
  have hstep : F.RootStep := by
    intro α w hα hw hV hVm
    exact ExcLangFrame.exists_rootSub_twistedE6 hpres.2.1.1 F hα hw hV hVm
  have hf : 1 ≤ f := hpres.1.1.2.1
  have hZodd : Odd (Nat.card (Subgroup.center ↥(ggG0 p B x L D J))) :=
    Odd.of_dvd_nat (by decide : Odd (3 : ℕ)) hpres.center_card_dvd_three_twistedE6
  obtain ⟨S, hmember, β, hβ, hlong, k, hS⟩ :=
    F4JoinE6.exists_member_rootPair (by simp only [langTag]) hp hp2 hpres.2.1.1 hZodd F hstep
      hXG0 hf hT hap h1 i hqs hL hmark (LongExpTwo.ggRootSub_exponent_two_twistedE6 hf ψ)
  refine ⟨S, hmember, ?_⟩
  rw [hS]
  exact presentedSelectedSL2At_twistedE6_long hf ψ hlong k

end CFSG.StandardType

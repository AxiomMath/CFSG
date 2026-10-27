module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanK8K9
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPFF2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPH2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPH7
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL11
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL3
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL4
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL6
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL8b
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPR
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS2a
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS2b
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS7a
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS7b
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6
import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndSix
import CFSG.RankThree.PartTwo.Sec4.Item422KFact
public import CFSG.GroupTheory.CentralizerQuotientCard
public import CFSG.GroupTheory.IsCyclicOfPRankLeOne
public import CFSG.GroupTheory.PLayer.PIndex
public import CFSG.LocalAnalysis.RankThreeUC.Section12.Context
public import CFSG.Quasithin.Background.C1PackC129Case
public import CFSG.Quasithin.Background.G25Seven
public import CFSG.Quasithin.EmptyFaithful.R3cBlocks
public import CFSG.Quasithin.EmptyFaithful.S14113bMain
public import CFSG.Quasithin.EmptyFaithful.S146zMComp
public import CFSG.Quasithin.EmptyFaithful.S146zQLists
public import CFSG.Quasithin.EmptyFaithful.SBc15R3G
public import CFSG.Quasithin.EmptyFaithful.SBc16SComp
public import CFSG.Quasithin.EmptyFaithful.SBc16SWr
public import CFSG.Quasithin.EmptyFaithful.SBc17Out5L
public import CFSG.Quasithin.H13.L32NThm1443
public import CFSG.Quasithin.SteinbergOuterPrimeControl
public import CFSG.RankThree.PartTwo.Sec16.Item1621StepsProofPara
public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldExc
public import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.GorensteinLyons (orbitConjugates)
open scoped Pointwise commutatorElement
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

noncomputable abbrev centralizerAt (a : G) : Subgroup G :=
  Subgroup.centralizer ({a} : Set G)

noncomputable abbrev thetaAt (a : G) : Subgroup ↥(centralizerAt a) :=
  aschbacherSolvableCore 3 ↥(centralizerAt a)

@[expose] noncomputable def thetaImgAt (a : G) (K : Subgroup G) :
    Subgroup (↥(centralizerAt a) ⧸ thetaAt a) :=
  (K.subgroupOf (centralizerAt a)).map (QuotientGroup.mk' (thetaAt a))

theorem perm_six_eq_bot_of_normal_isPGroup_two
    {H M : Subgroup (Equiv.Perm (Fin 6))} (hMH : M ≤ H)
    (hH : Group.IsPerfect H)
    (hnorm : ∀ h ∈ H, ∀ m ∈ M, h * m * h⁻¹ ∈ M)
    (hM : IsPGroup 2 M) : M = ⊥ := by
  have hMn : (M.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff hMH).2 fun h k hh hk => hnorm k hk h hh
  by_cases hbot : H = ⊥
  · rw [hbot] at hMH
    exact le_bot_iff.mp hMH
  rcases CFSG.RankThree.PartTwo.Sec4.Census.perfect_perm_six hH hbot with hA6 | he5
  · subst hA6
    haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    rcases hMn.eq_bot_or_eq_top with hb | ht
    · have hle : M ≤ ⊥ := by
        intro m hm
        have h1 : (⟨m, hMH hm⟩ : ↥(alternatingGroup (Fin 6))) ∈
            M.subgroupOf (alternatingGroup (Fin 6)) := hm
        rw [hb] at h1
        simpa using h1
      exact le_bot_iff.mp hle
    · have htop : alternatingGroup (Fin 6) ≤ M := Subgroup.subgroupOf_eq_top.mp ht
      have hMtop : M = alternatingGroup (Fin 6) := le_antisymm hMH htop
      rw [hMtop] at hM
      obtain ⟨n, hn⟩ := hM.exists_card_eq
      have hcard : Nat.card (alternatingGroup (Fin 6)) = 360 := by
        rw [nat_card_alternatingGroup, Nat.card_fin]; rfl
      rw [hcard] at hn
      have hle : n ≤ 8 := by
        by_contra h
        have h9 : 9 ≤ n := by omega
        have hp : 2 ^ 9 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h9
        omega
      interval_cases n <;> norm_num at hn
  ·
    obtain ⟨e5⟩ := he5
    haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    have hmapn : ((M.subgroupOf H).map e5.toMonoidHom).Normal :=
      Subgroup.Normal.map hMn e5.toMonoidHom e5.surjective
    rcases hmapn.eq_bot_or_eq_top with hb | ht
    · have hMt : M.subgroupOf H = ⊥ := by
        have hle : M.subgroupOf H ≤ e5.toMonoidHom.ker :=
          (Subgroup.map_eq_bot_iff _).1 hb
        have hker : e5.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e5.injective
        rw [hker] at hle
        exact le_bot_iff.mp hle
      have hle : M ≤ ⊥ := by
        intro m hm
        have h1 : (⟨m, hMH hm⟩ : ↥H) ∈ M.subgroupOf H := hm
        rw [hMt] at h1
        simpa using h1
      exact le_bot_iff.mp hle
    · have htop : (M.subgroupOf H).map e5.toMonoidHom = ⊤ := ht
      have hMt : M.subgroupOf H = ⊤ := by
        refine Subgroup.map_injective (f := e5.toMonoidHom) e5.injective ?_
        rw [htop, Subgroup.map_top, MonoidHom.range_eq_top.mpr e5.surjective]
      have hHM : H ≤ M := Subgroup.subgroupOf_eq_top.mp hMt
      have hMtop : M = H := le_antisymm hMH hHM
      rw [hMtop] at hM
      obtain ⟨n, hn⟩ := hM.exists_card_eq
      have hcard : Nat.card H = 60 := by
        rw [Nat.card_congr e5.toEquiv, nat_card_alternatingGroup, Nat.card_fin]; rfl
      rw [hcard] at hn
      have hle : n ≤ 5 := by
        by_contra h
        have h6 : 6 ≤ n := by omega
        have hp : 2 ^ 6 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h6
        omega
      interval_cases n <;> norm_num at hn

theorem center_eq_bot_of_isPerfect_perm_six {H : Subgroup (Equiv.Perm (Fin 6))}
    (hH : Group.IsPerfect H) : Subgroup.center H = ⊥ := by
  by_cases hbot : H = ⊥
  · rw [hbot]
    exact le_bot_iff.mp (fun x _ => Subgroup.mem_bot.mpr (Subsingleton.elim x 1))
  rcases CFSG.RankThree.PartTwo.Sec4.Census.perfect_perm_six hH hbot with hA6 | he5
  · rw [hA6]
    exact CFSG.RankThree.PartTwo.Sec14.center_eq_bot_of_mulEquiv_alternating_six (MulEquiv.refl _)
  · obtain ⟨e5⟩ := he5
    haveI : IsSimpleGroup ↥H :=
      (MulEquiv.isSimpleGroup_congr e5).2 (alternatingGroup.isSimpleGroup (by simp))
    have hnc5 : ∃ x y : ↥(alternatingGroup (Fin 5)), x * y ≠ y * x := by
      refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, ?_⟩,
        ⟨Equiv.swap 0 2 * Equiv.swap 2 3, ?_⟩, ?_⟩
      · rw [Equiv.Perm.mem_alternatingGroup]; decide
      · rw [Equiv.Perm.mem_alternatingGroup]; decide
      · decide
    obtain ⟨x, y, hxy⟩ := hnc5
    refine CFSG.GorensteinWalter.Helpers.center_eq_bot_of_noncommutative ⟨e5.symm x, e5.symm y, ?_⟩
    intro h
    exact hxy (by simpa using congrArg e5 h)

theorem z_fixes_orbit_of_six'
    {J : Subgroup G}
    (hP2 : IsTripleCover (perfectCoreL c a ⧸ CFSG.Open.pCore 2 ↥(perfectCoreL c a))
        (alternatingGroup (Fin 6)) ∧
      zSub P c.L ≤ perfectCoreL c a ∧
      ⁅perfectCoreL c a, zSub P c.L⁆ ≤
        CFSG.Open.pCoreOf 2 (perfectCoreL c a) ∧
      A ≤ Subgroup.closure ({a} : Set G) ⊔ perfectCoreL c a)
    (h6 : (orbitConjugates (perfectCoreL c a) J).ncard = 6) :
    ∀ z ∈ zSub P c.L, ∀ K ∈ orbitConjugates (perfectCoreL c a) J,
      z ∈ Subgroup.normalizer (K : Set G) := by
  classical
  let I : Subgroup G := perfectCoreL c a
  let Zs : Subgroup G := zSub P c.L
  let N : Subgroup G := CFSG.Open.pCoreOf 2 I
  obtain ⟨_, hZI, hcomm, _⟩ := hP2
  letI : MulAction ↥I (Subgroup G) :=
    MulAction.compHom (Subgroup G) (MulAut.conj.comp I.subtype)
  have hsmul : ∀ (b : ↥I) (M : Subgroup G), b • M = M.map (MulAut.conj (b : G)).toMonoidHom :=
    fun b M => by
      change (MulAut.conj (b : G)) • M = _
      rw [Subgroup.pointwise_smul_def]
      rfl
  let Ω : Set (Subgroup G) := MulAction.orbit ↥I J
  have hΩeq : Ω = orbitConjugates I J := by
    ext M
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨(b : G)⁻¹, inv_mem b.2, by rw [hsmul, CFSG.conjugate, inv_inv]⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b⁻¹, inv_mem hb⟩, by rw [hsmul, CFSG.conjugate]⟩
  have hfin' : (orbitConjugates I J).Finite := by
    have hrange : orbitConjugates I J =
        Set.range (fun b : ↥I => CFSG.conjugate J (b : G)) := by
      ext M
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨⟨b, hb⟩, rfl⟩
      · rintro ⟨b, rfl⟩
        exact ⟨b, b.2, rfl⟩
    rw [hrange]
    exact Set.finite_range _
  have hfin : Ω.Finite := by rw [hΩeq]; exact hfin'
  haveI : Fintype Ω := hfin.fintype
  have hΩn : Fintype.card Ω = 6 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hΩeq]
    exact h6
  let e : Ω ≃ Fin 6 := Fintype.equivFinOfCardEq hΩn
  let ρ : ↥I →* Equiv.Perm Ω := MulAction.toPermHom ↥I Ω
  let ρ' : ↥I →* Equiv.Perm (Fin 6) := (Equiv.permCongrHom e).toMonoidHom.comp ρ
  let H : Subgroup (Equiv.Perm (Fin 6)) := ρ'.range
  haveI : Group.IsPerfect ↥I := perfectCoreL_isPerfect c a
  have hHperf : Group.IsPerfect H := Group.IsPerfect.range ρ'
  have hcenter : Subgroup.center H = ⊥ := center_eq_bot_of_isPerfect_perm_six hHperf
  have hNsub_eq : N.subgroupOf I = CFSG.pCore 2 ↥I := by
    ext x
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hx' : (x : G) ∈ Subgroup.map I.subtype (CFSG.pCore 2 ↥I) := hx
      obtain ⟨n, hn, hnx⟩ := hx'
      have hxn : x = n := Subtype.ext (by simpa using hnx.symm)
      rwa [hxn]
    · intro hx
      exact Subgroup.mem_map_of_mem I.subtype hx
  have hNsubN : (N.subgroupOf I).Normal := by
    rw [hNsub_eq]
    exact CFSG.pCore_normal
  have hN2 : IsPGroup 2 (N.subgroupOf I) := by
    rw [hNsub_eq]
    exact CFSG.pCore_isPGroup
  have hM'2 : IsPGroup 2 ((N.subgroupOf I).map ρ') := hN2.map ρ'
  have hM'le : (N.subgroupOf I).map ρ' ≤ H := Subgroup.map_le_range ρ' _
  have hM'norm : ∀ h ∈ H, ∀ m ∈ (N.subgroupOf I).map ρ', h * m * h⁻¹ ∈ (N.subgroupOf I).map ρ' := by
    intro h hh m hm
    obtain ⟨g, rfl⟩ := hh
    obtain ⟨n, hn, rfl⟩ := hm
    have hconj : g * n * g⁻¹ ∈ N.subgroupOf I := hNsubN.conj_mem n hn g
    have hconj' : ρ' (g * n * g⁻¹) ∈ Subgroup.map ρ' (N.subgroupOf I) :=
      Subgroup.mem_map_of_mem ρ' hconj
    simpa only [map_mul, map_inv] using hconj'
  have hM'bot : (N.subgroupOf I).map ρ' = ⊥ :=
    perm_six_eq_bot_of_normal_isPGroup_two hM'le hHperf hM'norm hM'2
  have hNker : N.subgroupOf I ≤ ρ'.ker := (Subgroup.map_eq_bot_iff _).1 hM'bot
  intro z hz K hK
  have hzI : z ∈ I := hZI hz
  have hzcenter : (⟨ρ' ⟨z, hzI⟩, ⟨⟨z, hzI⟩, rfl⟩⟩ : ↥H) ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro h
    obtain ⟨g, hg⟩ := h.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    have hval : (h : Equiv.Perm (Fin 6)) = ρ' g := hg.symm
    rw [hval]
    have hcom : ⁅g, (⟨z, hzI⟩ : ↥I)⁆ ∈ N.subgroupOf I := by
      rw [Subgroup.mem_subgroupOf]
      show I.subtype ⁅g, (⟨z, hzI⟩ : ↥I)⁆ ∈ N
      rw [map_commutatorElement]
      exact hcomm (Subgroup.commutator_mem_commutator g.2 hz)
    have h1 : ρ' ⁅g, (⟨z, hzI⟩ : ↥I)⁆ = 1 := by
      have := hNker hcom
      simpa using this
    rw [map_commutatorElement, commutatorElement_def] at h1
    calc ρ' g * ρ' ⟨z, hzI⟩
        = (ρ' g * ρ' ⟨z, hzI⟩ * (ρ' g)⁻¹ * (ρ' ⟨z, hzI⟩)⁻¹) *
            (ρ' ⟨z, hzI⟩ * ρ' g) := by group
      _ = 1 * (ρ' ⟨z, hzI⟩ * ρ' g) := by rw [h1]
      _ = ρ' ⟨z, hzI⟩ * ρ' g := one_mul _
  have hz1 : ρ' ⟨z, hzI⟩ = 1 := by
    rw [hcenter] at hzcenter
    have h1 : (⟨ρ' ⟨z, hzI⟩, ⟨⟨z, hzI⟩, rfl⟩⟩ : ↥H) = 1 := by simpa using hzcenter
    exact congrArg Subtype.val h1
  have hzρ : ρ ⟨z, hzI⟩ = 1 := by
    have h2 : (Equiv.permCongrHom e) (ρ ⟨z, hzI⟩) = 1 := by
      simpa [ρ'] using hz1
    exact (Equiv.permCongrHom e).injective (h2.trans (map_one (Equiv.permCongrHom e)).symm)
  have hKΩ : K ∈ Ω := by rw [hΩeq]; exact hK
  have hfix : (⟨z, hzI⟩ : ↥I) • (⟨K, hKΩ⟩ : Ω) = ⟨K, hKΩ⟩ := by
    have h1 : ρ ⟨z, hzI⟩ • (⟨K, hKΩ⟩ : Ω) = ⟨K, hKΩ⟩ := by
      rw [hzρ]
      exact one_smul _ _
    simpa [ρ, MulAction.toPermHom_apply, Equiv.Perm.smul_def, MulAction.toPerm_apply] using h1
  have hfixK : (⟨z, hzI⟩ : ↥I) • K = K := by
    have h := congrArg Subtype.val hfix
    rwa [MulAction.orbit.coe_smul] at h
  have hmap : K.map (MulAut.conj z).toMonoidHom = K := by
    rw [← hsmul (⟨z, hzI⟩ : ↥I) K]
    exact hfixK
  exact CFSG.LocalAnalysis.GorensteinLyons.map_conj_eq_self_iff.mp hmap

theorem z_normalizes_orbit
    (hPSz : CFSG.RankThree.PartTwo.KFacts.KPSz) (hK8 : K8Cat)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hA27 : Nat.card A = 27) (hZA : zSub P c.L ≤ A)
    (hAPL : A ≤ P ⊓ c.L) (ha : a ∈ A) (haZ : a ∉ zSub P c.L)
    (hP2 : IsTripleCover (perfectCoreL c a ⧸ CFSG.Open.pCore 2 ↥(perfectCoreL c a))
        (alternatingGroup (Fin 6)) ∧
      zSub P c.L ≤ perfectCoreL c a ∧
      ⁅perfectCoreL c a, zSub P c.L⁆ ≤
        CFSG.Open.pCoreOf 2 (perfectCoreL c a) ∧
      A ≤ Subgroup.closure ({a} : Set G) ⊔ perfectCoreL c a)
    (hP3 : CFSG.Open.pRank 7 (Subgroup.centralizer ({a} : Set G)) = 1)
    (hP5 : ∀ W : Subgroup G, W ≤ D.M → Group.IsPerfect ↥W → ¬ 3 ∣ Nat.card W →
      W ≤ CFSG.LocalAnalysis.RankThreeUC.centralizerOnQuotient D.M
        (CFSG.Open.pCoreOf 2 c.L) c.L)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a) (h3 : ¬ 3 ∣ Nat.card J)
    (h6 : (orbitConjugates (perfectCoreL c a) J).ncard = 6)
    (h7J : ¬ 7 ∣ Nat.card (J ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 J)) :
    ∀ z ∈ zSub P c.L, ∀ K ∈ orbitConjugates (perfectCoreL c a) J,
      z ∈ Subgroup.normalizer (K : Set G) :=
  z_fixes_orbit_of_six' c hP2 h6

@[expose] def ZSubIsThreeGroup (P L : Subgroup G) : Prop :=
  IsPGroup 3 (zSub P L)

theorem card_thetaQuot_conj {J : Subgroup G} {b : G} :
    Nat.card (↥(CFSG.conjugate J b) ⧸
        aschbacherSolvableCore 3 ↥(CFSG.conjugate J b)) =
      Nat.card (↥J ⧸ aschbacherSolvableCore 3 ↥J) := by
  classical
  let e : ↥J ≃* ↥(CFSG.conjugate J b) :=
    Subgroup.equivMapOfInjective J (MulAut.conj b⁻¹).toMonoidHom (MulAut.conj b⁻¹).injective
  have hθ : (aschbacherSolvableCore 3 ↥J).map e.toMonoidHom =
      aschbacherSolvableCore 3 ↥(CFSG.conjugate J b) :=
    CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e
  exact Nat.card_congr (QuotientGroup.congr _ _ e hθ).toEquiv.symm

theorem z_centralizes_components_of_isPGroup
    (hPSz : CFSG.RankThree.PartTwo.KFacts.KPSz)
    (hZ3 : ZSubIsThreeGroup P c.L)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a) (h3 : ¬ 3 ∣ Nat.card J)
    (h6 : (orbitConjugates (perfectCoreL c a) J).ncard = 6)
    (h7J : ¬ 7 ∣ Nat.card (J ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 J))
    (hfix : ∀ z ∈ zSub P c.L, ∀ K ∈ orbitConjugates (perfectCoreL c a) J,
      z ∈ Subgroup.normalizer (K : Set G)) :
    ∀ K ∈ orbitConjugates (perfectCoreL c a) J,
      autThetaQuot (zSub P c.L) K = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3G : 3 ∣ Nat.card G := by
    obtain ⟨E, hEL, -, hEcard⟩ :=
      CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (H := c.L) (k := 3)
        (by simpa using c.hyp81.2.2.2.1)
    have h3E : 3 ∣ Nat.card E := by rw [hEcard]; norm_num
    exact h3E.trans ((Subgroup.card_dvd_of_le hEL).trans (Subgroup.card_subgroup_dvd_card c.L))
  have hZ3' : IsPGroup 3 (zSub P c.L) := hZ3
  intro K hK
  obtain ⟨b, hb, rfl⟩ := hK
  have hbc : b⁻¹ ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.inv_mem _ (perfectCoreL_le c a hb).2
  have hKθ : CFSG.conjugate J b ∈ thetaComponentsAt 3 a :=
    CFSG.RankThree.PartOne.F106.conj_mem_thetaComponentsAt_cent Nat.prime_three hbc hJ
  have hK3 : ¬ 3 ∣ Nat.card (CFSG.conjugate J b) := by
    change ¬ 3 ∣ Nat.card ↥(J.map (MulAut.conj b⁻¹).toMonoidHom)
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj b⁻¹).toMonoidHom)
      (MulAut.conj b⁻¹).injective]
    exact h3
  have hKne : CFSG.conjugate J b ≠ ⊤ := by
    intro htop
    apply hK3
    rw [htop]
    simpa using h3G
  let Q := ↥(CFSG.conjugate J b) ⧸ aschbacherSolvableCore 3 ↥(CFSG.conjugate J b)
  have hKK : CFSG.Open.IsKGroup ↥(CFSG.conjugate J b) :=
    D.standing.kProper.isKGroup _ hKne
  have hqQ : CFSG.IsQuasisimple Q :=
    CFSG.RankThree.PartOne.isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt
      Nat.prime_three hKθ
  have hQK : CFSG.Open.IsKGroup Q :=
    hKK.quotient (aschbacherSolvableCore 3 ↥(CFSG.conjugate J b))
  have h3Q : ¬ 3 ∣ Nat.card Q := fun h =>
    hK3 (h.trans (Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 ↥(CFSG.conjugate J b))))
  have h3S : ¬ 3 ∣ Nat.card (Q ⧸ Subgroup.center Q) := fun h =>
    h3Q (h.trans (Subgroup.card_quotient_dvd_card (Subgroup.center Q)))
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hqQ.2.1
  have hnab : ∃ x y : Q ⧸ Subgroup.center Q, x * y ≠ y * x := hqQ.2.2
  have hcat : CFSG.Assembly.InCatalog (Q ⧸ Subgroup.center Q) :=
    hQK.isCatalogGroup_of_surjective (⊤ : Subgroup Q) hnab
      ((QuotientGroup.mk' (Subgroup.center Q)).comp
        (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q).toMonoidHom)
      ((QuotientGroup.mk'_surjective _).comp
        (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q).surjective)
  obtain ⟨f, hSz⟩ := hPSz (Q ⧸ Subgroup.center Q) hnab hcat h3S
  haveI : Group.IsPerfect Q := hqQ.1
  have hOutdvd : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Q) ∣ f :=
    ((CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity
      (Q ⧸ Subgroup.center Q) 2 f hSz).2 Q ⟨MulEquiv.refl _⟩).2.1
  have h3f : ¬ 3 ∣ f := by
    intro h3df
    obtain ⟨-, a', ha', Kf, hField, hFin, hf, hKcard, ⟨eS⟩⟩ := hSz
    letI : Field Kf := hField
    letI : Finite Kf := hFin
    have hKf : Nat.card Kf = 2 ^ (2 * a' + 1) := by rw [hf] at hKcard; exact hKcard
    have hord := CFSG.LieType.Ree.suzuki_order (a := a') (K := Kf) hKf
    rw [← hf] at hord
    have hScard : Nat.card (Q ⧸ Subgroup.center Q) =
        (2 ^ f) ^ 2 * (2 ^ f - 1) * ((2 ^ f) ^ 2 + 1) := by
      rw [Nat.card_congr eS.toEquiv, hord]
    obtain ⟨m, hm⟩ := h3df
    have h7 : 7 ∣ 2 ^ f - 1 := by
      rw [hm]
      have hbase : 1 ≡ 2 ^ 3 [MOD 7] := by norm_num
      have hmod : 1 ≡ 2 ^ (3 * m) [MOD 7] := by
        simpa [pow_mul] using hbase.pow m
      exact (Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).mp hmod
    have h7S : 7 ∣ Nat.card (Q ⧸ Subgroup.center Q) := by
      rw [hScard]
      exact dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_right h7 ((2 ^ f) ^ 2)) ((2 ^ f) ^ 2 + 1)
    have h7Q : 7 ∣ Nat.card Q :=
      h7S.trans (Subgroup.card_quotient_dvd_card (Subgroup.center Q))
    have h7KQ : 7 ∣ Nat.card (↥(CFSG.conjugate J b) ⧸
        aschbacherSolvableCore 3 ↥(CFSG.conjugate J b)) := by
      change 7 ∣ Nat.card Q
      exact h7Q
    rw [card_thetaQuot_conj] at h7KQ
    exact h7J h7KQ
  have hOut3 : ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Q) :=
    fun h => h3f (h.trans hOutdvd)
  have hInnEq : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner Q) =
      Nat.card (Q ⧸ Subgroup.center Q) :=
    CFSG.RankThree.PartTwo.Sec4.Item422Proof.card_range_conj_eq
  have hAut3 : ¬ 3 ∣ Nat.card (MulAut Q) := by
    intro h
    have h' : 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Q) *
        Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner Q) := by
      rwa [(CFSG.ComponentClassification.OuterAutomorphisms.inner
        Q).card_eq_card_quotient_mul_card_subgroup]
        at h
    rcases (Nat.prime_three.dvd_mul).mp h' with h1 | h1
    · exact hOut3 h1
    · exact h3S (hInnEq ▸ h1)
  have hImg3 : IsPGroup 3 (autThetaQuot (zSub P c.L) (CFSG.conjugate J b)) := by
    have h1 : IsPGroup 3 (((zSub P c.L) ⊓
        Subgroup.normalizer (CFSG.conjugate J b : Set G)).subgroupOf
          (Subgroup.normalizer (CFSG.conjugate J b : Set G))) :=
      (hZ3'.to_le inf_le_left).comap_subtype
    exact (h1.map (CFSG.conjugate J b).normalizerMonoidHom).map
      (thetaQuotMulAut (CFSG.conjugate J b))
  have hImg3' : ¬ 3 ∣ Nat.card (autThetaQuot (zSub P c.L) (CFSG.conjugate J b)) := fun h =>
    hAut3 (h.trans (Subgroup.card_subgroup_dvd_card
      (autThetaQuot (zSub P c.L) (CFSG.conjugate J b))))
  obtain ⟨k, hk⟩ := hImg3.exists_card_eq
  have hk0 : k = 0 := by
    by_contra hne
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hne
    refine hImg3' (hk ▸ ⟨3 ^ m, ?_⟩)
    rw [pow_succ]
    ring
  have hcard1 : Nat.card (autThetaQuot (zSub P c.L) (CFSG.conjugate J b)) = 1 := by
    rw [hk, hk0]
    norm_num
  exact Subgroup.eq_bot_of_card_eq _ hcard1

theorem z_centralizes_components_of_sylow
    (hPSz : CFSG.RankThree.PartTwo.KFacts.KPSz)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a) (h3 : ¬ 3 ∣ Nat.card J)
    (h6 : (orbitConjugates (perfectCoreL c a) J).ncard = 6)
    (h7J : ¬ 7 ∣ Nat.card (J ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 J))
    (hfix : ∀ z ∈ zSub P c.L, ∀ K ∈ orbitConjugates (perfectCoreL c a) J,
      z ∈ Subgroup.normalizer (K : Set G)) :
    ∀ K ∈ orbitConjugates (perfectCoreL c a) J,
      autThetaQuot (zSub P c.L) K = ⊥ := by
  refine z_centralizes_components_of_isPGroup c hPSz ?_ hJ h3 h6 h7J hfix
  exact hP.isPGroup.to_le (inf_le_left.trans inf_le_left)

theorem z_centralizes_orbit_images
    (hPSz : CFSG.RankThree.PartTwo.KFacts.KPSz) (hK8 : K8Cat)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hA27 : Nat.card A = 27) (hZA : zSub P c.L ≤ A)
    (hAPL : A ≤ P ⊓ c.L) (ha : a ∈ A) (haZ : a ∉ zSub P c.L)
    (hP2 : IsTripleCover (perfectCoreL c a ⧸ CFSG.Open.pCore 2 ↥(perfectCoreL c a))
        (alternatingGroup (Fin 6)) ∧
      zSub P c.L ≤ perfectCoreL c a ∧
      ⁅perfectCoreL c a, zSub P c.L⁆ ≤
        CFSG.Open.pCoreOf 2 (perfectCoreL c a) ∧
      A ≤ Subgroup.closure ({a} : Set G) ⊔ perfectCoreL c a)
    (hP3 : CFSG.Open.pRank 7 (Subgroup.centralizer ({a} : Set G)) = 1)
    (hP5 : ∀ W : Subgroup G, W ≤ D.M → Group.IsPerfect ↥W → ¬ 3 ∣ Nat.card W →
      W ≤ CFSG.LocalAnalysis.RankThreeUC.centralizerOnQuotient D.M
        (CFSG.Open.pCoreOf 2 c.L) c.L)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a) (h3 : ¬ 3 ∣ Nat.card J)
    (h6 : (orbitConjugates (perfectCoreL c a) J).ncard = 6)
    (h7J : ¬ 7 ∣ Nat.card (J ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 J))
    (hS1 : ∀ z ∈ zSub P c.L, ∀ K ∈ orbitConjugates (perfectCoreL c a) J,
      z ∈ Subgroup.normalizer (K : Set G)) :
    ∀ K ∈ orbitConjugates (perfectCoreL c a) J,
      autThetaQuot (zSub P c.L) K = ⊥ :=
  z_centralizes_components_of_sylow c hPSz hP hJ h3 h6 h7J hS1

theorem card_perm_six_perfect {H : Subgroup (Equiv.Perm (Fin 6))}
    (hH : Group.IsPerfect H) (hne : H ≠ ⊥) :
    Nat.card H = 360 ∨ Nat.card H = 60 := by
  rcases CFSG.RankThree.PartTwo.Sec4.Census.perfect_perm_six hH hne with hA6 | hne5
  · left
    rw [hA6, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  · right
    obtain ⟨e5⟩ := hne5
    rw [Nat.card_congr e5.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num

theorem not_normal_card_eighteen {X : Type} [Group X] [Finite X]
    (N : Subgroup X) [hN : N.Normal]
    (hsimple : IsSimpleGroup (X ⧸ Subgroup.center X))
    (hZcard : Nat.card (Subgroup.center X) = 3) (hXcard : Nat.card X = 1080) :
    Nat.card N ≠ 18 := by
  intro hNcard
  classical
  let Z : Subgroup X := Subgroup.center X
  haveI hZn : Z.Normal := by
    change (Subgroup.center X).Normal
    exact Subgroup.normal_of_le_center le_rfl
  let q : X →* X ⧸ Z := QuotientGroup.mk' Z
  let Nbar : Subgroup (X ⧸ Z) := N.map q
  have hNbarNormal : Nbar.Normal := hN.map q (QuotientGroup.mk'_surjective Z)
  haveI : Nbar.Normal := hNbarNormal
  have hXZ : Nat.card (X ⧸ Z) = 360 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    rw [hXcard, hZcard] at h
    omega
  have hNbar_le : Nat.card Nbar ≤ Nat.card N := by
    let φ : ↥N →* X ⧸ Z := q.comp N.subtype
    have hφrange : φ.range = Nbar := by
      ext x
      constructor
      · rintro ⟨n, rfl⟩
        exact Subgroup.mem_map_of_mem q n.2
      · intro hx
        obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx
        exact ⟨⟨n, hn⟩, rfl⟩
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    have hquot : Nat.card (↥N ⧸ φ.ker) = Nat.card Nbar := by
      rw [← hφrange]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    rw [hquot] at hcard
    exact Nat.le_of_dvd (Nat.card_pos) ⟨Nat.card φ.ker, hcard⟩
  rcases hNbarNormal.eq_bot_or_eq_top with hbot | htop
  · have hNleZ : N ≤ Z := by
      intro x hx
      have hxbar : q x ∈ Nbar := Subgroup.mem_map_of_mem q hx
      rw [hbot] at hxbar
      have hx1 : q x = 1 := by simpa using hxbar
      exact (QuotientGroup.eq_one_iff x).mp (by simpa [q] using hx1)
    have hdvd : Nat.card N ∣ Nat.card Z := Subgroup.card_dvd_of_le hNleZ
    rw [hZcard, hNcard] at hdvd
    norm_num at hdvd
  · have hle : Nat.card (X ⧸ Z) ≤ Nat.card Nbar := by
      rw [htop]
      simp
    rw [hXZ] at hle
    rw [hNcard] at hNbar_le
    omega

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

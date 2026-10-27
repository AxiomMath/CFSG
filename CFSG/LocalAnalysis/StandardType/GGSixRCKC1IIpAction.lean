module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpLang
public import CFSG.LocalAnalysis.StandardType.GGLangNormalizer
public import CFSG.LocalAnalysis.StandardType.GGReverseMarking
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGPsiInnerDiagOfMarking
public import CFSG.LocalAnalysis.StandardType.GGLieOddCover
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFAt
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeAssemblyHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutCore
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgCore
public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinctShapes
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeTransvOmegaAut
public import CFSG.HardMathSupport.Dickson.Bal207.OrthInnerField
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridge
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.E6BadLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151DiagDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeD4ThreeHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6KernelExitFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcAdj
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcInnerD4FixMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamChar2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpModelPairedMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthPairMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeCompDescIndSymp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthModelAnalysis
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthCatCatalogue
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthAsmPlus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthAsmMinus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriAct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriLang
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeLinStatedInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeReeF4LargeRFHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6CompAct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6Conn
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeUniInner
public import CFSG.Quasithin.Background.B3ThreeModel
public import CFSG.Quasithin.Background.B3ThreeStruct
public import CFSG.Quasithin.Background.G2Omega4PlusModule
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompO
public import CFSG.Quasithin.EmptyFaithful.R3c19B
public import CFSG.Quasithin.EmptyFaithful.S143FF
public import CFSG.Quasithin.EmptyFaithful.S143Final
public import CFSG.Quasithin.EmptyFaithful.S143HD
public import CFSG.Quasithin.EmptyFaithful.S143IG
public import CFSG.Quasithin.EmptyFaithful.S143JB
public import CFSG.Quasithin.EmptyFaithful.S143KO
public import CFSG.Quasithin.EmptyFaithful.S143KP
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15421
public import CFSG.RankThree.PartOne.N143.HighEvenU

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.StandardType.LieCore
  CFSG.ComponentClassification.PerfectCentralQuotient
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.PerfectAutomorphisms
  CFSG.GroupActions
open CFSG.StandardType.RCKRP
open CFSG.Open (StatedLieTag)
open CFSG.StandardType.S2MathFi1035Pos (GGPosTag)
open scoped commutatorElement

theorem rckIIpAt_excFive_classicalModelIDAt_of_model
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ} {G₀ A B₁ D J L K : Subgroup X} {e : X}
    (ht : GGExcFive t) (hrow : GGSixRCKJRow .IIp J)
    (hcfg : RCKCompConfig t n f ψ p G₀ A B₁ D J L K e)
    {d : X} (hdD : d ∈ D) (hdN : d ∈ Subgroup.normalizer (K : Set X))
    {s : StatedLieTag} {m g : ℕ}
    (hLM : LieModel (↥K ⧸ Subgroup.center ↥K) s m 2 g)
    (hshape : (s = .PSL ∧ ((m = 4 ∧ g = 3) ∨ (6 ≤ m ∧ Even m ∧ g = 1))) ∨
      (s = .POmegaMinus ∧ 4 ≤ m ∧ g = 1) ∨
      (s = .POmegaPlus ∧ 5 ≤ m ∧ g = 1)) :
    RCKClassicalModelIDAt s K (Subgroup.zpowers d) := by
  classical
  have hcfg0 := hcfg
  obtain ⟨hGG, hodd, hp, hp2, hAel, hB1A, hDB1, hDc, hAnorm, hMark, hB1J, hB1inf,
    hp4, hA2, hrankA, hbot, hB1L, hMarkL, hJcomp, hoddJ, hLG0, hx, hnotD, hJcompL,
    hA6, heD, hene, hKcomp, hJK, hoddK⟩ := hcfg
  have hD_le_A : D ≤ A := hDB1.trans hB1A
  have hKG0 : K ≤ G₀ := hKcomp.1.trans inf_le_left
  have hKperf : commutator ↥K = ⊤ := hKcomp.2.2.1
  haveI : Group.IsPerfect ↥K := ⟨hKperf⟩

  obtain ⟨η, E', S, a, i, hηker, _, _, hE'torus, _, _, hE'1, _, hrootMem, hrd1, hap, _,
    hi_eq, hi_qs⟩ := rckIIpAt_excFive_lang_component ht hrow hcfg0
  let R' : Subgroup (ModGL (langTag t) GGL) :=
    rationalComponent S.ρ S.Γ (rootCharHom a) i
  have hR'image : (K.subgroupOf G₀).map η = R' := hi_eq
  have hQS : CFSG.IsQuasisimple ↥R' := hi_qs
  have hrootT : rootDiagUnit (langTag t) a ∈ S.D.torus := hE'torus hrootMem

  let ηK : ↥K →* ModGL (langTag t) GGL := η.comp (Subgroup.inclusion hKG0)
  have hηKrange : ηK.range = R' := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    exact hR'image
  let χ : ↥K →* ↥R' := ηK.codRestrict R' fun x => by
    rw [← hηKrange]
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
  have hχsurj : Function.Surjective χ := by
    intro r
    have hr : (r : ModGL (langTag t) GGL) ∈ ηK.range := by
      rw [hηKrange]
      exact r.2
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hr
    exact ⟨x, Subtype.ext hx⟩
  have hχker : χ.ker ≤ Subgroup.center ↥K := by
    intro x hx
    have hx1 : ηK x = 1 := by
      have hx' : χ x = 1 := MonoidHom.mem_ker.mp hx
      have hval := congrArg (fun r : ↥R' => (r : ModGL (langTag t) GGL)) hx'
      simpa [χ, ηK] using hval
    have hxG0 : (⟨x, hKG0 x.2⟩ : ↥G₀) ∈ Subgroup.center ↥G₀ := by
      have hInc : (Subgroup.inclusion hKG0) x = (⟨x, hKG0 x.2⟩ : ↥G₀) :=
        Subtype.ext (Subgroup.coe_inclusion hKG0 x)
      have hx1' : η ⟨x, hKG0 x.2⟩ = 1 := by
        rw [← hInc]
        simpa [ηK, MonoidHom.comp_apply] using hx1
      rw [← hηker]
      exact MonoidHom.mem_ker.mpr hx1'
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hc := Subgroup.mem_center_iff.mp hxG0 ⟨y, hKG0 y.2⟩
    exact congrArg (fun z : ↥G₀ => (z : X)) hc

  let eK : ↥K ⧸ Subgroup.center ↥K ≃* ↥R' ⧸ Subgroup.center ↥R' :=
    CFSG.SeitzReduction.F4Pilot.centerQuotientEquivOfSurjective χ hχsurj hχker
  have hLM_R : LieModel (↥R' ⧸ Subgroup.center ↥R') s m 2 g :=
    CFSG.Blueprint.LieModel.of_mulEquiv eK hLM
  have h360 : Nat.card (↥R' ⧸ Subgroup.center ↥R') ≠ 360 :=
    CFSG.Quasithin.H13.EvenOrd.card_ne_of_evenLieType
      CFSG.Quasithin.H13.EvenOrd.excl_360 ⟨s, m, g, hLM_R.admissible, hLM_R⟩

  have hspos : GGPosTag s := by
    rcases hshape with ⟨rfl, _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ <;> simp [GGPosTag]
  have hexctags : langTag t = .G2 ∨ langTag t = .F4 ∨ langTag t = .D4 ∨
      langTag t = .E6 ∨ langTag t = .E7 ∨ langTag t = .E8 := by
    rcases langTag_five t with h | h | h | h <;> rw [h] <;> simp
  have hnotG2 : langTag t ≠ .G2 := by
    rcases langTag_five t with h | h | h | h <;> rw [h] <;> simp
  have hG2guard : langTag t = .G2 → 4 ≤ S.D.q := fun h => absurd h hnotG2
  haveI : CharP GGL 2 := inferInstance
  have haPow : a ^ p = 1 := by
    funext j
    simpa using hap j
  have hrootPow : rootDiagUnit (langTag t) a ^ p = 1 := by
    rw [rootDiagUnit_pow, haPow, rootDiagUnit_one]

  have hMark0 := CFSG.StandardType.Legacy.largeEvenMarking_of_lieModel_centerQuot hKperf hLM
  obtain ⟨_, lab, hlab, hraw⟩ := hMark0
  obtain ⟨R, instR, I, F, hQ⟩ := CFSG.StandardType.largeEvenRawDatum_exists hraw
  haveI := instR
  obtain ⟨hs, hna, θ, htag, hrank, hchar, hdeg⟩ := hQ
  have hstits : s ≠ .Tits := by
    rintro rfl
    rcases hshape with ⟨h, _⟩ | ⟨h, _, _⟩ | ⟨h, _, _⟩
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact absurd h (by simp)
  have hnotD4 : ¬ (s = .POmegaPlus ∧ m = 4) := by
    rintro ⟨rfl, rfl⟩
    rcases hshape with ⟨h, _⟩ | ⟨h, _, _⟩ | ⟨h, hm, _⟩
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · omega
  have htits : lab.tag ≠ .twF4der := by
    obtain ⟨tag, r, k⟩ := lab
    intro h
    change tag = .twF4der at h
    subst tag
    have hs : s = .Tits := by
      rw [← htag]
      simp [markTag]
    exact hstits hs
  have hD4 : ¬ (lab.tag = .D ∧ lab.rank = 4) := by
    obtain ⟨tag, r, k⟩ := lab
    rintro ⟨rfl, rfl⟩
    have hsp : s = .POmegaPlus := by
      rw [← htag]
      simp [markTag]
    have hm4 : m = 4 := by
      rw [← hrank]
      simp [markRank]
    exact hnotD4 ⟨hsp, hm4⟩

  have hsubAll : CFSG.StandardType.LargeEvenLabelAll lab
      (CFSG.StandardType.LargeEvenSimpleGuard CFSG.StandardType.GGRawInnSubgroup) :=
    CFSG.LocalAnalysis.GLTheoremA.T171Sh.largeEvenLabelAll_innSubgroup hlab
  have hcommAll : CFSG.StandardType.LargeEvenLabelAll lab
      (CFSG.StandardType.LargeEvenSimpleGuard CFSG.StandardType.GGInndiagCommEq) :=
    CFSG.LocalAnalysis.GLTheoremA.T171Sh.largeEvenLabelAll_inndiagComm_charTwo
      hlab hchar htits hD4
  have hrawSub := hsubAll _ hraw
  have hrawBoth := hcommAll _ hrawSub

  have hrawT : CFSG.StandardType.LargeEvenRawDatum lab (fun R _ I F =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : ↥K ⧸ Subgroup.center ↥K ≃* R,
          ∀ b ∈ Subgroup.zpowers d, ∃ φ ∈ I,
            LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ) := by
    refine CFSG.StandardType.largeEvenRawDatum_mono ?_ hrawBoth
    rintro R _ I F ⟨⟨⟨hs, hna, θ, htag, hrank, hchar, hdeg⟩, hsubfun⟩, hcommfun⟩
    refine ⟨hs, hna, θ, ?_⟩
    obtain ⟨hmul, hinv, hinn⟩ := hsubfun hs hna
    have hcommEq := hcommfun hs hna
    obtain ⟨ad, hadE, hpartd⟩ := hE'1 d hdD
    have hdNG0 : d ∈ Subgroup.normalizer (G₀ : Set X) := hAnorm (hD_le_A hdD)
    intro b hb
    have hbN : b ∈ Subgroup.normalizer (K : Set X) := (Subgroup.zpowers_le.2 hdN) hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
    let y : ModGL (langTag t) GGL := ad ^ (-k)
    have hyE' : y ∈ E' := E'.zpow_mem hadE (-k)
    have hbu : d ^ (-k) = b⁻¹ := by
      rw [← hk]
      exact zpow_neg d k
    have hparty : GGLiePartner G₀ η (b⁻¹) y := by
      rw [← hbu]
      exact GGLiePartner.zpow hdNG0 hpartd (-k)
    have hyT : y ∈ S.D.torus := hE'torus hyE'
    have hyH : y ∈ torusGroup (langTag t) GGL := (mem_twistedTorusOf.1 hyT).1
    have hyZ : y ∈ torusGroup (langTag t) GGL ⊔
        rootSpan (langTag t) GGL (kernelRoots (rootCharHom a)) := Subgroup.mem_sup_left hyH
    have hyF : S.D.step y = y := by
      change (MulAut.conj S.D.n) (S.D.Φ y) = y
      rw [MulAut.conj_apply]
      exact (mem_twistedTorusOf.1 hyT).2
    obtain ⟨b', hb'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hyH
    have hb'T : rootDiagUnit (langTag t) b' ∈ S.D.torus := by
      rwa [hb'] at hyT
    have hyN : y ∈ Subgroup.normalizer (R' : Set (ModGL (langTag t) GGL)) := by
      rw [hb']
      exact CFSG.StandardType.LangRat.rootDiagUnit_mem_normalizer_rationalComponent
        S a b' hb'T i
    have hyStab : MulAut.conj y ∈ CFSG.GroupActions.subgroupStabAut R' :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hyN

    have hexcAction : CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥R'
        (CFSG.GroupActions.subgroupStabRestrict R' ⟨MulAut.conj y, hyStab⟩) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
          (↥R' ⧸ Subgroup.center ↥R') :=
      CFSG.LocalAnalysis.GLTheoremA.T171Sh.excKernelCompAction_holds
        (S := S) (p := p) (a := a) (y := y)
        (by norm_num : Nat.Prime 5) (by norm_num : (5 : ℕ) ≠ 2)
        hp hp2 hexctags hrootT hap hrootPow hrd1 hG2guard i hQS h360 hyZ hyF hyStab

    let α : MulAut ↥K := K.normalizerMonoidHom ⟨b⁻¹, Subgroup.inv_mem _ hbN⟩
    let γ : MulAut ↥R' :=
      CFSG.GroupActions.subgroupStabRestrict R' ⟨MulAut.conj y, hyStab⟩
    have hαγ : ∀ x : ↥K, γ (χ x) = χ (α x) := by
      intro x
      apply Subtype.ext
      change (MulAut.conj y) ((χ x : ↥R') : ModGL (langTag t) GGL) =
        ((χ (α x) : ↥R') : ModGL (langTag t) GGL)
      rw [MulAut.conj_apply]
      have hxval : ((α x : ↥K) : X) = b⁻¹ * (x : X) * b := by
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
      have hmemArgB : b⁻¹ * (x : X) * b ∈ G₀ := by
        rw [← hxval]
        exact hKG0 (α x).2
      have hmemArg : b⁻¹ * (x : X) * (b⁻¹)⁻¹ ∈ G₀ := by
        simpa [inv_inv] using hmemArgB
      have hpart := hparty ⟨x, hKG0 x.2⟩ hmemArg
      have hAB : (⟨b⁻¹ * (x : X) * (b⁻¹)⁻¹, hmemArg⟩ : ↥G₀) =
          ⟨α x, hKG0 (α x).2⟩ := by
        apply Subtype.ext
        change b⁻¹ * (x : X) * (b⁻¹)⁻¹ = ((α x : ↥K) : X)
        rw [inv_inv]
        exact hxval.symm
      have hχx : ((χ x : ↥R') : ModGL (langTag t) GGL) = η ⟨x, hKG0 x.2⟩ := rfl
      have hχαx : ((χ (α x) : ↥R') : ModGL (langTag t) GGL) =
          η ⟨α x, hKG0 (α x).2⟩ := rfl
      rw [hχx, hχαx, ← hpart]
      exact congrArg η hAB
    have hmemR : CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥R' γ ∈
        CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
          (↥R' ⧸ Subgroup.center ↥R') := hexcAction
    have hmemK : CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K α ∈
        CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
          (↥K ⧸ Subgroup.center ↥K) :=
      (CFSG.ComponentClassification.PerfectCentralQuotient.centerQuotientHom_mem_innAutDerived_iff_of_surjective
          (π := χ) (hπ := hχsurj) (hker := hχker) (α := α) (γ := γ) hαγ).1 hmemR
    have hmemCongr : MulAut.congr θ
        (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K α) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived R :=
      (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr θ).2 hmemK
    have hmemG : MulAut.congr θ
        (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K α) ∈
        CFSG.StandardType.ggInndiag R I := by
      rw [hcommEq, CFSG.StandardType.ggInndiagComm_eq_innAutDerived]
      exact hmemCongr
    have hmemI : MulAut.congr θ
        (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K α) ∈ I :=
      (CFSG.StandardType.ggL45_mem_ggInndiag_iff hmul hinv hinn).1 hmemG

    refine ⟨MulAut.congr θ
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K α), hmemI, ?_⟩
    intro l l' hll'
    have hαl : α l = l' := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
      exact hll'.symm
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    have hstep : CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K α
        ((l : ↥K ⧸ Subgroup.center ↥K)) =
        ((α l : ↥K) : ↥K ⧸ Subgroup.center ↥K) :=
      CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk α l
    rw [hstep, hαl]

  have hmark : CFSG.StandardType.LargeEvenMarking ↥K
      (fun _ _ _ I _ θ => ∀ b ∈ Subgroup.zpowers d, ∃ φ ∈ I,
        LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ) :=
    ⟨hKperf, lab, hlab, hrawT⟩

  have hcover := CFSG.StandardType.LieOddCover.ggLieOddCover_holds
  obtain ⟨ψK0, hψ0surj, hψ0ker⟩ :=
    hcover.1 s m g hspos hLM.admissible ↥K hKperf hoddK hLM
  let ψK : (ggU s m g).K →* X := K.subtype.comp ψK0
  have hψrange : ψK.range = K := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hψ0surj, Subgroup.map_top,
      Subgroup.range_subtype]
  have hψker : ψK.ker ≤ Subgroup.center (ggU s m g).K := by
    rw [MonoidHom.ker_comp_of_injective ψK0 K.subtype K.subtype_injective]
    exact hψ0ker
  have hbnRank : 3 ≤ bnRank s m := by
    rcases hshape with ⟨rfl, hm⟩ | ⟨rfl, hm, _⟩ | ⟨rfl, hm, _⟩
    · rcases hm with ⟨rfl, rfl⟩ | ⟨hm, _, _⟩
      · simp [bnRank]
      · simp only [bnRank]
        omega
    · simp only [bnRank]
      omega
    · simp only [bnRank]
      omega
  have hrankD : 2 ≤ (ggU s m g).D.rank :=
    CFSG.StandardType.two_le_lieUniversal_rank s m 2 g Nat.prime_two hLM.admissible hbnRank
  have hpres : GGPresentsG0 K (ggU s m g).D s m g ψK :=
    ⟨⟨hLM.admissible, hrankD⟩, ⟨hψrange, hψker⟩, hKperf, hLM⟩

  have hBN : Subgroup.zpowers d ≤ Subgroup.normalizer (K : Set X) :=
    Subgroup.zpowers_le.2 hdN
  exact ⟨m, g, ψK, hLM.admissible.2.1, hψrange, hψker,
    CFSG.StandardType.ggPsiInnerDiag_of_marking hpres hmark hBN⟩

section OrthogonalTwo

theorem exists_orthogonal_two_innerDiag_presentation
    {X : Type} [Group X] [Finite X] {K B : Subgroup X} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hB : IsElemAbelian p B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hKperf : commutator ↥K = ⊤)
    (hoddK : Odd (Nat.card (Subgroup.center ↥K)))
    {s : StatedLieTag} {m : ℕ}
    (hLM : LieModel (↥K ⧸ Subgroup.center ↥K) s m 2 1)
    (hshape : (s = .POmegaMinus ∧ 4 ≤ m) ∨ (s = .POmegaPlus ∧ 5 ≤ m)) :
    ∃ ψ : (ggU s m 1).K →* X,
      ψ.range = K ∧ ψ.ker ≤ Subgroup.center (ggU s m 1).K ∧
        ∀ b ∈ B, GGPsiInnerDiag (ggU s m 1).D ψ b := by
  classical
  haveI : Finite ↥K := Subtype.finite
  have hspos : GGPosTag s := by
    rcases hshape with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [GGPosTag]
  have hcover := CFSG.StandardType.LieOddCover.ggLieOddCover_holds
  obtain ⟨ψK0, hψ0surj, hψ0ker⟩ :=
    hcover.1 s m 1 hspos hLM.admissible ↥K hKperf hoddK hLM
  let ψK : (ggU s m 1).K →* X := K.subtype.comp ψK0
  have hψrange : ψK.range = K := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hψ0surj, Subgroup.map_top,
      Subgroup.range_subtype]
  have hψker : ψK.ker ≤ Subgroup.center (ggU s m 1).K := by
    rw [MonoidHom.ker_comp_of_injective ψK0 K.subtype K.subtype_injective]
    exact hψ0ker
  have hKperf_psi : commutator ↥ψK.range = ⊤ := hψrange.symm ▸ hKperf
  have hLM_psi : LieModel (↥ψK.range ⧸ Subgroup.center ↥ψK.range) s m 2 1 :=
    hψrange.symm ▸ hLM
  have hsclass : s ∈ classicalTags := by
    rcases hshape with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [classicalTags]
  have hSCM : CFSG.Open.StatedClassicalModel
      (↥ψK.range ⧸ Subgroup.center ↥ψK.range) s m 2 1 :=
    hLM_psi.statedClassicalModel hsclass
  refine ⟨ψK, hψrange, hψker, ?_⟩
  intro b hb
  have hbp : b ^ p = 1 := hB.2 b hb
  have hbN : b ∈ Subgroup.normalizer (K : Set X) := hBN hb
  have hbN_psi : b ∈ Subgroup.normalizer (ψK.range : Set X) := hψrange.symm ▸ hbN
  let α : MulAut ↥ψK.range :=
    (ψK.range).normalizerMonoidHom ⟨b⁻¹, Subgroup.inv_mem _ hbN_psi⟩
  let β : MulAut (↥ψK.range ⧸ Subgroup.center ↥ψK.range) :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥ψK.range α
  have hxpow : (⟨b⁻¹, Subgroup.inv_mem _ hbN_psi⟩ :
      Subgroup.normalizer (ψK.range : Set X)) ^ p = 1 := by
    apply Subtype.ext
    change (b⁻¹) ^ p = (1 : X)
    rw [inv_pow, hbp, inv_one]
  have hαpow : α ^ p = 1 := by
    change ((ψK.range).normalizerMonoidHom
      ⟨b⁻¹, Subgroup.inv_mem _ hbN_psi⟩) ^ p = 1
    rw [← map_pow, hxpow, map_one]
  have hβpow : β ^ p = 1 := by
    change (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom
      ↥ψK.range α) ^ p = 1
    rw [← map_pow, hαpow, map_one]
  have hβodd : Odd (orderOf β) :=
    Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hβpow)
  have hfinal : ∀ r : ↥ψK.range ⧸ Subgroup.center ↥ψK.range,
      MulAut.conj r = β → GGPsiInnerDiag (ggU s m 1).D ψK b := by
    intro r hβconj
    refine CFSG.StandardType.ggPsiInnerDiag_of_induces_conj
      (R := ↥ψK.range ⧸ Subgroup.center ↥ψK.range)
      (ggU s m 1).D ψK hKperf_psi (MulEquiv.refl _) hbN_psi (r := r) ?_
    intro l l' hll'
    have hαl : α l = l' := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
      exact hll'.symm
    have hstep : β (QuotientGroup.mk l) = QuotientGroup.mk (α l) :=
      CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk α l
    calc (MulAut.conj r) ((MulEquiv.refl _) (QuotientGroup.mk l))
        = (MulAut.conj r) (QuotientGroup.mk l) := rfl
      _ = β (QuotientGroup.mk l) := by rw [hβconj]
      _ = QuotientGroup.mk (α l) := hstep
      _ = (MulEquiv.refl _) (QuotientGroup.mk l') := by simp [hαl]
  rcases hshape with ⟨hs, _⟩ | ⟨hs, hm⟩
  · subst hs
    obtain ⟨r, hr⟩ :=
      CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.TransvW.OmegaMinusEight.exists_conj_of_odd_orderOf
        (G := ↥ψK.range ⧸ Subgroup.center ↥ψK.range) (m := m) hSCM β hβodd
    exact hfinal r hr.symm
  · subst hs
    have hinner : ∃ r : ↥ψK.range ⧸ Subgroup.center ↥ψK.range,
        β = MulAut.conj r := by
      by_contra h
      have hout : ∀ a : ↥ψK.range ⧸ Subgroup.center ↥ψK.range,
          MulAut.conj a ≠ β := by
        intro a ha
        exact h ⟨a, ha.symm⟩
      exact hp.ne_one (Nat.dvd_one.1
        (CFSG.HardMathSupport.Dickson.Bal207.OrthFix.orth_outer_dvd
          (S := ↥ψK.range ⧸ Subgroup.center ↥ψK.range)
          (t := .POmegaPlus) (n := m) (ℓ := 2) (f := 1) (p := p)
          (Or.inl rfl) hm hSCM hp hp2 hβpow hout))
    obtain ⟨r, hr⟩ := hinner
    exact hfinal r hr.symm

theorem rckClassicalModelIDAt_orthogonal_two_of_elemAbelian
    {X : Type} [Group X] [Finite X] {K B : Subgroup X} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hB : IsElemAbelian p B)
    (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hKperf : commutator ↥K = ⊤)
    (hoddK : Odd (Nat.card (Subgroup.center ↥K)))
    {s : StatedLieTag} {m : ℕ}
    (hLM : LieModel (↥K ⧸ Subgroup.center ↥K) s m 2 1)
    (hshape : (s = .POmegaMinus ∧ 4 ≤ m) ∨ (s = .POmegaPlus ∧ 5 ≤ m)) :
    RCKClassicalModelIDAt s K B := by
  obtain ⟨ψ, hψrange, hψker, hψid⟩ :=
    exists_orthogonal_two_innerDiag_presentation hp hp2 hB hBN hKperf hoddK hLM hshape
  exact ⟨m, 1, ψ, le_rfl, hψrange, hψker, hψid⟩

end OrthogonalTwo

end CFSG.StandardType.RCKC1

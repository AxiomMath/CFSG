module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrField
public import CFSG.LocalAnalysis.StandardType.GGNsq2QuotHyp
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixType
public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbr6Main
public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1
public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1Odd
public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrSixFrame
public import Certificates.Certificate3143
public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1Edge
public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrSixEdge
public import CFSG.LocalAnalysis.StandardType.GGQTwoDSelCore
public import CFSG.LocalAnalysis.StandardType.GGQTwoDGenAbsorb
import CFSG.LocalAnalysis.StandardType.GGNsq2QuotCover
import CFSG.LocalAnalysis.StandardType.GGNsq2Main
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthChart
import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameMain
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1InvFixQuot
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1InvFixU
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1InvFixO
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthModel
import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCBase
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1Final
import CFSG.LocalAnalysis.StandardType.GGQTwoDSevenPrelim
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1LocalU
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1LocalO
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthPair
import CFSG.LocalAnalysis.StandardType.GGNsq2QuotNorm
import CFSG.LocalAnalysis.StandardType.GGNsq2RankOne
import CFSG.LocalAnalysis.StandardType.GGQTwoDSelUnit
import CFSG.LocalAnalysis.StandardType.GGQTwoDSelOrth
import CFSG.LocalAnalysis.StandardType.GGQTwoDSelModuleOfB2
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1PrimeToThree
import CFSG.LocalAnalysis.StandardType.GGQTwoDSelBases

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {G : Type} [Group G] [Finite G]

theorem qtwoDL1_local_quot {p : ℕ} {B Bs X Z : Subgroup G} {Q : Type} [Group Q] [Finite Q]
    {f : ↥(Subgroup.normalizer (X : Set G)) →* Q}
    (hD : NsQuot.Datum p (Subgroup.normalizer (X : Set G)) f X Bs Z)
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {ψ : Su K 2 1 n →* Q}
    (hK : Nat.card K = 4) (h : GGNSLocalHyp p (NsQuot.img _ f B) (NsQuot.img _ f Bs) K 1 n ψ)
    (hrange : ψ.range = NsQuot.img _ f X)
    (hd : GGActsDiagonally (p := 2) (f := 1) ψ (NsQuot.img _ f Bs))
    {r r' : MulAut ↥Bs} (hrX : r ∈ ggAutomizer X Bs) (hr'X : r' ∈ ggAutomizer X Bs)
    (hr : GGIsReflection p r) (hr' : GGIsReflection p r') (hne : r * r' ≠ r' * r) :
    216 ≤ Nat.card ↥(ggRankTwoIn X Bs r r') := by
  have hmap := hD.map_automizer_eq hD.ZL hD.LN
  have hrQ : MulAut.congr hD.tau r ∈ ggAutomizer (NsQuot.img _ f X) (NsQuot.img _ f Bs) := by
    rw [← hmap]
    exact ⟨r, hrX, rfl⟩
  have hr'Q : MulAut.congr hD.tau r' ∈ ggAutomizer (NsQuot.img _ f X) (NsQuot.img _ f Bs) := by
    rw [← hmap]
    exact ⟨r', hr'X, rfl⟩
  have hneQ : MulAut.congr hD.tau r * MulAut.congr hD.tau r' ≠
      MulAut.congr hD.tau r' * MulAut.congr hD.tau r := by
    intro h'
    apply hne
    apply (MulAut.congr hD.tau).injective
    rw [map_mul, map_mul]
    exact h'
  exact (qtwoDL1_local_unit hK h hrange hd hrQ hr'Q ((ggIsReflection_congr_iff hD.tau r).2 hr)
    ((ggIsReflection_congr_iff hD.tau r').2 hr') hneQ).trans (hD.card_rankTwoIn_img_le r r')

theorem qtwoDNbr_jlabel_quot {B Bs L D J : Subgroup G} {x : G} (hcfg : GGConfig 3 B Bs x L D J)
    {Q : Type} [Group Q] [Finite Q] {f : ↥(Subgroup.normalizer (L : Set G)) →* Q}
    {Z : Subgroup G} (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs Z)
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {ψ : Su K 2 1 n →* Q}
    (hKcard : Nat.card K = 4) (hker : ψ.ker ≤ Subgroup.center (Su K 2 1 n))
    (hrange : ψ.range = NsQuot.img _ f L)
    (hdiag : GGActsDiagonally (p := 2) (f := 1) ψ (NsQuot.img _ f Bs)) :
    ∃ t : ℕ, 4 ≤ t ∧ LieModel (↥J ⧸ Subgroup.center ↥J) .PSU t 2 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by rw [hKcard]; norm_num
  obtain ⟨y, hy, hyx, -, hJy⟩ := qTwoNbrA_exists_y hcfg.1 hcfg.2.1 hcfg.2.2
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) := hD.BsN
  have hψL : ∀ s : Su K 2 1 n, ψ s ∈ NsQuot.img _ f L := fun s => by
    rw [← hrange]
    exact MonoidHom.mem_range.mpr ⟨s, rfl⟩
  let πSU : Su K 2 1 n →* ↥(NsQuot.img _ f L) := ψ.codRestrict _ hψL
  have hπ_surj : Function.Surjective πSU := by
    intro l
    obtain ⟨s, hs⟩ : (l : Q) ∈ ψ.range := by
      rw [hrange]
      exact l.2
    exact ⟨s, Subtype.ext hs⟩
  have hπ_ker : πSU.ker ≤ Subgroup.center (Su K 2 1 n) := by
    intro s hs
    apply hker
    rw [MonoidHom.mem_ker] at hs ⊢
    exact congrArg Subtype.val hs
  let c : ↥L →* ↥(NsQuot.img _ f L) := hD.fL
  have hc_surj : Function.Surjective c := hD.fL_surjective
  have hc_ker : c.ker ≤ Subgroup.center ↥L := fun l hl =>
    hD.mem_center_of_mem ((hD.fL_eq_one_iff l).1 hl)
  let ι : ↥Bs →* ↥(Subgroup.normalizer ((NsQuot.img _ f L : Subgroup Q) : Set Q)) :=
    (f.comp (Subgroup.inclusion hD.BsN)).codRestrict _
      fun b => hD.f_mem_normalizer_img hN b.2
  let ρ : ↥Bs →* MulAut ↥(NsQuot.img _ f L) :=
    (NsQuot.img _ f L).normalizerMonoidHom.comp ι
  have hρ : ∀ (b : ↥Bs) (l : ↥L), c (ggGamma L hN b l) = ρ b (c l) := fun b l =>
    Subtype.ext (by
      have e : (⟨((ggGamma L hN b l : ↥L) : G), hD.LN (ggGamma L hN b l).2⟩ :
            ↥(Subgroup.normalizer (L : Set G))) =
          ⟨(b : G), hD.BsN b.2⟩ * ⟨(l : G), hD.LN l.2⟩ * ⟨(b : G), hD.BsN b.2⟩⁻¹ := rfl
      change f ⟨((ggGamma L hN b l : ↥L) : G), hD.LN (ggGamma L hN b l).2⟩ =
        f ⟨(b : G), hD.BsN b.2⟩ * f ⟨(l : G), hD.LN l.2⟩ * (f ⟨(b : G), hD.BsN b.2⟩)⁻¹
      rw [e, map_mul, map_mul, map_inv])
  have hne := qTwoNbrA_rho_ne_one hcfg.1 hcfg.2.1 hN c hc_surj hc_ker ρ hρ hy hyx
  have hM := qTwoNbrA_image_isComponentOf hN c hc_surj hc_ker ρ hρ hy hJy
  have hdg : ∃ g : GL (Fin n) K, ggIsDiagMat g ∧ ∀ u : Su K 2 1 n, ∃ u' : Su K 2 1 n,
      (u' : GL (Fin n) K) = g * (u : GL (Fin n) K) * g⁻¹ ∧ ρ ⟨y, hy⟩ (πSU u) = πSU u' := by
    obtain ⟨g, hgd, hgi⟩ :=
      hdiag (f ⟨y, hD.BsN hy⟩) (NsQuot.mem_img.2 ⟨⟨y, hD.BsN hy⟩, hy, rfl⟩)
    refine ⟨g, hgd, fun u => ?_⟩
    obtain ⟨u', hu'mat, hu'act⟩ := hgi.2 u
    refine ⟨u', hu'mat, Subtype.ext ?_⟩
    change f ⟨y, hD.BsN hy⟩ * ψ u * (f ⟨y, hD.BsN hy⟩)⁻¹ = ψ u'
    exact hu'act
  obtain ⟨t, δ, ht, hδ, hφδ⟩ := qTwoNbrA_diag_aut hF πSU hdg
  set φ := πSU.comp (qTwoNbrRec_suEquiv hF n).symm.toMonoidHom with hφ
  have hφsurj : Function.Surjective φ :=
    hπ_surj.comp (qTwoNbrRec_suEquiv hF n).symm.surjective
  have hφker : φ.ker ≤ Subgroup.center ↥(unitarySU 2 1 K n) := by
    intro w hw
    have h1 : (qTwoNbrRec_suEquiv hF n).symm w ∈ πSU.ker := hw
    have h2 := hπ_ker h1
    have h3 : w ∈ (Subgroup.center (Su K 2 1 n)).map
        (qTwoNbrRec_suEquiv hF n).toMonoidHom :=
      ⟨_, h2, by simp⟩
    rwa [show (Subgroup.center (Su K 2 1 n)).map (qTwoNbrRec_suEquiv hF n).toMonoidHom =
        Subgroup.center ↥(unitarySU 2 1 K n) from
      Subgroup.map_center_eq (qTwoNbrRec_suEquiv hF n)] at h3
  obtain ⟨S, hS4, hSm, hMS⟩ := qTwoNbrA_block_of_diag hF φ hφsurj hφker hne ht hδ hφδ hM
  obtain ⟨hLie, -⟩ := qTwoNbrA_block_model hF φ hφker hS4 hSm
  rw [← hMS] at hLie
  have hJL : J ≤ L := hJy.1.trans inf_le_left
  obtain ⟨⟨e⟩, -⟩ := qTwoNbrA_center_quot_of_component hJL c hc_ker hJy
  exact ⟨S.card, hS4, LieModel.of_mulEquiv e.symm hLie⟩

theorem qtwoDNbr_jlabel_quot' {B Bs L D J : Subgroup G} {x : G} (hcfg : GGConfig 3 B Bs x L D J)
    {Q : Type} [Group Q] [Finite Q] {f : ↥(Subgroup.normalizer (L : Set G)) →* Q}
    {Z : Subgroup G} (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs Z)
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {ψ : Su K 2 1 n →* Q}
    (hKcard : Nat.card K = 4) (hker : ψ.ker ≤ Subgroup.center (Su K 2 1 n))
    (hrange : ψ.range = NsQuot.img _ f L)
    (hdiag : GGActsDiagonally (p := 2) (f := 1) ψ (NsQuot.img _ f Bs)) :
    ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧
      GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) ∧ labJ.n = 1 ∧ labJ.tag ≠ .A ∧
        (labJ.tag = .twD → labJ.rank ≠ 2) := by
  obtain ⟨t, ht, hJ⟩ := qtwoDNbr_jlabel_quot hcfg hD hKcard hker hrange hdiag
  refine ⟨⟨.twA, t - 1, 1⟩, ?_, qTwoNbrA_hasLabel_of_lieModel ht hJ, rfl,
    by show LargeEvenLieTag.twA ≠ LargeEvenLieTag.A; decide,
    fun h => absurd h (by show ¬ LargeEvenLieTag.twA = LargeEvenLieTag.twD; decide)⟩
  refine ⟨le_refl 1, ?_, ?_⟩
  · change 2 ≤ t - 1
    omega
  · intro h
    change t - 1 = 2 at h
    omega

theorem qtwoD6_chartL_or_u62
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    (e' : Fin 6 ≃ ι) (hM : M = (ggCoxeterMatrixD 6).reindex e') :
    QTwoDL1Chart p B Bs L ∨
      GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs L := by
  by_cases hL : qtwoOrthL G L 𝒦
  · obtain ⟨Φ, hF, h5, hZ⟩ := qtwoDL1Chart_orth_L_on (R := fun m => m = 6)
      (ggQTwoFrameInput_of_inputs (fun m hm => by omega) ggLabelRigidInput_holds hTBF hWI)
      hcfg 6 e' rfl (by norm_num) hM hL
    exact Or.inl (Or.inr ⟨Φ, hF, h5, hZ⟩)
  rcases ggQTwoDUnit_memberUnitary_L_or_u62 ggLabelRigidInput_holds hTBF hcfg e' (by norm_num) hM
      hL with hU | ⟨-, hmark⟩
  · obtain ⟨F0, iF, iFin, iC, ψ, ε, h⟩ :=
      ggQTwoDUnit_base_of_member hTBF hWI hcfg e' (by norm_num) hM hU
    exact Or.inl (Or.inl ⟨F0, iF, iFin, iC, 6, ψ, h.card_field, h.hyp, h.range, h.diag,
      h.card_bs_eq (by norm_num)⟩)
  · exact Or.inr hmark

section Or

theorem GGQTwoL1InputOn.or {R R' : ℕ → Prop} (h : GGQTwoL1InputOn R) (h' : GGQTwoL1InputOn R') :
    GGQTwoL1InputOn fun m => R m ∨ R' m := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM
  rcases hm with hm | hm
  · exact h G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM
  · exact h' G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM

end Or

section Six

theorem qtwoD6_jlabel (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hOJ : GGQTwoDOrthJInput)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hcfg : GGQTwoDCfg 3 B Bs x L D J 𝒦 M e) (e' : Fin 6 ≃ ι)
    (hM : M = (ggCoxeterMatrixD 6).reindex e') :
    ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧
      GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) ∧ labJ.n = 1 ∧ labJ.tag ≠ .A ∧
        (labJ.tag = .twD → labJ.rank ≠ 2) := by
  rcases qtwoD6_chartL_or_u62 hTBF hWI hcfg e' hM with hch | hmk
  · exact qtwoDNbr_jlabel hOJ hcfg.1 hch
  · obtain ⟨-, K, _, _, _, hK, Q, _, _, f, ψ, hD, hrange, hhyp, hdiag, -⟩ :=
      ggQTwoDUnitSix_quotFrame hcfg.1 hmk
    exact qtwoDNbr_jlabel_quot' hcfg.1.1.1 hD hK hhyp.ker hrange hdiag

theorem qtwoD6_invFix (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hRM : GGQTwoRMInputOn fun m => m = 6) (hTCJ : GGTCJKnown) (hLB : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) (hSel : GGQTwoDSelModuleInputOn fun m => m = 6)
    (hOJ : GGQTwoDOrthJInput) (hTw : GGQTwoDSixTwE6InputOn fun m => m = 6)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (e' : Fin 6 ≃ ι)
    (hM : M = (ggCoxeterMatrixD 6).reindex e') (hBBs : B = Bs) :
    QTwoDL1InvFix p B Bs x L D J := by
  intro X hX t htC htN ht2
  have hp := (ggRouteCfg_prime hcfg.1).1
  have hp3 : p = 3 := by
    obtain ⟨r, hr, hrc, h6⟩ := hcfg.2.2.2.2
    exact ggQTwo_p_eq_three hcfg.1 M e hcfg.2.2.2.1 hr hrc h6
  subst hp3
  have hroute : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦 := hcfg.1
  have hconf : GGConfig 3 B Bs x L D J := hroute.1.1
  obtain ⟨β, hβ⟩ := hSel G 3 B Bs x L D J 𝒦 ι M e hcfg 6 e' rfl hM
  have hcard : Nat.card ↥Bs = 3 ^ 6 := card_bs_of_module β
  have hbase := qtwoD6_chartL_or_u62 hTBF hWI hcfg e' hM
  have hJlab := qtwoD6_jlabel hTBF hWI hOJ hcfg e' hM
  rcases hX with rfl | ⟨y, hy⟩
  · rcases hbase with hch | hmk
    · rcases hch with ⟨K, _, _, _, n, ψ, hK, h, hrange, hd, hfull⟩ | ⟨Φ, hF, h5, hZ⟩
      · exact qtwoDL1_invFix_unit hK h hrange hd hfull htC htN ht2
      · exact qtwoDL1_invFix_orth qtwoDL1OrthModel_holds hp Φ hF h5 hZ htC htN ht2
    · obtain ⟨-, K, _, _, _, hK, Q, _, _, f, ψ, hD, hrange, hhyp, hdiag, -⟩ :=
        ggQTwoDUnitSix_quotFrame hroute hmk
      refine hD.mem_centralizer_of_chart ⟨qTwoLMFrameC_perfect hconf.1⟩ hK hhyp hrange hdiag ?_
        htC htN ht2
      subst hBBs
      have h3 := hhyp.cent
      rw [hrange] at h3
      rw [hD.card_img le_rfl, hcard, h3]
      norm_num
  · rcases qtwoDNbr6_chart4_or (R := fun m => m = 6) (fun m hm => by omega) hRM hTCJ hLB hPJ hSel
        hTw hcfg e' rfl hM hJlab hy with hch | ⟨-, -, h5⟩
    · rcases hch with ⟨K, _, _, _, n, ψ, hK, h, hrange, hd, hfull⟩ | ⟨Φ, hF, h4, hlt, hZ⟩
      · exact qtwoDL1_invFix_unit hK h hrange hd hfull htC htN ht2
      · rcases Nat.lt_or_ge Φ.r 5 with hr | h5
        · exact absurd hBBs (hlt (by omega)).ne
        · exact qtwoDL1_invFix_orth qtwoDL1OrthModel_holds hp Φ hF h5 hZ htC htN ht2
    · obtain ⟨-, ⟨Φ⟩⟩ := ggQTwoDNbrSix_signedFrame_of_sel hcfg e' hM β hβ hy h5 hBBs
        (hRM G 3 B Bs x L D J 𝒦 ι M e hcfg 6 e' rfl hM y X hy)
      exact Φ.mem_centralizer htC htN ht2

theorem ggQTwoDL1InvFixInputOn_six (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hRM : GGQTwoRMInputOn fun m => m = 6) (hTCJ : GGTCJKnown) (hLB : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) (hSel : GGQTwoDSelModuleInputOn fun m => m = 6)
    (hOJ : GGQTwoDOrthJInput) (hTw : GGQTwoDSixTwE6InputOn fun m => m = 6) :
    GGQTwoDL1InvFixInputOn fun m => m = 6 := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM hBBs
  subst hm
  exact qtwoD6_invFix hTBF hWI hRM hTCJ hLB hPJ hSel hOJ hTw hcfg e' hM hBBs

theorem ggQTwoL1InputOn_six (hNonc : GGLNoncyclicInput) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) (hRM : GGQTwoRMInputOn fun m => m = 6) (hTCJ : GGTCJKnown)
    (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hSel : GGQTwoDSelModuleInputOn fun m => m = 6) (hOJ : GGQTwoDOrthJInput)
    (hTw : GGQTwoDSixTwE6InputOn fun m => m = 6) :
    GGQTwoL1InputOn fun m => m = 6 :=
  ggQTwoL1Input_of_invFix hNonc hLB hPJ
    (ggQTwoDL1InvFixInputOn_six hTBF hWI hRM hTCJ hLB hPJ hSel hOJ hTw)

theorem ggQTwoL1InputOn_fiveSix (hNonc : GGLNoncyclicInput) (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) (hRM : GGQTwoRMInputOn fun m => m = 6) (hTCJ : GGTCJKnown)
    (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hSel : GGQTwoDSelModuleInputOn fun m => m = 6) (hOJ : GGQTwoDOrthJInput)
    (hTw : GGQTwoDSixTwE6InputOn fun m => m = 6) :
    GGQTwoL1InputOn fun m => m = 5 ∨ m = 6 :=
  (ggQTwoL1InputOn_five hLB hPJ hTBF hWI).or
    (ggQTwoL1InputOn_six hNonc hTBF hWI hRM hTCJ hLB hPJ hSel hOJ hTw)

theorem qtwoD6_edgeBase (hNonc : GGLNoncyclicInput)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hRM : GGQTwoRMInputOn fun m => m = 6)
    (hTCJ : GGTCJKnown) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hSel : GGQTwoDSelModuleInputOn fun m => m = 6) (hOJ : GGQTwoDOrthJInput)
    (hTw : GGQTwoDSixTwE6InputOn fun m => m = 6)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (e' : Fin 6 ≃ ι)
    (hM : M = (ggCoxeterMatrixD 6).reindex e') :
    ∃ r₀ ∈ ggCoxRefl M e, ∃ r₀' ∈ ggCoxRefl M e, r₀ * r₀' ≠ r₀' * r₀ ∧
      Nat.card ↥(ggRankTwo Bs r₀ r₀') ≤ 216 := by
  have hfix6 := ggQTwoDL1InvFixInputOn_six hTBF hWI hRM hTCJ hLB hPJ hSel hOJ hTw
  rcases qtwoD6_chartL_or_u62 hTBF hWI hcfg e' hM with hch | hmk
  · exact qtwoDL1_edgeBase_of_chartL hNonc hLB hPJ qtwoDL1OrthModel_holds hfix6 hcfg
      (m := 6) rfl hM hch
  have hp3 : p = 3 := by
    obtain ⟨r, hr, hrc, h6⟩ := hcfg.2.2.2.2
    exact ggQTwo_p_eq_three hcfg.1 M e hcfg.2.2.2.1 hr hrc h6
  subst hp3
  have hroute : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦 := hcfg.1
  have hconf : GGConfig 3 B Bs x L D J := hroute.1.1
  have hodd := qtwoDL1_odd_of_cfg hNonc hLB hPJ hfix6 hcfg (m := 6) rfl hM
  obtain ⟨β, hβ⟩ := hSel G 3 B Bs x L D J 𝒦 ι M e hcfg 6 e' rfl hM
  obtain ⟨-, ⟨Φ⟩⟩ := ggQTwoDNbrSix_signedFrame_base_of_sel hcfg e' hM β hβ hmk
  have h01 : (0 : Fin 6) ≠ 1 := by decide
  have h12 : (1 : Fin 6) ≠ 2 := by decide
  have h02 : (0 : Fin 6) ≠ 2 := by decide
  have hS : LargeEvenSStar 3 B x L := hconf.1.2.2.2.2.2.2.1
  have hxB : x ∈ B := hS.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hconf.tableB_facts.2.2.2.1
  have hxH : x ∈ Φ.eqSub {0, 1, 2} := by
    refine Subgroup.mem_inf.2 ⟨hconf.2.1.1 hxB, ?_⟩
    simp only [Subgroup.mem_iInf]
    intro i _ j _
    obtain ⟨g, hgL, -, hact⟩ := mem_ggAutomizer_iff.mp (Φ.φ₀ (Equiv.swap i j)).2
    have hgx : g * x * g⁻¹ = x := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp (hLx hgL)]
      group
    refine ⟨⟨x, hconf.2.1.1 hxB⟩, ?_, rfl⟩
    change ((Φ.φ₀ (Equiv.swap i j) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) ⟨x, hconf.2.1.1 hxB⟩ =
      ⟨x, hconf.2.1.1 hxB⟩
    apply Subtype.ext
    rw [hact]
    exact hgx
  have hN : Subgroup.centralizer (Φ.eqSub {0, 1, 2} : Set G) ≤
      Subgroup.normalizer (L : Set G) := fun g hg =>
    mem_normalizer_of_sstar hS (hNonc G 3 B x L hconf.1) (by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Subgroup.mem_centralizer_iff.mp hg) x hxH).symm)
  have hcard := Φ.card_ambEdge_triple_le hodd h01 h12 h02 hN
  rw [Φ.ambEdge_triple] at hcard
  have h3 := qtwo_label_le_three e' hM
  exact ⟨_, ggCoxRefl_of_cfg hroute (ggAutomizerJoin_le_top L Bs 𝒦) hcfg.2.2.2.1 h3
      (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) (Φ.φ₀ (Equiv.swap 0 1)).2) (Φ.refl 0 1 h01),
    _, ggCoxRefl_of_cfg hroute (ggAutomizerJoin_le_top L Bs 𝒦) hcfg.2.2.2.1 h3
      (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) (Φ.φ₀ (Equiv.swap 1 2)).2) (Φ.refl 1 2 h12),
    Φ.refl_mul_ne h01 h12 h02, hcard⟩

theorem ggQTwoDL1EdgeBaseInputOn_six (hNonc : GGLNoncyclicInput)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hRM : GGQTwoRMInputOn fun m => m = 6)
    (hTCJ : GGTCJKnown) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hSel : GGQTwoDSelModuleInputOn fun m => m = 6) (hOJ : GGQTwoDOrthJInput)
    (hTw : GGQTwoDSixTwE6InputOn fun m => m = 6) :
    GGQTwoDL1EdgeBaseInputOn fun m => m = 6 := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM
  subst hm
  exact qtwoD6_edgeBase hNonc hTBF hWI hRM hTCJ hLB hPJ hSel hOJ hTw hcfg e' hM

theorem ggQTwoDL1EdgeLocalInputOn_six (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hRM : GGQTwoRMInputOn fun m => m = 6) (hTCJ : GGTCJKnown) (hLB : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) (hSel : GGQTwoDSelModuleInputOn fun m => m = 6)
    (hOJ : GGQTwoDOrthJInput) (hTw : GGQTwoDSixTwE6InputOn fun m => m = 6) :
    GGQTwoDL1EdgeLocalInputOn fun m => m = 6 := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM X hX r hrA hrC r' hr'A hr'C hne
  subst hm
  have hp3 : p = 3 := by
    obtain ⟨r, hr, hrc, h6⟩ := hcfg.2.2.2.2
    exact ggQTwo_p_eq_three hcfg.1 M e hcfg.2.2.2.1 hr hrc h6
  subst hp3
  have hrefl := ggCoxRefl_isReflection hcfg.2.2.2.1.2 hrC
  have hrefl' := ggCoxRefl_isReflection hcfg.2.2.2.1.2 hr'C
  rcases hX with rfl | ⟨y, hy⟩
  · rcases qtwoD6_chartL_or_u62 hTBF hWI hcfg e' hM with hch | hmk
    · rcases hch with ⟨K, _, _, _, n, ψ, hK, h, hrange, hd, -⟩ | ⟨Φ, hF, -, hZ⟩
      · exact qtwoDL1_local_unit hK h hrange hd hrA hr'A hrefl hrefl' hne
      · exact qtwoDL1_local_orth qtwoDL1OrthPair_holds Φ hF hZ hrA hr'A hrefl hrefl' hne
    · obtain ⟨-, K, _, _, _, hK, Q, _, _, f, ψ, hD, hrange, hhyp, hdiag, -⟩ :=
        ggQTwoDUnitSix_quotFrame hcfg.1 hmk
      exact qtwoDL1_local_quot hD hK hhyp hrange hdiag hrA hr'A hrefl hrefl' hne
  · rcases qtwoDNbr6_chart4_or (R := fun m => m = 6) (fun m hm => by omega) hRM hTCJ hLB hPJ hSel
        hTw hcfg e' rfl hM (qtwoD6_jlabel hTBF hWI hOJ hcfg e' hM) hy with
      hch | ⟨-, hBBs, h5⟩
    · rcases hch with ⟨K, _, _, _, n, ψ, hK, h, hrange, hd, -⟩ | ⟨Φ, hF, -, -, hZ⟩
      · exact qtwoDL1_local_unit hK h hrange hd hrA hr'A hrefl hrefl' hne
      · exact qtwoDL1_local_orth qtwoDL1OrthPair_holds Φ hF hZ hrA hr'A hrefl hrefl' hne
    · obtain ⟨β, hβ⟩ := hSel G 3 B Bs x L D J 𝒦 ι M e hcfg 6 e' rfl hM
      obtain ⟨-, ⟨Φ⟩⟩ := ggQTwoDNbrSix_signedFrame_of_sel hcfg e' hM β hβ hy h5 hBBs
        (hRM G 3 B Bs x L D J 𝒦 ι M e hcfg 6 e' rfl hM y X hy)
      exact qtwoDL1_local_quot Φ.datum Φ.card_K Φ.hyp Φ.range Φ.diag hrA hr'A hrefl hrefl' hne

theorem ggQTwoEdgeAmbientInputOn_six (hNonc : GGLNoncyclicInput)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hRM : GGQTwoRMInputOn fun m => m = 6)
    (hTCJ : GGTCJKnown) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hSel : GGQTwoDSelModuleInputOn fun m => m = 6) (hOJ : GGQTwoDOrthJInput)
    (hTw : GGQTwoDSixTwE6InputOn fun m => m = 6) :
    GGQTwoEdgeAmbientInputOn fun m => m = 6 :=
  ggQTwoEdgeAmbientInputOn_of_base_local (fun m hm => by omega)
    (ggQTwoDL1EdgeBaseInputOn_six hNonc hTBF hWI hRM hTCJ hLB hPJ hSel hOJ hTw)
    (ggQTwoDL1EdgeLocalInputOn_six hTBF hWI hRM hTCJ hLB hPJ hSel hOJ hTw)

theorem ggQTwoLGenRankTwoInputOn_six (hTBF : GGTBFixInput)
    (hWI : GGNbrInnerWeylInput) : GGQTwoLGenRankTwoInputOn fun m => m = 6 := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM
  subst hm
  have hp3 : p = 3 := by
    obtain ⟨r, hr, hrc, h6⟩ := hcfg.2.2.2.2
    exact ggQTwo_p_eq_three hcfg.1 M e hcfg.2.2.2.1 hr hrc h6
  subst hp3
  obtain ⟨β, hβ⟩ := ggQTwoDSelModuleInputOn_of_selectedModule (R := fun m => m = 6)
    (fun m hm => by omega) hTBF hWI G 3 B Bs x L D J 𝒦 ι M e hcfg 6 e' rfl hM
  by_cases hc : qtwoOrthL G L 𝒦
  · obtain ⟨Φ, hF, -, hZ⟩ := qtwoDL1Chart_orth_L_on (R := fun m => m = 6)
      (ggQTwoFrameInput_of_inputs (fun m hm => by omega) ggLabelRigidInput_holds hTBF hWI)
      hcfg 6 e' rfl (by norm_num) hM hc
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact qtwoLGen_of_orthChart rfl e' (by norm_num) hM β hβ Φ hF hZ
      (ggRouteCfg_isElemAbelian hcfg.1)
  rcases ggQTwoDUnit_memberUnitary_L_or_u62 ggLabelRigidInput_holds hTBF hcfg e' (by norm_num) hM
      hc with hU | ⟨-, hmark⟩
  · obtain ⟨F0, _, _, _, ψ, ε, hB⟩ :=
      ggQTwoDUnit_base_of_member hTBF hWI hcfg e' (by norm_num) hM hU
    exact qtwoLGen_of_unitaryBase e' (by norm_num) hM β hβ hB
  · obtain ⟨-, ⟨Φ⟩⟩ := ggQTwoDNbrSix_signedFrame_base_of_sel hcfg e' hM β hβ hmark
    have h3 := qtwo_label_le_three e' hM
    refine (le_of_eq Φ.eq_iSup_edge).trans (iSup₂_le fun T hT => ?_)
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 hT
    rw [Φ.edge_triple]
    have hrA := (Φ.φ₀ (Equiv.swap a b)).2
    have hr'A := (Φ.φ₀ (Equiv.swap b c)).2
    have hrC := ggCoxRefl_of_cfg hcfg.1 (ggAutomizerJoin_le_top L Bs 𝒦) hcfg.2.2.2.1 h3
      (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hrA) (Φ.refl a b hab)
    have hr'C := ggCoxRefl_of_cfg hcfg.1 (ggAutomizerJoin_le_top L Bs 𝒦) hcfg.2.2.2.1 h3
      (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hr'A) (Φ.refl b c hbc)
    exact le_iSup_of_le _ (le_iSup_of_le ⟨hrA, hrC⟩ (le_iSup_of_le _ (le_iSup_of_le ⟨hr'A, hr'C⟩
      (le_iSup_of_le (Φ.refl_mul_ne hab hbc hac) le_rfl))))

theorem ggQTwoSelLInputOn_six (hNonc : GGLNoncyclicInput)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hRM : GGQTwoRMInputOn fun m => m = 6)
    (hTCJ : GGTCJKnown) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hSel : GGQTwoDSelModuleInputOn fun m => m = 6) (hOJ : GGQTwoDOrthJInput)
    (hTw : GGQTwoDSixTwE6InputOn fun m => m = 6) :
    GGQTwoSelLInputOn fun m => m = 6 :=
  ggQTwoSelLInputOn_of_rankTwoGen (fun m hm => by omega)
    (ggQTwoEdgeAmbientInputOn_six hNonc hTBF hWI hRM hTCJ hLB hPJ hSel hOJ hTw)
    (ggQTwoLGenRankTwoInputOn_six hTBF hWI)

end Six

end CFSG.StandardType.QTwo

end

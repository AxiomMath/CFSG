module

import CFSG.LocalAnalysis.UniquenessCase.UC22R856TrialityAction

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest15Cases
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest15IntersectionCore
public import CFSG.LocalAnalysis.UniquenessCase.UC22R856NormalFour
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest15ComponentLift
import CFSG.LocalAnalysis.UniquenessCase.UC6R869NS
import CFSG.CGT.Foote82.D1Steps
import CFSG.CGT.Foote82.T66.BranchAGen
import CFSG.GroupTheory.PRankLeOfSylowLe
import CFSG.HardMathSupport.Foote.FamilyReduction.ClassicalFive
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Main
import CFSG.Adapters.LieModelOrders
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest15LinearThreeCenter
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest15LinearAlternating
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest15LinearLieThree
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest15LinearLieGeneric
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest15LinearSporadic


import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.DetExc
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest15LinearLieSeitz
public import CFSG.GroupTheory.PRankZeroOfPrimeNotDvd
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69R876

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)

variable {G : Type} [Group G] [Finite G]

@[expose] def Rest15NormReduced (D : Data G) (Ch : Choice2011 G) : Prop :=
  (3 ∉ D.sig → ∀ L Z : Subgroup G, PartOne.Section8.Loc876 D.M L Z →
    Z ∈ uniqueSet D.M) →
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ¬ S21_3Closed L → ¬ S21_3Closed2 L →
    ¬ S21_3ClosedZ L → ¬ S21_3ClosedCov D.M L → ¬ S21_3ClosedSpor D.M L →
    ¬ S21_3ClosedL2 L → ¬ S21_3ClosedTorus L → ¬ S21_3ClosedSmall D.M L → S21_3List L →
    (¬ D.M ≤ normalizer (L : Set G) → ∀ q : ℕ, q.Prime → q ≠ 2 →
      2 ≤ CFSG.Open.pRank q L → q ∣ Nat.card (center (Bar2 L))) →
    ¬ S21_3ClosedU3 L → ¬ S21_3ClosedTorusL3 L → ¬ S21_3ClosedTorus4 L →
    ¬ S21_3ClosedChar D.M L → ¬ S21_3ClosedU54 L → ¬ S21_3ClosedCharY D.M L →
    ¬ F08.Thin8 L → CFSG.Open.pRank 3 L = 2 →
    (IsStronglyPEmbedded 3 D.M → CFSG.Open.pRank 3 L ≤ 1) →
    (D.M ≤ normalizer (L : Set G)) →
    ∀ a ∈ c.B, (orderOf a).Prime →
      (∀ p ∈ D.sig,
        CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ D.M) ≤ 1) →
      (∀ r : ℕ, r.Prime → r ≠ 2 → ∀ Q : Subgroup G, Q ≤ L → IsPGroup r Q →
        2 ≤ CFSG.Open.pRank r Q → rankThreeGamma 1 r Q ≤ D.M) →
      (∀ H : Subgroup G, L ⊓ centralizer ((zpowers a : Subgroup G) : Set G) ≤ H →
        CFSG.Open.pRank 3 H ≤ 3) →
      (∀ H : Subgroup G, L ⊓ centralizer ((zpowers a : Subgroup G) : Set G) ≤ H →
        ¬ H ≤ D.M → pCoreOf 2 H = ⊥) →
      (∀ H : Subgroup G, L ⊓ centralizer ((zpowers a : Subgroup G) : Set G) ≤ H →
        relPPrimeCore 3 H ≤ D.M ∧ CFSG.fittingSubgroupOf H ≤ D.M) →
      (let X := CFSG.Quasithin.perfectCore
          (L ⊓ centralizer ((zpowers a : Subgroup G) : Set G));
        X ≤ L ⊓ centralizer ((zpowers a : Subgroup G) : Set G) ∧
          ⁅X, X⁆ = X ∧ X ⊔ pCoreOf 2 L = L ∧ CFSG.Open.IsQuasisimple (Bar2 X)) →
      (let X := CFSG.Quasithin.perfectCore
          (L ⊓ centralizer ((zpowers a : Subgroup G) : Set G));
        (IsSL3 (Bar2 X) 2 ∨ IsSU3 (Bar2 X) 3) →
        ∀ H : Subgroup G, L ⊓ centralizer ((zpowers a : Subgroup G) : Set G) ≤ H →
          H ≠ ⊤ → ¬ H ≤ D.M → pCoreOf 2 (H ⊓ D.M) = ⊥) →
      (∀ H : Subgroup G,
        L ⊓ centralizer ((zpowers a : Subgroup G) : Set G) ≤ H →
        pCoreOf 2 (H ⊓ D.M) = ⊥ →
        CFSG.Open.IsComponentOf
          (CFSG.Quasithin.perfectCore
            (L ⊓ centralizer ((zpowers a : Subgroup G) : Set G))) (H ⊓ D.M)) →
      ¬ CentralizesBar a L

theorem normal_subgroupOf_of_centerless_component_of_rank_le_three
    {X A : Subgroup G} (hX : IsComponentOf X A) (hZ : center X = ⊥)
    (hrX : 2 ≤ CFSG.Open.pRank 3 X) (hrA : CFSG.Open.pRank 3 A ≤ 3) :
    (X.subgroupOf A).Normal := by
  have hX' : CFSG.IsComponent (X.subgroupOf A) :=
    CFSG.CGT.Foote82.BranchAAux.isComponent_subgroupOf hX
  have e : (X.subgroupOf A) ≃* X := Subgroup.subgroupOfEquivOfLe hX.1
  have hc : center (X.subgroupOf A) = ⊥ := by
    have hmap := Subgroup.map_center_eq e
    rw [hZ] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 hmap
  apply CFSG.Quasithin.SteinbergBM.centerless_component_rank_forces_normality Nat.prime_three hX' hc
  have hrA' : CFSG.pRank 3 A ≤ 3 := by
    rwa [CFSG.SectionRank.pRank_coe_eq_openPRank]
  have hrX' : 2 ≤ CFSG.pRank 3 (X.subgroupOf A) := by
    rw [CFSG.pRank_congr_of_mulEquiv e 3]
    simpa only [CFSG.SectionRank.pRank_coe_eq_openPRank] using hrX
  omega

theorem rankThreeGamma_subgroupOf_le_of_le
    {P K M : Subgroup G} (hPK : P ≤ K) (hGamma : rankThreeGamma 1 3 P ≤ M) :
    rankThreeGamma 1 3 (P.subgroupOf K) ≤ M.subgroupOf K := by
  apply CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall
  intro R hRP hRr n hnR
  let Rg := R.map K.subtype
  have hRgP : Rg ≤ P := by
    have h := Subgroup.map_mono (f := K.subtype) hRP
    rwa [Subgroup.map_subgroupOf_eq_of_le hPK] at h
  have hRgr : 1 ≤ CFSG.Open.pRank 3 Rg := hRr.trans
    (CFSG.SectionRank.pRank_le_map (by norm_num) K.subtype K.subtype_injective R)
  have hnRg : (n : G) ∈ normalizer (Rg : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hnR ⊢
    have h := congrArg (Subgroup.map K.subtype) hnR
    have heq : K.subtype.comp (MulAut.conj n : K →* K) =
        (MulAut.conj (n : G) : G →* G).comp K.subtype := by
      ext x
      simp [MulAut.conj_apply]
    rw [Subgroup.map_map, heq] at h
    simpa only [Rg, Subgroup.map_map] using h
  exact hGamma
    (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hRgP hRgr hnRg)


theorem rest15_central_three_context
    {X H K P M : Subgroup G} (hX : IsComponentOf X (H ⊓ M))
    (hK : IsComponentOf K H) (hXK : X ≤ K)
    (hZ : Nat.card (center X) = 3)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P X)
    (hGamma : rankThreeGamma 1 3 P ≤ M) :
    let Z := (center X).map X.subtype;
    Nat.card Z = 3 ∧ Z ≤ P ∧ X ≤ centralizer (Z : Set G) ∧
      IsComponentOf X (K ⊓ centralizer (Z : Set G)) ∧
      rankThreeGamma 1 3 (P.subgroupOf K) ≤ M.subgroupOf K := by
  dsimp only
  let Z := (center X).map X.subtype
  have hZX : Z ≤ X := Subgroup.map_subtype_le _
  have hZcard : Nat.card Z = 3 := by
    rw [Subgroup.card_map_of_injective X.subtype_injective, hZ]
  have hZP : Z ≤ P := by
    have hZ3 : IsPGroup 3 (center X) := IsPGroup.of_card (n := 1) (by simpa using hZ)
    obtain ⟨S, hS⟩ := hP.exists_sylow_eq_subgroupOf
    have hle : center X ≤ (S : Subgroup X) := hZ3.le_sylow_of_normal S
    rw [hS] at hle
    have h := Subgroup.map_mono (f := X.subtype) hle
    rwa [Subgroup.map_subgroupOf_eq_of_le hP.le] at h
  have hXCZ : X ≤ centralizer (Z : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    rintro z ⟨c, hc, rfl⟩
    exact (congrArg Subtype.val ((Subgroup.mem_center_iff.1 hc) ⟨x, hx⟩)).symm
  have hzr : 1 ≤ CFSG.Open.pRank 3 Z := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup Z]
    exact CFSG.one_le_pRank_of_dvd_card Nat.prime_three (by rw [hZcard])
  have hNZ : normalizer (Z : Set G) ≤ M :=
    (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hZP hzr).trans hGamma
  have hCZ : K ⊓ centralizer (Z : Set G) ≤ H ⊓ M :=
    le_inf (inf_le_left.trans hK.1) (inf_le_right.trans ((centralizer_le_normalizer _).trans hNZ))
  have hcomp : IsComponentOf X (K ⊓ centralizer (Z : Set G)) :=
    CFSG.Assembly.isComponentOf_iff_open.1
      (CFSG.Assembly.IsComponentOf.of_le_of_le
        (CFSG.Assembly.isComponentOf_iff_open.2 hX) (le_inf hXK hXCZ) hCZ)
  exact ⟨hZcard, hZP, hXCZ, hcomp,
    rankThreeGamma_subgroupOf_le_of_le (hP.le.trans hXK) hGamma⟩


theorem rest15_central_three_position
    {X K : Subgroup G} (_hXK : X ≤ K)
    (hZ : Nat.card (center X) = 3)
    (hX : CFSG.Blueprint.LieModel (X ⧸ center X) .PSL 3 2 2 ∨
      CFSG.Blueprint.LieModel (X ⧸ center X) .PSU 3 2 3)
    (hCZ : IsComponentOf X
      (K ⊓ centralizer (((center X).map X.subtype : Subgroup G) : Set G))) :
    PartOne.Section8.K328.Pos K
      (((center X).map X.subtype).subgroupOf K) (X.subgroupOf K) := by
  let Z := (center X).map X.subtype
  have hZX : Z ≤ X := map_subtype_le _
  have hcomp : IsComponentOf X (centralizer (Z : Set G) ⊓ K) := by
    simpa only [inf_comm K] using hCZ
  exact PartOne.Section8.K328.pos_of_k328_hyps
    (by rw [card_map_of_injective X.subtype_injective]; exact hZ)
    hZX hcomp.1 (CFSG.Open.IsSubnormal.subgroupOf hcomp.2.1) hcomp.2.2 hZ hX

theorem rest15_false_of_central_three_centralizer_context
    {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (S : Setup4 G) {X H K P : Subgroup G}
    (hHtop : H ≠ ⊤) (hHr : CFSG.Open.pRank 3 H ≤ 3)
    (_hXcomp : CFSG.Open.IsComponentOf X (H ⊓ S.M))
    (hKcomp : CFSG.Open.IsComponentOf K H) (hXK : X ≤ K) (hKM : ¬ K ≤ S.M)
    (hZ : Nat.card (Subgroup.center X) = 3)
    (hX : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .PSL 3 2 2 ∨
      CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .PSU 3 2 3)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P X)
    (_hGamma : rankThreeGamma 1 3 P ≤ S.M)
    (_hZP : (center X).map X.subtype ≤ P)
    (hCZ : IsComponentOf X
      (K ⊓ centralizer (((center X).map X.subtype : Subgroup G) : Set G)))
    (hGammaK : rankThreeGamma 1 3 (P.subgroupOf K) ≤ S.M.subgroupOf K) : False := by
  have hKq := hKcomp.2.2
  have hKt : K ≠ ⊤ := fun h => hHtop (top_le_iff.mp (h ▸ hKcomp.1))
  have hKG := (hS.kProper.isKGroup K hKt).quotient (center K)
  have hft : genFittingFStar K = ⊤ := by
    rw [CFSG.Adapters.genFittingFStar_eq_foundations]
    exact CFSG.WholeGroup.generalizedFitting_eq_top_of_isQuasisimple
      (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hKq)
  let ef : genFittingFStar K ≃* K :=
    (MulEquiv.subgroupCongr hft).trans Subgroup.topEquiv
  have hqF : CFSG.Open.IsQuasisimple (genFittingFStar K) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv ef hKq
  let ec : (genFittingFStar K) ⧸ center (genFittingFStar K) ≃* K ⧸ center K :=
    QuotientGroup.congr _ _ ef (Subgroup.map_center_eq ef)
  have hKFG : CFSG.Open.IsKGroup
      (genFittingFStar K ⧸ center (genFittingFStar K)) :=
    CFSG.KCore.KGroupNonab.of_mulEquiv CFSG.Open.isCatalogGroup_isoInvariant hKG ec
  have hKr : CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup K]
    exact (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt hKcomp.1).trans hHr
  let Z : Subgroup K := ((center X).map X.subtype).subgroupOf K
  let X' : Subgroup K := X.subgroupOf K
  let P' : Subgroup K := P.subgroupOf K
  have hpos : PartOne.Section8.K328.Pos K Z X' :=
    rest15_central_three_position hXK hZ hX hCZ
  obtain ⟨hZc, hZX, hXC, hsub, hXq, hXc, hXm⟩ := hpos
  have hP' := PartOne.Section8.K328.isSylowOf_subgroupOf_of_le hXK hP
  have hInf : centralizer (Z : Set K) ⊓ genFittingFStar K = centralizer (Z : Set K) := by
    rw [hft]
    exact inf_eq_left.mpr le_top
  have hgen := PartOne.Section8.K328.k328_holds
    CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement K
    hqF hKFG hKr Z X' P' hZc hZX
    (by rw [hInf]; exact hXC)
    (by
      rw [hInf]
      exact hsub) hXq hXc hXm hP'
  rw [hgen] at hGammaK
  exact hKM fun k hk => hGammaK (mem_top (⟨k, hk⟩ : K))

section CentralThreeOvercomponent

theorem rest15_false_of_central_three_overcomponent
    {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (S : Setup4 G) {X H K P : Subgroup G}
    (hHtop : H ≠ ⊤) (hHr : CFSG.Open.pRank 3 H ≤ 3)
    (hXcomp : CFSG.Open.IsComponentOf X (H ⊓ S.M))
    (hKcomp : CFSG.Open.IsComponentOf K H) (hXK : X ≤ K) (hKM : ¬ K ≤ S.M)
    (hZ : Nat.card (Subgroup.center X) = 3)
    (hX : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .PSL 3 2 2 ∨
      CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .PSU 3 2 3)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P X)
    (hGamma : rankThreeGamma 1 3 P ≤ S.M) : False := by
  obtain ⟨_, hZP, _, hCZ, hGammaK⟩ :=
    rest15_central_three_context hXcomp hKcomp hXK hZ hP hGamma
  exact rest15_false_of_central_three_centralizer_context hS S hHtop hHr
    hXcomp hKcomp hXK hKM hZ hX hP hGamma hZP hCZ hGammaK

end CentralThreeOvercomponent

theorem rest15_false_of_linear_quotient_order
    {G : Type} [Group G] [Finite G] {X H K M : Subgroup G}
    (hXcomp : IsComponentOf X (H ⊓ M)) (hKcomp : IsComponentOf K H)
    (hXK : X ≤ K) (hKM : ¬ K ≤ M)
    (hX : CFSG.Blueprint.LieModel X .PSL 3 2 2)
    (hcard : Nat.card (K ⧸ center K) = 20160) : False := by
  have hXs : IsSimpleGroup X := hX.isSimpleGroup_of_mem_classicalTags (by decide)
  have : IsSimpleGroup X := hXs
  have hZX : center X = ⊥ := uc22p21k_center_eq_bot hXcomp.2.2
  let π := QuotientGroup.mk' (center K)
  let ι := Subgroup.inclusion hXK
  have hinj : Function.Injective (π.comp ι) :=
    quotient_center_inclusion_injective hXK hXcomp.2.2 hXs
  have hcX : Nat.card X = 20160 := by
    rw [hX.card_eq_lieOrd (by norm_num)]
    decide +kernel
  have hc : Nat.card (π.comp ι).range = Nat.card (K ⧸ center K) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hcX, hcard]
  have hr : (π.comp ι).range = ⊤ := Subgroup.eq_top_of_card_eq (π.comp ι).range hc
  have hm : (X.subgroupOf K).map π = ⊤ := by
    simpa only [ι, MonoidHom.range_comp, Subgroup.inclusion_range] using hr
  have : Group.IsPerfect K := ⟨hKcomp.2.2.1⟩
  have htop := CFSG.LieType.SeitzGeneration.eq_top_of_map_eq_top_of_perfect π
    (by rw [QuotientGroup.ker_mk']) hm
  have hKX : K ≤ X := by
    intro k hk
    have : (⟨k, hk⟩ : K) ∈ X.subgroupOf K := htop ▸ mem_top _
    exact this
  exact hKM (hKX.trans (hXcomp.1.trans inf_le_right))


theorem rest15_false_of_linear_psl_three_four_quotient
    {X H K M : Subgroup G}
    (hXcomp : IsComponentOf X (H ⊓ M)) (hKcomp : IsComponentOf K H)
    (hXK : X ≤ K) (hKM : ¬ K ≤ M)
    (hX : CFSG.Blueprint.LieModel X .PSL 3 2 2)
    (hmodel : CFSG.Blueprint.LieModel (K ⧸ center K) .PSL 3 2 2) : False := by
  apply rest15_false_of_linear_quotient_order hXcomp hKcomp hXK hKM hX
  rw [hmodel.card_eq_lieOrd (by norm_num)]
  decide +kernel


theorem rest15_false_of_linear_lie_seitz
    {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M)
    {L X H K P : Subgroup G} (hL : L ∈ calC S.M)
    (hLN : S.M ≤ normalizer (L : Set G)) (hthin : ¬ F08.Thin8 L)
    (hXL : X ≤ L) (hsupp : X ⊔ pCoreOf 2 L = L)
    (hHtop : H ≠ ⊤) (hHr : CFSG.Open.pRank 3 H ≤ 3)
    (hnotStrong : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M)
    (hXcomp : CFSG.Open.IsComponentOf X (H ⊓ S.M))
    (hKcomp : CFSG.Open.IsComponentOf K H) (hXK : X ≤ K) (hKM : ¬ K ≤ S.M)
    (hX : CFSG.Blueprint.LieModel X .PSL 3 2 2)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P X)
    (hGamma : rankThreeGamma 1 3 P ≤ S.M)
    (hNormal : (X.subgroupOf (H ⊓ S.M)).Normal)
    (hGammaH : rankThreeGamma 1 3 (P.subgroupOf H) ≤
      (normalizer (X : Set G)).subgroupOf H)
    (hZK : ¬ 3 ∣ Nat.card (center K))
    (hAlt : ¬ ∃ n : ℕ, 5 ≤ n ∧
      Nonempty (K ⧸ center K ≃* alternatingGroup (Fin n)))
    {d : TauCeti.ValidLieTypeIndex}
    (e : K ⧸ center K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hex : CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1) : False := by
  have hdiv := linear_order_dvd_center_quotient hXK hXcomp.2.2 hX
  obtain ⟨d, hv⟩ := d
  rcases hex with ⟨_, h | h | h | h | h⟩ | ⟨h, _⟩
  · obtain ⟨q, hp, hf, rfl⟩ := h
    have hm := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
    rw [hp, hf] at hm
    rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_eight hm] at hdiv
    norm_num at hdiv
  · obtain ⟨q, hp, hf, rfl⟩ := h
    have hm := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
    rw [hp, hf] at hm
    exact rest15_false_of_linear_quotient_order hXcomp hKcomp hXK hKM hX
      (CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four hm)
  · obtain ⟨q, hp, hf, rfl⟩ := h
    have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
    rw [hp, hf] at hm
    rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_four_two hm] at hdiv
    norm_num at hdiv
  · obtain ⟨q, hp, hf, h⟩ := h
    rcases h with rfl | rfl
    · rcases CFSG.Models.lieModel_B 3 q hv e with hm | hm
      · rw [hp, hf] at hm
        exact rest15_false_of_linear_symplectic_two hS hU S hMS hPart hL hLN hthin
          hXL hsupp hHtop hHr hnotStrong hXcomp hKcomp hXK hKM hX hP hGamma
          hNormal hGammaH hZK hAlt (Or.inl rfl)
          (CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (by simp [CFSG.Blueprint.classicalTags]) hm)
      · rw [hp] at hm
        exact absurd hm.1.2.2.2 (by simp)
    · rcases CFSG.Models.lieModel_B 4 q hv e with hm | hm
      · rw [hp, hf] at hm
        exact rest15_false_of_linear_symplectic_two hS hU S hMS hPart hL hLN hthin
          hXL hsupp hHtop hHr hnotStrong hXcomp hKcomp hXK hKM hX hP hGamma
          hNormal hGammaH hZK hAlt (Or.inr rfl)
          (CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (by simp [CFSG.Blueprint.classicalTags]) hm)
      · rw [hp] at hm
        exact absurd hm.1.2.2.2 (by simp)
  · subst h
    have hm : CFSG.Blueprint.LieModel (K ⧸ center K) .Tits 0 2 1 :=
      .inr (.inr (.inl ⟨rfl, by simp [CFSG.Blueprint.reeTitsTags],
      CFSG.StandardType.ChevTwo.reeTitsModel_of_tits hv e⟩))
    rw [PartOne.Section8.K328.k328det_titsCard _ hm] at hdiv
    norm_num at hdiv
  · norm_num at h


section LinearOvercomponent


theorem rest15_false_of_linear_overcomponent
    {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M)
    {L X H K P : Subgroup G} (hL : L ∈ calC S.M)
    (hLN : S.M ≤ normalizer (L : Set G)) (hthin : ¬ F08.Thin8 L)
    (hXL : X ≤ L) (hsupp : X ⊔ pCoreOf 2 L = L)
    (hHtop : H ≠ ⊤) (hHr : CFSG.Open.pRank 3 H ≤ 3)
    (hnotStrong : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M)
    (hXcomp : CFSG.Open.IsComponentOf X (H ⊓ S.M))
    (hKcomp : CFSG.Open.IsComponentOf K H) (hXK : X ≤ K) (hKM : ¬ K ≤ S.M)
    (hX : CFSG.Blueprint.LieModel X .PSL 3 2 2)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P X)
    (hGamma : rankThreeGamma 1 3 P ≤ S.M) : False := by
  have hcenter : center X = ⊥ := by
    have : IsSimpleGroup X := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags
      (by decide) hX
    exact uc22p21k_center_eq_bot hXcomp.2.2
  have hXrank : 2 ≤ CFSG.Open.pRank 3 X := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup X]
    exact CFSG.Blueprint.LieModel.two_le_pRank_psl3_of_dvd hX Nat.prime_three (by norm_num)
  have hNormal : (X.subgroupOf (H ⊓ S.M)).Normal :=
    normal_subgroupOf_of_centerless_component_of_rank_le_three hXcomp hcenter hXrank
      ((CFSG.SectionRank.pRank_mono (by norm_num) inf_le_left).trans hHr)
  have hGammaH : rankThreeGamma 1 3 (P.subgroupOf H) ≤
      (normalizer (X : Set G)).subgroupOf H := by
    have hrestrict := rankThreeGamma_subgroupOf_le_of_le
      (hP.le.trans (hXcomp.1.trans inf_le_left)) hGamma
    apply hrestrict.trans
    intro h hh
    have hhinf : (h : G) ∈ H ⊓ S.M := ⟨h.2, hh⟩
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hXcomp.1).1 hNormal hhinf
  by_cases hZK : 3 ∣ Nat.card (center K)
  · exact rest15_false_of_linear_three_center hS S hHtop hHr hXcomp hKcomp hXK hKM hX hP hGamma hZK
  by_cases hAlt : ∃ n : ℕ, 5 ≤ n ∧
      Nonempty (K ⧸ center K ≃* alternatingGroup (Fin n))
  · obtain ⟨n, hn, ⟨e⟩⟩ := hAlt
    exact rest15_false_of_linear_alternating hS S hHtop hHr hXcomp hKcomp
      hXK hKM hX hP hGamma hn e
  by_cases hSame : CFSG.Blueprint.LieModel (K ⧸ center K) .PSL 3 2 2
  · exact rest15_false_of_linear_psl_three_four_quotient hXcomp hKcomp hXK hKM hX hSame
  by_cases hLieThree : ∃ d : TauCeti.ValidLieTypeIndex, 3 = d.1.characteristic ∧
      Nonempty (K ⧸ center K ≃* (TauCeti.CFSGIndex.lie d).Group)
  · obtain ⟨d, hd, ⟨e⟩⟩ := hLieThree
    exact rest15_false_of_linear_lie_three hS hU S hMS hPart hL hLN hthin hXL hsupp
      hHtop hHr hnotStrong hXcomp hKcomp hXK hKM hX hP hGamma hNormal hGammaH hZK hAlt hd e
  by_cases hSeitz : ∃ d : TauCeti.ValidLieTypeIndex,
      Nonempty (K ⧸ center K ≃* (TauCeti.CFSGIndex.lie d).Group) ∧
      CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1
  · obtain ⟨d, ⟨e⟩, hex⟩ := hSeitz
    exact rest15_false_of_linear_lie_seitz hS hU S hMS hPart hL hLN hthin hXL hsupp
      hHtop hHr hnotStrong hXcomp hKcomp hXK hKM hX hP hGamma hNormal hGammaH hZK hAlt e hex
  by_cases hLie : ∃ d : TauCeti.ValidLieTypeIndex,
      Nonempty (K ⧸ center K ≃* (TauCeti.CFSGIndex.lie d).Group)
  · obtain ⟨d, ⟨e⟩⟩ := hLie
    have hchar : 3 ≠ d.1.characteristic := fun hd => hLieThree ⟨d, hd, ⟨e⟩⟩
    have hex : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1 :=
      fun hx => hSeitz ⟨d, ⟨e⟩, hx⟩
    exact rest15_false_of_linear_lie_nonexceptional hS hU S hMS hPart hL hLN hthin
      hXL hsupp hHtop hHr hnotStrong hXcomp hKcomp hXK hKM hX hP hGamma
      hNormal hGammaH hZK hAlt e hchar hex
  have hKtop : K ≠ ⊤ := fun h => hHtop (top_le_iff.mp (h ▸ hKcomp.1))
  obtain ⟨i, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.inCatalog_quotient_center_of_kgroup
      hKcomp.2.2 (hS.kProper.isKGroup K hKtop)
  have hsp : ∃ s : TauCeti.SporadicName,
      Nonempty (K ⧸ center K ≃* (TauCeti.CFSGIndex.sporadic s).Group) := by
    cases i with
    | cyclic q hq =>
      exfalso
      obtain ⟨a, b, hab⟩ :=
        CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_noncomm_quotient_center_of_quasisimple hKcomp.2.2
      exact hab (e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _))
    | alternating n hn => exact (hAlt ⟨n, hn, ⟨e⟩⟩).elim
    | lie d => exact (hLie ⟨d, ⟨e⟩⟩).elim
    | sporadic s => exact ⟨s, ⟨e⟩⟩
  obtain ⟨s, ⟨e⟩⟩ := hsp
  exact rest15_false_of_linear_sporadic_quotient hS hU S hMS hPart hL hLN hthin
    hXL hsupp hHtop hHr hnotStrong hXcomp hKcomp hXK hKM hX hP hGamma
    hNormal hGammaH hZK hAlt e

end LinearOvercomponent

section SmallTriality


theorem rest15_false_of_triality_two_dataOfSetup4
    {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M) {L Q P X : Subgroup G}
    (hX : PartOne.Section8.ChoiceX (UC6.dataOfSetup4 hS hU S) L Q P X)
    (hMN : S.M ≤ normalizer (L : Set G))
    (hmodel : CFSG.Blueprint.LieModel (Bar2 L) .trialityD4 0 2 1)
    (hNontrivial : ¬ ⁅L, X⁆ ≤ pCoreOf 2 L) : False := by
  obtain ⟨x, hx, hGen, _, _, hAut3, hAutNe⟩ :=
    R856NormalFour.exists_generator_of_commutator_not_le hX.le
      (hX.cex.sylowP.le.trans hMN) hX.card hNontrivial
  exact false_of_trialityD4_three_action hmodel (by norm_num)
    (PartOne.Section8.barConjAut (L := L) x) hAut3 hAutNe
    (fun A hA3 hAc hInv => R856NormalFour.fixes_abelian_bar_dataOfSetup4
      hS hU S hMS hPart hX hMN hx hGen hA3 hAc hInv)

theorem rest15_false_of_triality_four_dataOfSetup4
    {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M) {L Q P X : Subgroup G}
    (hX : PartOne.Section8.ChoiceX (UC6.dataOfSetup4 hS hU S) L Q P X)
    (hMN : S.M ≤ normalizer (L : Set G))
    (hmodel : CFSG.Blueprint.LieModel (Bar2 L) .trialityD4 0 2 2)
    (hNontrivial : ¬ ⁅L, X⁆ ≤ pCoreOf 2 L) : False := by
  obtain ⟨x, hx, hGen, _, _, hAut3, hAutNe⟩ :=
    R856NormalFour.exists_generator_of_commutator_not_le hX.le
      (hX.cex.sylowP.le.trans hMN) hX.card hNontrivial
  exact false_of_trialityD4_three_action hmodel (by norm_num)
    (PartOne.Section8.barConjAut (L := L) x) hAut3 hAutNe
    (fun A hA3 hAc hInv => R856NormalFour.fixes_abelian_bar_dataOfSetup4
      hS hU S hMS hPart hX hMN hx hGen hA3 hAc hInv)

theorem rest15_false_of_triality_small_dataOfSetup4
    {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M) {L Q P X : Subgroup G}
    (hX : PartOne.Section8.ChoiceX (UC6.dataOfSetup4 hS hU S) L Q P X)
    (hMN : S.M ≤ normalizer (L : Set G)) {f : ℕ} (hf : f = 1 ∨ f = 2)
    (hmodel : CFSG.Blueprint.LieModel (Bar2 L) .trialityD4 0 2 f)
    (hNontrivial : ¬ ⁅L, X⁆ ≤ pCoreOf 2 L) : False := by
  rcases hf with rfl | rfl
  · exact rest15_false_of_triality_two_dataOfSetup4 hS hU S hMS hPart hX hMN hmodel hNontrivial
  · exact rest15_false_of_triality_four_dataOfSetup4 hS hU S hMS hPart hX hMN hmodel hNontrivial

end SmallTriality

section NormalModels



theorem rest15NormReduced_dataOfSetup4_of_endgames
    {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M)
    (hCentral : ∀ {X H K P : Subgroup G},
      H ≠ ⊤ → CFSG.Open.pRank 3 H ≤ 3 → IsComponentOf X (H ⊓ S.M) →
      IsComponentOf K H → X ≤ K → ¬ K ≤ S.M → Nat.card (center X) = 3 →
      (CFSG.Blueprint.LieModel (X ⧸ center X) .PSL 3 2 2 ∨
        CFSG.Blueprint.LieModel (X ⧸ center X) .PSU 3 2 3) →
      CFSG.ABGLocalTools.IsSylowOf 3 P X → rankThreeGamma 1 3 P ≤ S.M → False)
    (hLinear : ∀ {L X H K P : Subgroup G}, L ∈ calC S.M →
      S.M ≤ normalizer (L : Set G) → ¬ F08.Thin8 L → X ≤ L →
      X ⊔ pCoreOf 2 L = L → H ≠ ⊤ → CFSG.Open.pRank 3 H ≤ 3 →
      ¬ IsStronglyPEmbedded 3 S.M → IsComponentOf X (H ⊓ S.M) →
      IsComponentOf K H → X ≤ K → ¬ K ≤ S.M →
      CFSG.Blueprint.LieModel X .PSL 3 2 2 →
      CFSG.ABGLocalTools.IsSylowOf 3 P X → rankThreeGamma 1 3 P ≤ S.M → False)
    (hUnitary : ∀ {X H K P : Subgroup G},
      H ≠ ⊤ → CFSG.Open.pRank 3 H ≤ 3 → IsComponentOf X (H ⊓ S.M) →
      IsComponentOf K H → X ≤ K → ¬ K ≤ S.M →
      CFSG.Blueprint.LieModel X .PSU 3 2 3 →
      CFSG.ABGLocalTools.IsSylowOf 3 P X → rankThreeGamma 1 3 P ≤ S.M → False) :
    Rest15NormReduced (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) := by
  intro _ hH c L hL _ hC2 _ _ _ hL2 hT hSmall _ _ hU3 hTL _ hCh _ hY
    hthin hrank hk1 hMN a ha hpr _ hGamma hOver _ hCore hPerfect hInter hComp haL
  classical
  have hNS : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M := by
    intro hsp
    have h := hk1 hsp
    omega
  obtain ⟨Q, hQ⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 L
  have hQr : 2 ≤ CFSG.Open.pRank 3 Q := (by omega : 2 ≤ CFSG.Open.pRank 3 L).trans
    (CFSG.pRank_le_of_isSylowOf_le Nat.prime_three hQ.le hQ le_rfl)
  have hGammaQ := hGamma 3 Nat.prime_three (by norm_num) Q hQ.le hQ.isPGroup hQr
  have hSL : PartOne.Section8.IsSL3PiType (Bar2 L) :=
    (r856_normal_dataOfSetup4_of_triality hS hU S hMS hPart hL hMN
      (fun {Q P X} hX {p f} _hp3 hD4 hLX => by
        obtain ⟨hp2, hf⟩ := rest15_triality_parameters hL hC2 hT hD4
        subst p
        exact rest15_false_of_triality_small_dataOfSetup4
          hS hU S hMS hPart hX hMN hf hD4 hLX)
      hrank hQ hGammaQ).resolve_left hNS
  have hmodelL := rest15_models_of_isSL3PiType_bar2
    CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
    hL hSL hC2 hL2 hTL hU3 hCh hSmall hY
  have hodd := uc22p21d_odd_orderOf_of_mem_calB1 c.hB ha
  have hmodel := rest15_perfectCore_bar2_models_of_barInf_models hL hodd hpr haL hmodelL
  let X := CFSG.Quasithin.perfectCore
    (L ⊓ centralizer ((zpowers a : Subgroup G) : Set G))
  let H := normalizer ((zpowers a : Subgroup G) : Set G)
  have hCH : L ⊓ centralizer ((zpowers a : Subgroup G) : Set G) ≤ H :=
    inf_le_right.trans (centralizer_le_normalizer _)
  have hHtop : H ≠ ⊤ := UC6.normalizer_ne_top_of_card_prime_uc6
    (UC6.dataOfSetup4 hS hU S).standing.simple
    (UC6.dataOfSetup4 hS hU S).standing.nonab hpr (Nat.card_zpowers a)
  have hHM : ¬ H ≤ S.M := s21_2 _ _ hH c (zpowers a) (zpowers_le.2 ha)
  have hInterH : pCoreOf 2 (H ⊓ S.M) = ⊥ := hInter hmodel H hCH hHtop hHM
  have hXcomp : CFSG.Open.IsComponentOf X (H ⊓ S.M) := hComp H hCH hInterH
  have hHr : CFSG.Open.pRank 3 H ≤ 3 := hOver H hCH
  have hGamma3 := hGamma 3 Nat.prime_three (by norm_num)
  obtain ⟨K, hK, hXK, hKM⟩ := rest15_exists_component_not_le_of_perfect_centralizer
    hS hU S hPart hL (by omega) hodd hpr haL hGamma3
    hCH hHtop hHM hHr (hCore H hCH).1 (hCore H hCH).2 hInterH hmodel
  have hO2X : pCoreOf 2 X = ⊥ := by
    have h := CFSG.CGT.Foote82.pCoreOf_le_pCoreOf_of_isSubnormal hXcomp.2.1
    rw [hInterH] at h
    exact le_bot_iff.1 h
  have hmodelX := rest15_models_of_bar2_models_of_pCoreOf_eq_bot hO2X hmodel
  have hXr : 2 ≤ CFSG.Open.pRank 3 X := (by omega : 2 ≤ CFSG.Open.pRank 3 L).trans
    (UC6.R869S.pRank_le_of_sup_pCore (hPerfect.1.trans inf_le_left)
      hPerfect.2.2.1 Nat.prime_three (by norm_num))
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 X
  have hPr : 2 ≤ CFSG.Open.pRank 3 P := hXr.trans
    (CFSG.pRank_le_of_isSylowOf_le Nat.prime_three hP.le hP le_rfl)
  have hPG : rankThreeGamma 1 3 P ≤ S.M := hGamma3 P
    (hP.le.trans (hPerfect.1.trans inf_le_left)) hP.isPGroup hPr
  rcases rest15_center_eq_bot_or_card_eq_three
    CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement hO2X hmodelX with hZ | hZ
  · rcases hmodelX with ⟨_, hLin⟩ | ⟨_, hUni⟩
    · exact hLinear hL hMN hthin
        (hPerfect.1.trans inf_le_left) hPerfect.2.2.1 hHtop hHr hNS
        hXcomp hK hXK hKM (CFSG.Blueprint.LieModel.of_quotient_center hZ hLin) hP hPG
    · exact hUnitary hHtop hHr hXcomp hK hXK hKM
        (CFSG.Blueprint.LieModel.of_quotient_center hZ hUni) hP hPG
  · apply hCentral hHtop hHr hXcomp hK hXK hKM hZ _ hP hPG
    exact hmodelX.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)





theorem rest15NormReduced_dataOfSetup4
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M) :
    Rest15NormReduced (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) :=
  rest15NormReduced_dataOfSetup4_of_endgames hS hU S hMS hPart
    (fun hHt hHr hXc hKc hXK hKM hZ hX hP hG =>
      rest15_false_of_central_three_overcomponent hS S hHt hHr hXc hKc hXK hKM hZ hX hP hG)
    (fun hL hLN hthin hXL hsupp hHt hHr hNS hXc hKc hXK hKM hX hP hG =>
      rest15_false_of_linear_overcomponent hS hU S hMS hPart hL hLN hthin hXL hsupp
        hHt hHr hNS hXc hKc hXK hKM hX hP hG)
    (fun hHt hHr hXc hKc hXK hKM hX hP hG =>
      rest15_false_of_unitary_overcomponent hS S hHt hHr hXc hKc hXK hKM hX hP hG)

end NormalModels

theorem rest15Norm_dataOfSetup4_of_reduced
    (hGA : GriessAllModelsStatement)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    (hSE : PartOne.Section7.StronglyEmbeddedFive)
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M)
    (h67 : UC6.R6_7 (UC6.dataOfSetup4 hS hU S))
    (hFusion : 3 ∉ (UC6.dataOfSetup4 hS hU S).sig → ∀ L Z : Subgroup G,
      PartOne.Section8.Loc876 S.M L Z → Z ∈ uniqueSet S.M)
    (hRest : Rest15NormReduced (UC6.dataOfSetup4 hS hU S) (fun _ _ => True)) :
    Rest15Norm (UC6.dataOfSetup4 hS hU S) (fun _ _ => True) := by
  intro hH c L hL hC hC2 hCZ hCov hSp hL2 hT hSmall hlist hnn hU3 hTL hT4 hCh hU54 hY
    hthin h3 hk1 hMN a ha hpr hN haL
  have hrank := rest15_pRank_three_eq_two hGA hL hC2 hL2 hTL hU3 hCh hSmall hY hlist h3
  have hodd := uc22p21d_odd_orderOf_of_mem_calB1 c.hB ha
  have hGamma : ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ Q : Subgroup G, Q ≤ L → IsPGroup r Q →
      2 ≤ CFSG.Open.pRank r Q → rankThreeGamma 1 r Q ≤ (UC6.dataOfSetup4 hS hU S).M := by
    intro r hr hr2 Q hQL hQ hQr
    exact rest15_rankThreeGamma_le_of_exclusions hGA hOut hSE hS hU S hMS hL hMN
      hC2 hL2 hTL hU3 hCh hSmall hY hlist hk1 hodd hpr haL (hN S.p S.hp)
      hr hr2 hQL hQ hQr
  have hOver := rest15_overgroup_rank_of_local_inputs hS hU S hMS hPart hL.1.le
    hrank hk1 hodd hpr hGamma haL
  have hO2 : ∀ H : Subgroup G,
      L ⊓ centralizer ((zpowers a : Subgroup G) : Set G) ≤ H →
        ¬ H ≤ (UC6.dataOfSetup4 hS hU S).M → pCoreOf 2 H = ⊥ := by
    intro H hH hHM
    exact rest15_pCore_two_eq_bot_of_centralizer_le hS hU S hPart.1 hL.1.le
      (by omega) hodd hpr haL (hGamma 3 Nat.prime_three (by norm_num)) hH hHM
  have hCore : ∀ H : Subgroup G,
      L ⊓ centralizer ((zpowers a : Subgroup G) : Set G) ≤ H →
        relPPrimeCore 3 H ≤ (UC6.dataOfSetup4 hS hU S).M ∧
          CFSG.fittingSubgroupOf H ≤ (UC6.dataOfSetup4 hS hU S).M := by
    intro H hH
    exact rest15_overgroup_core_le_of_centralizesBar hS hU S hPart.1 hL.1.le
      (by omega) hodd hpr haL (hGamma 3 Nat.prime_three (by norm_num)) hH
  have hPerfect := rest15_perfectCore_centralizer_spec hL hodd hpr haL
  have hComp : ∀ H : Subgroup G,
      L ⊓ centralizer ((zpowers a : Subgroup G) : Set G) ≤ H →
      pCoreOf 2 (H ⊓ (UC6.dataOfSetup4 hS hU S).M) = ⊥ →
      CFSG.Open.IsComponentOf
        (CFSG.Quasithin.perfectCore
          (L ⊓ centralizer ((zpowers a : Subgroup G) : Set G)))
        (H ⊓ (UC6.dataOfSetup4 hS hU S).M) := by
    intro H hCH hbot
    exact isComponentOf_inf_of_sup_pCore_of_pCore_eq_bot hL
      (hPerfect.1.trans inf_le_left) (hPerfect.1.trans hCH) hPerfect.2.2.1
      hPerfect.2.2.2 hbot
  have hInter :
      let X := CFSG.Quasithin.perfectCore
        (L ⊓ centralizer ((zpowers a : Subgroup G) : Set G));
      (IsSL3 (Bar2 X) 2 ∨ IsSU3 (Bar2 X) 3) →
        ∀ H : Subgroup G, L ⊓ centralizer ((zpowers a : Subgroup G) : Set G) ≤ H →
          H ≠ ⊤ → ¬ H ≤ (UC6.dataOfSetup4 hS hU S).M →
          pCoreOf 2 (H ⊓ (UC6.dataOfSetup4 hS hU S).M) = ⊥ := by
    dsimp only
    intro hmodel H hCH hHtop hHM
    let X := CFSG.Quasithin.perfectCore
      (L ⊓ centralizer ((zpowers a : Subgroup G) : Set G))
    have hXr : 2 ≤ CFSG.Open.pRank 3 X := (by omega : 2 ≤ CFSG.Open.pRank 3 L).trans
      (UC6.R869S.pRank_le_of_sup_pCore (hPerfect.1.trans inf_le_left)
        hPerfect.2.2.1 Nat.prime_three (by norm_num))
    obtain ⟨E, hEX, hEe, hEc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank Nat.prime_three hXr
    have hEL : E ≤ L := hEX.trans (hPerfect.1.trans inf_le_left)
    have hΓ := hGamma 3 Nat.prime_three (by norm_num) E hEL hEe.isPGroup
      (CFSG.SectionRank.le_pRank Nat.prime_three.one_lt le_rfl hEe hEc)
    exact PartOne.Section8.pCore_two_inf_eq_bot_of_local_shape
      (UC6S846.sigmaStd_dataOfSetup4 hS hU S) h67
      hHtop hHM
      (le_inf (hPerfect.1.trans hCH) (hPerfect.1.trans (inf_le_left.trans hL.1.le)))
      hPerfect.2.1 hmodel hEX hEe hEc hΓ
  exact hRest hFusion hH c L hL hC hC2 hCZ hCov hSp hL2 hT hSmall hlist hnn hU3 hTL hT4 hCh hU54 hY
    hthin hrank hk1 hMN a ha hpr hN hGamma hOver hO2 hCore hPerfect hInter hComp haL

end CFSG.LocalAnalysis.UniquenessCase.UC22

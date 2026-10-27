module

public import CFSG.Quasithin.Vol2.Ch10SecKIK2g
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BBarDeltaNormal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentySix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ExceptionalNotClassical
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSevenA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def K_ExceptionalNotThin : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    ((∃ n : ℕ, CFSG.Quasithin.Is2F4 n X) ∨ CFSG.Blueprint.LieModel X .Tits 0 2 1 ∨
      (∃ n : ℕ, Is3D4 X n)) →
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)

theorem not_thin_of_exceptional {L : Subgroup G}
    (hK : K_ExceptionalNotThin)
    (hshape : ((∃ n : ℕ, CFSG.Quasithin.Is2F4 n (Bar2 L)) ∨
      CFSG.Blueprint.LieModel (Bar2 L) .Tits 0 2 1 ∨ (∃ n : ℕ, Is3D4 (Bar2 L) n))) :
    ¬ F08.Thin8 L := by
  obtain ⟨p, hp, hp2, hpr⟩ := hK (Bar2 L) hshape
  rw [s13_pRank_bar_top hp hp2 L] at hpr
  intro hthin
  have h1 := hthin p hp hp2
  omega

theorem pCoreOf_eq_inf_of_mem_calC {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M) :
    pCoreOf 2 L = pCoreOf 2 D.M ⊓ L := by
  refine le_antisymm (le_inf (CFSG.Quasithin.pCoreOf_le_pCoreOf_of_isSubnormal hL.1)
    (CFSG.LieType.BorelTits.pCoreOf_le 2 L)) ?_
  have h2 : IsPGroup 2 ↥(pCoreOf 2 D.M ⊓ L) :=
    IsPGroup.to_le (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M) inf_le_left
  have hN : L ≤ Subgroup.normalizer (((pCoreOf 2 D.M) ⊓ L : Subgroup G) : Set G) := by
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hL.1.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M) hx,
        Subgroup.le_normalizer hx⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hN h2

theorem subgroupOf_pCoreOf_eq_pCore_of_mem_calC {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M) :
    (pCoreOf 2 D.M).subgroupOf L = CFSG.pCore 2 ↥L := by
  apply (Subgroup.map_subtype_inj (H := L)).mp
  rw [Subgroup.subgroupOf_map_subtype,
    show (CFSG.pCore 2 ↥L).map L.subtype = pCoreOf 2 L from rfl]
  exact (pCoreOf_eq_inf_of_mem_calC hL).symm

theorem pCoreOf_sup_pCoreOf_of_mem_calC {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hN : (L.subgroupOf D.M).Normal) :
    pCoreOf 2 (L ⊔ pCoreOf 2 D.M) = pCoreOf 2 D.M := by
  have hKM : L ⊔ pCoreOf 2 D.M ≤ D.M :=
    sup_le hL.1.le (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)
  have hLK : L ≤ L ⊔ pCoreOf 2 D.M := le_sup_left
  have hNL : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).1 hN
  have hNA : D.M ≤ Subgroup.normalizer ((pCoreOf 2 D.M : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M
  have hNK : D.M ≤ Subgroup.normalizer ((L ⊔ pCoreOf 2 D.M : Subgroup G) : Set G) := by
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_sup L (pCoreOf 2 D.M) ⟨hNL hx, hNA hx⟩
  refine le_antisymm ?_ ?_
  · have hNKp : D.M ≤ Subgroup.normalizer
        ((pCoreOf 2 (L ⊔ pCoreOf 2 D.M) : Subgroup G) : Set G) :=
      hNK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2
        (L ⊔ pCoreOf 2 D.M))
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 (L ⊔ pCoreOf 2 D.M)).trans hKM) hNKp
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ pCoreOf 2 D.M))
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right
      (hKM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M)

theorem subgroupOf_pCoreOf_sup_eq_pCore {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hN : (L.subgroupOf D.M).Normal) :
    (pCoreOf 2 D.M).subgroupOf (L ⊔ pCoreOf 2 D.M) =
      CFSG.pCore 2 ↥(L ⊔ pCoreOf 2 D.M) := by
  apply (Subgroup.map_subtype_inj (H := L ⊔ pCoreOf 2 D.M)).mp
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr le_sup_right,
    show (CFSG.pCore 2 ↥(L ⊔ pCoreOf 2 D.M)).map (L ⊔ pCoreOf 2 D.M).subtype =
      pCoreOf 2 (L ⊔ pCoreOf 2 D.M) from rfl]
  exact (pCoreOf_sup_pCoreOf_of_mem_calC hL hN).symm

theorem bar2_sup_pCoreOf_mulEquiv {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hN : (L.subgroupOf D.M).Normal) :
    Nonempty (Bar2 (L ⊔ pCoreOf 2 D.M) ≃* Bar2 L) := by
  have hLN : L ≤ Subgroup.normalizer ((pCoreOf 2 D.M : Subgroup G) : Set G) :=
    hL.1.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M)
  have hKM : L ⊔ pCoreOf 2 D.M ≤ D.M :=
    sup_le hL.1.le (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)
  have hKN : L ⊔ pCoreOf 2 D.M ≤
      Subgroup.normalizer ((pCoreOf 2 D.M : Subgroup G) : Set G) :=
    hKM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M)
  haveI : ((pCoreOf 2 D.M).subgroupOf L).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hLN
  haveI : ((pCoreOf 2 D.M).subgroupOf (L ⊔ pCoreOf 2 D.M)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hKN
  let e1 := QuotientGroup.quotientInfEquivProdNormalizerQuotient L (pCoreOf 2 D.M) hLN
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (subgroupOf_pCoreOf_sup_eq_pCore hL hN)).symm.trans
    (e1.symm.trans
      (QuotientGroup.quotientMulEquivOfEq (subgroupOf_pCoreOf_eq_pCore_of_mem_calC hL)))⟩

theorem isComponentModO2_sup_pCoreOf {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hN : (L.subgroupOf D.M).Normal) :
    F12.IsComponentModO2 D.M (L ⊔ pCoreOf 2 D.M) := by
  have hKM : L ⊔ pCoreOf 2 D.M ≤ D.M :=
    sup_le hL.1.le (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)
  have hNL : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).1 hN
  have hNA : D.M ≤ Subgroup.normalizer ((pCoreOf 2 D.M : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M
  have hNK : D.M ≤ Subgroup.normalizer ((L ⊔ pCoreOf 2 D.M : Subgroup G) : Set G) := by
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_sup L (pCoreOf 2 D.M) ⟨hNL hx, hNA hx⟩
  have hKnormal : ((L ⊔ pCoreOf 2 D.M).subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).2 hNK
  refine ⟨le_sup_right, hKM,
    CFSG.Open.IsSubnormal.step hKM hKnormal (CFSG.Open.IsSubnormal.refl D.M), ?_⟩
  let hAn : ((pCoreOf 2 D.M).subgroupOf (L ⊔ pCoreOf 2 D.M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2
      (hKM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M))
  refine ⟨hAn, ?_⟩
  letI := hAn
  obtain ⟨e⟩ := bar2_sup_pCoreOf_mulEquiv hL hN
  exact CFSG.Quasithin.Vol2.Ch10.SecC.C10KH.isQuasisimple_of_open
    (hL.2.2.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq (subgroupOf_pCoreOf_sup_eq_pCore hL hN)).trans e))

section Certified


theorem k_exceptionalNotThin : K_ExceptionalNotThin := by
  intro X _ _ hX
  rcases hX with ⟨n, h2F4⟩ | hTits | ⟨n, h3D4⟩
  · obtain ⟨r, hr, hr2, hle⟩ :=
      CFSG.RankThree.Chevalley.exists_two_le_pRank_of_largeReeModel h2F4
    exact ⟨r, hr, hr2, by rwa [CFSG.SectionRank.pRank_eq_open_pRank_top] at hle⟩
  · have hRT : CFSG.Blueprint.ReeTitsModel X .Tits 2 1 :=
      (CFSG.Blueprint.LieModel.reeTitsModel hTits (by decide)).2
    have hle := CFSG.RankThree.Chevalley.two_le_pRank_five_of_titsModel hRT
    exact ⟨5, Nat.prime_five, by norm_num,
      by rwa [CFSG.SectionRank.pRank_eq_open_pRank_top] at hle⟩
  · by_contra hcon
    have hS' : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r X ≤ 1 := by
      intro r hr hr2
      by_contra hle
      exact hcon ⟨r, hr, hr2, by
        rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hle
        omega⟩
    have hCE : CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 2 n :=
      CFSG.Blueprint.LieModel.chevalleyExceptionalModel h3D4 (by decide)
    obtain ⟨-, -, hn1⟩ :=
      CFSG.RankThree.Chevalley.odd_rank_one_Chevalley_exceptional_model_is_binary_triality
        X hS' .trialityD4 2 n hCE
    have h21 : CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 2 1 := hn1 ▸ hCE
    have hle := CFSG.QuasithinUnique.Setup.Family.trialityTwoHasRankTwo X h21
    have h1 := hS' 3 Nat.prime_three (by norm_num)
    omega

@[expose] def W4McClurg2F4 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)) (n : ℕ),
      L ≤ Y → (L.subgroupOf Y).Normal → CFSG.Quasithin.Is2F4 n ↥L → fixV L = ⊥ →
        4 * n + 2 < E3.mParam Y

@[expose] def W4McClurgTits : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)),
      L ≤ Y → (L.subgroupOf Y).Normal → CFSG.Quasithin.IsTits ↥L → fixV L = ⊥ →
        6 < E3.mParam Y

theorem is2F4_barSub_of_is2F4 {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    {L : Subgroup G} {n : ℕ} (hL : L ∈ calC D.M)
    (hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥)
    (h2F4 : CFSG.Quasithin.Is2F4 n (Bar2 L)) :
    CFSG.Quasithin.Is2F4 n ↥(barSub V₀ V hV.isElemAbelian L) := by
  have hsimple := (CFSG.LieType.Simplicity.fam_ree_tits_simplicity (Bar2 L) .twistedF4 2 n h2F4).2
  obtain ⟨e⟩ := barSubBar2Equiv_of_isSimpleGroup hV hL hL1 hsimple
  exact CFSG.Quasithin.Is2F4.of_mulEquiv e h2F4

theorem isTits_barSub_of_isTits {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥)
    (hTits : CFSG.Quasithin.IsTits (Bar2 L)) :
    CFSG.Quasithin.IsTits ↥(barSub V₀ V hV.isElemAbelian L) := by
  have hsimple := (CFSG.LieType.Simplicity.fam_ree_tits_simplicity (Bar2 L) .Tits 2 1 hTits).2
  obtain ⟨e⟩ := barSubBar2Equiv_of_isSimpleGroup hV hL hL1 hsimple
  exact CFSG.Quasithin.IsTits.of_mulEquiv e hTits



theorem fixV_barSub_eq_bot_of_normal {D : Data G} (h640 : UC6.R6_40_2 D)
    (hFF : W4Thm12McClurg) (h869 : F08.R869 D) (h127 : R127 D) {V : Subgroup G}
    (hV : Hyp125 D ⊥ V) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hN : (L.subgroupOf D.M).Normal)
    (hshape : (∃ n : ℕ, CFSG.Quasithin.Is2F4 n (Bar2 L)) ∨
      CFSG.Quasithin.IsTits (Bar2 L) ∨ (∃ n : ℕ, Is3D4 (Bar2 L) n)) :
    fixV (barSub ⊥ V hV.isElemAbelian L) = ⊥ := by
  have hnt : ¬ F08.Thin8 L := by
    apply not_thin_of_exceptional k_exceptionalNotThin
    rcases hshape with h2 | hT | h3
    · exact Or.inl h2
    · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hT⟩))))
    · exact Or.inr (Or.inr h3)
  set A := pCoreOf 2 D.M with hA
  set K := L ⊔ A with hK
  have hLK : L ≤ K := le_sup_left
  have hAK : A ≤ K := le_sup_right
  have hKM : K ≤ D.M := sup_le hL.1.le (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)
  have hLKstab : L ≤ stabTil ⊥ V :=
    hL.1.le.trans (le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀)
  have hAKstab : A ≤ stabTil ⊥ V :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M).trans
      (le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀)
  have hbar : barSub ⊥ V hV.isElemAbelian K = barSub ⊥ V hV.isElemAbelian L := by
    have hsup : barSub ⊥ V hV.isElemAbelian (L ⊔ A) =
        barSub ⊥ V hV.isElemAbelian L ⊔ barSub ⊥ V hV.isElemAbelian A := by
      unfold barSub
      rw [Subgroup.subgroupOf_sup hLKstab hAKstab, Subgroup.map_sup]
    rw [show K = L ⊔ A from rfl, hsup, barSub_pCoreOf_eq_bot_of_hyp125 hV, sup_bot_eq]
  have hKnormal : (K.subgroupOf D.M).Normal := by
    have hNL : D.M ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).1 hN
    have hNA : D.M ≤ Subgroup.normalizer (A : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).2 fun x hx => ?_
    exact Subgroup.inf_normalizer_le_normalizer_sup L A ⟨hNL hx, hNA hx⟩
  have hcomp : F12.IsComponentModO2 D.M K := isComponentModO2_sup_pCoreOf hL hN
  have hU : UniqueMax D.M (K ⊔ D.T) := by
    have hNcal : calNOf L = {D.M} := h869 L (Or.inl hL) L le_rfl
      (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L)) hnt
    have hUL : UniqueMax D.M L := UC22.uc22p22u_uniqueMax_of_calN D hL.1.le hNcal
    exact UC22.uc22p22u_uniqueMax_mono D (hLK.trans le_sup_left)
      (sup_le hKM D.sylowM.le) hUL
  have hL1 : barSub ⊥ V hV.isElemAbelian L ≠ ⊥ :=
    barSub_ne_bot_of_not_thin_bot h869 h127 hV hL hnt
  have hKH : barSub ⊥ V hV.isElemAbelian (UC22.conjClosure D.M K) ≠ ⊥ := by
    rw [uc22p2214_conjClosure_eq_of_normal hKM hKnormal, hbar]
    exact hL1
  have h26 := twelve_twentySix D h640 hFF hV hcomp hU hKH
  rcases h26 with hfix | ⟨-, hclass, -⟩
  · rwa [uc22p2214_conjClosure_eq_of_normal hKM hKnormal, hbar] at hfix
  · obtain ⟨e⟩ := bar2_sup_pCoreOf_mulEquiv hL hN
    rcases hshape with ⟨n, h2⟩ | hT | ⟨n, h3⟩
    · exact absurd hclass (not_classicalEvenAltG2Der_of_is2F4
        (CFSG.Quasithin.Is2F4.of_mulEquiv e.symm h2))
    · exact absurd hclass (not_classicalEvenAltG2Der_of_isTits
        (CFSG.Quasithin.IsTits.of_mulEquiv e.symm hT))
    · exact absurd hclass (not_classicalEvenAltG2Der_of_is3D4
        (CFSG.Blueprint.LieModel.of_mulEquiv e.symm h3))

theorem seventeen_thirtyone_normal_v0eq1
    (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h126 : R126 D) (h111 : W3Thm111 G) (h869 : F08.R869 D) (h127 : R127 D)
    (h640 : UC6.R6_40_2 D) (hFF : W4Thm12McClurg)
    (hMc2F4 : W4McClurg2F4) (hMcTits : W4McClurgTits)
    (h2F4 : Inputs1719.W4Lem4_17TwoF4N)
    {V : Subgroup G} (hV : Hyp125 D ⊥ V)
    (L : Subgroup G) (hL : L ∈ calC D.M) (hN : (L.subgroupOf D.M).Normal) :
    (∀ n : ℕ, ¬ CFSG.Quasithin.Is2F4 n (Bar2 L)) ∧
      ¬ CFSG.Blueprint.LieModel (Bar2 L) .Tits 0 2 1 := by
  constructor
  · intro n h2F4Shape
    have hshape : ((∃ n : ℕ, CFSG.Quasithin.Is2F4 n (Bar2 L)) ∨
        CFSG.Blueprint.LieModel (Bar2 L) .Tits 0 2 1 ∨ (∃ n : ℕ, Is3D4 (Bar2 L) n)) :=
      Or.inl ⟨n, h2F4Shape⟩
    have hnt := not_thin_of_exceptional k_exceptionalNotThin hshape
    have hL1 := barSub_ne_bot_of_not_thin_bot h869 h127 hV hL hnt
    have hU := uniqueMax_conjClosure_of_not_thin h869 hL hnt
    have hcomp : barSub ⊥ V hV.isElemAbelian L ∈ compBar D.M ⊥ V hV.isElemAbelian :=
      barSub_mem_compBar_of_ne_bot hV hL hL1
    have hshapeBar := is2F4_barSub_of_is2F4 hV hL hL1 h2F4Shape
    have hfix := fixV_barSub_eq_bot_of_normal h640 hFF h869 h127 hV hL hN
      (Or.inl ⟨n, h2F4Shape⟩)
    have hLMbar : barSub ⊥ V hV.isElemAbelian L ≤ Mbar D.M ⊥ V hV.isElemAbelian :=
      barSub_mono ⊥ V hV.isElemAbelian hL.1.le
    have hMN : D.M ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).1 hN
    have hNormBar : ((barSub ⊥ V hV.isElemAbelian L).subgroupOf
        (Mbar D.M ⊥ V hV.isElemAbelian)).Normal :=
      barSub_subgroupOf_mbar_normal hV.isElemAbelian hL.1.le hMN
    have hpow : ∀ w : Vtil ⊥ V hV.isElemAbelian, w ^ 2 = 1 :=
      s15_Infra_vtil_sq_eq_one ⊥ V hV.isElemAbelian
    have hm := hMc2F4 (W := Vtil ⊥ V hV.isElemAbelian) hpow
      (Y := Mbar D.M ⊥ V hV.isElemAbelian) (L := barSub ⊥ V hV.isElemAbelian L) (n := n)
      hLMbar hNormBar hshapeBar hfix
    have hm' : 4 * n + 2 < mBar D.M ⊥ V hV.isElemAbelian := hm
    have hsimple : IsSimpleGroup (Bar2 L) :=
      (CFSG.LieType.Simplicity.fam_2f4_simplicity (Bar2 L) 2 n h2F4Shape).2
    have hb := bBar_le_two_mul_of_is2F4 hV h2F4 hL hN hL1 hfix hsimple h2F4Shape
    have hb' : bBar (UC22.conjClosure D.M L) D.M ⊥ V hV.isElemAbelian ≤ 2 * n := by
      rwa [uc22p2214_conjClosure_eq_of_normal hL.1.le hN]
    have h1 := twelve_twentyThree_one D hx h61 h126 h111 hV rfl hL.1 hL.2.2 hL1 hU
    have hk := TwelveSeven.k_le_two D
    omega
  · intro hTits
    have hshape : ((∃ n : ℕ, CFSG.Quasithin.Is2F4 n (Bar2 L)) ∨
        CFSG.Blueprint.LieModel (Bar2 L) .Tits 0 2 1 ∨ (∃ n : ℕ, Is3D4 (Bar2 L) n)) :=
      Or.inr (Or.inl hTits)
    have hnt := not_thin_of_exceptional k_exceptionalNotThin hshape
    have hL1 := barSub_ne_bot_of_not_thin_bot h869 h127 hV hL hnt
    have hU := uniqueMax_conjClosure_of_not_thin h869 hL hnt
    have hcomp : barSub ⊥ V hV.isElemAbelian L ∈ compBar D.M ⊥ V hV.isElemAbelian :=
      barSub_mem_compBar_of_ne_bot hV hL hL1
    have hRT : CFSG.Quasithin.IsTits (Bar2 L) :=
      (CFSG.Blueprint.LieModel.reeTitsModel hTits (by decide)).2
    have hshapeBar := isTits_barSub_of_isTits hV hL hL1 hRT
    have hfix := fixV_barSub_eq_bot_of_normal h640 hFF h869 h127 hV hL hN
      (Or.inr (Or.inl hRT))
    have hLMbar : barSub ⊥ V hV.isElemAbelian L ≤ Mbar D.M ⊥ V hV.isElemAbelian :=
      barSub_mono ⊥ V hV.isElemAbelian hL.1.le
    have hMN : D.M ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).1 hN
    have hNormBar : ((barSub ⊥ V hV.isElemAbelian L).subgroupOf
        (Mbar D.M ⊥ V hV.isElemAbelian)).Normal :=
      barSub_subgroupOf_mbar_normal hV.isElemAbelian hL.1.le hMN
    have hpow : ∀ w : Vtil ⊥ V hV.isElemAbelian, w ^ 2 = 1 :=
      s15_Infra_vtil_sq_eq_one ⊥ V hV.isElemAbelian
    have hm := hMcTits (W := Vtil ⊥ V hV.isElemAbelian) hpow
      (Y := Mbar D.M ⊥ V hV.isElemAbelian) (L := barSub ⊥ V hV.isElemAbelian L)
      hLMbar hNormBar hshapeBar hfix
    have hm' : 6 < mBar D.M ⊥ V hV.isElemAbelian := hm
    have hsimple : IsSimpleGroup (Bar2 L) :=
      (CFSG.LieType.Simplicity.fam_tits_simplicity (Bar2 L) 2 1 hRT).2
    have hb := bBar_le_two_of_isTits hV hL hN hL1 hfix hsimple hRT
    have hb' : bBar (UC22.conjClosure D.M L) D.M ⊥ V hV.isElemAbelian ≤ 2 := by
      rwa [uc22p2214_conjClosure_eq_of_normal hL.1.le hN]
    have h1 := twelve_twentyThree_one D hx h61 h126 h111 hV rfl hL.1 hL.2.2 hL1 hU
    have hk := TwelveSeven.k_le_two D
    omega

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

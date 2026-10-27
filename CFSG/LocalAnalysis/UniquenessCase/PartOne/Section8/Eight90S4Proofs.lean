module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90S4
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.TwoGroupNormalizerMaxLocal.TwoGroupNormalizerMaxLocal
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.List880Rank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3a
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Choice
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.SylowCent
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NotThinShapes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEleven
import CFSG.RankThree.PartTwo.Sec17.Item17Res3ProofMeet
public import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon
import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement Pointwise

private theorem r90p2_KN_le_X {G : Type} [Group G] {J M N : Subgroup G} (hJM : J ≤ M) :
    perfInter890 J N ≤ N ⊓ M :=
  le_inf (r890_perfInter_le_right J N) ((r890_perfInter_le_left J N).trans hJM)

private theorem r90p2_X_le_normalizer_KN {G : Type} [Group G] {J M N : Subgroup G}
    (hMJ : M ≤ normalizer (J : Set G)) :
    N ⊓ M ≤ normalizer (perfInter890 J N : Set G) :=
  calc N ⊓ M ≤ normalizer (J : Set G) ⊓ normalizer (N : Set G) :=
        le_inf (inf_le_right.trans hMJ) (inf_le_left.trans Subgroup.le_normalizer)
    _ ≤ normalizer ((J ⊓ N : Subgroup G) : Set G) :=
        Subgroup.inf_normalizer_le_normalizer_inf (H := J) (K := N)
    _ ≤ normalizer (perfInter890 J N : Set G) :=
        CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf_normalizer_contains (J ⊓ N)

private theorem r90p1_le_perfInter {G : Type} [Group G] [Finite G] {J N C : Subgroup G}
    (hKN : perfInter890 J C ≤ N) : perfInter890 J C ≤ perfInter890 J N := by
  have hperf : Group.IsPerfect (perfInter890 J C) :=
    Subgroup.isPerfect_iff.mpr (r890_perfInter_perfect J C)
  have hle : perfInter890 J C ≤ J ⊓ N := le_inf (r890_perfInter_le_left J C) hKN
  exact CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidualOf _ _ hperf hle

private theorem r90p1_join_eq {G : Type} [Group G] {J N C : Subgroup G}
    (hKle : perfInter890 J C ≤ perfInter890 J N)
    (hKJ : perfInter890 J C ⊔ pCoreOf 2 J = J) :
    J = perfInter890 J N ⊔ pCoreOf 2 J := by
  apply le_antisymm
  · calc J = perfInter890 J C ⊔ pCoreOf 2 J := hKJ.symm
      _ ≤ perfInter890 J N ⊔ pCoreOf 2 J := sup_le_sup hKle le_rfl
  · exact sup_le (r890_perfInter_le_left J N) (CFSG.LieType.BorelTits.pCoreOf_le 2 J)

private theorem r90p1_isSz_bar2 {G : Type} [Group G] {J N : Subgroup G}
    (hKNJ : perfInter890 J N ≤ J)
    (hJeq : J = perfInter890 J N ⊔ pCoreOf 2 J)
    {n : ℕ} (hSz : IsSz (Bar2 J) n) : IsSz (Bar2 (perfInter890 J N)) n := by
  obtain ⟨e⟩ :=
    CFSG.RankThree.PartTwo.Sec17.Proof17Res3.nonempty_quotient_pCore_two_equiv
      (L := perfInter890 J N) (Y := J) hKNJ hJeq
  exact CFSG.Blueprint.LieModel.of_mulEquiv e hSz

theorem r890_lemma5b1 : Lemma5b1_890 := by
  intro G _ _ D L P J Y n hCfg hKJ _hpCore _hSzK N hKN
  have hJM : J ≤ D.M :=
    CFSG.LocalAnalysis.GLTheoremA.I142N.isSubnormal_le hCfg.memJ.1
  have hKN_le : perfInter890 J N ≤ N ⊓ D.M := r90p2_KN_le_X hJM
  have hnorm : N ⊓ D.M ≤ Subgroup.normalizer (perfInter890 J N : Set G) :=
    r90p2_X_le_normalizer_KN hCfg.normal_J
  have hKle : perfInter890 J (Subgroup.centralizer (Y : Set G)) ≤ perfInter890 J N :=
    r90p1_le_perfInter hKN
  have hJeq : J = perfInter890 J N ⊔ pCoreOf 2 J := r90p1_join_eq hKle hKJ
  have hsz : IsSz (Bar2 (perfInter890 J N)) n :=
    r90p1_isSz_bar2 (r890_perfInter_le_left J N) hJeq hCfg.szJ
  exact ⟨(Subgroup.normal_subgroupOf_iff_le_normalizer hKN_le).mpr hnorm, hsz⟩

private theorem r90p2_pCoreOf_KN {G : Type} [Group G] [Finite G] {J N Y : Subgroup G}
    (hJ : perfInter890 J (centralizer (Y : Set G)) ⊔ pCoreOf 2 J = J)
    (hN : perfInter890 J (centralizer (Y : Set G)) ≤ N) :
    pCoreOf 2 (perfInter890 J N) = perfInter890 J N ⊓ pCoreOf 2 J :=
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.pCoreOf_eq_inf (r890_perfInter_le_left J N)
    (r90p1_join_eq (r90p1_le_perfInter hN) hJ)

private theorem r90p2_commutator_mem_pCoreOf {G : Type} [Group G] [Finite G] {J R K : Subgroup G}
    (hJ : K ⊔ pCoreOf 2 J = J) (hRJ : R ≤ normalizer (J : Set G))
    (hKR : K ≤ normalizer (R : Set G)) (hR : IsPGroup 2 R) :
    ∀ r ∈ R, ∀ j ∈ J, r * j * r⁻¹ * j⁻¹ ∈ pCoreOf 2 J := by
  classical
  have hKJ : K ≤ J := by rw [← hJ]; exact le_sup_left
  set U : Subgroup G := R ⊔ pCoreOf 2 J with hU
  have hO2p : IsPGroup 2 (pCoreOf 2 J) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J
  have hRO2 : R ≤ normalizer (pCoreOf 2 J : Set G) :=
    hRJ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J)
  have hUp : IsPGroup 2 U := by
    rw [hU]
    exact hR.to_sup_of_normal_right' hO2p hRO2
  have hKnormU : K ≤ normalizer (U : Set G) := by
    refine (le_inf hKR (hKJ.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J))).trans ?_
    rw [hU]
    exact Subgroup.inf_normalizer_le_normalizer_sup R (pCoreOf 2 J)
  have hO2normU : pCoreOf 2 J ≤ normalizer (U : Set G) := by
    rw [hU]
    exact le_sup_right.trans Subgroup.le_normalizer
  have hJnormU : J ≤ normalizer (U : Set G) := by
    rw [← hJ]
    exact sup_le hKnormU hO2normU
  have hWp : IsPGroup 2 ↥(J ⊓ U) := hUp.to_inf_right (H := J)
  have hJnormW : J ≤ normalizer ((J ⊓ U : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer hJnormU).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := J) (K := U))
  have hWle : J ⊓ U ≤ pCoreOf 2 J :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hJnormW hWp
  intro r hr j hj
  have hrjJ : r * j * r⁻¹ * j⁻¹ ∈ J :=
    J.mul_mem ((Subgroup.mem_normalizer_iff.1 (hRJ hr) j).1 hj) (J.inv_mem hj)
  have hjconj : j * r⁻¹ * j⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.1 (hJnormU hj) r⁻¹).1 (U.inv_mem ((le_sup_left : R ≤ U) hr))
  have hrjU : r * j * r⁻¹ * j⁻¹ ∈ U := by
    have hmem := U.mul_mem ((le_sup_left : R ≤ U) hr) hjconj
    simpa only [mul_assoc] using hmem
  exact hWle ⟨hrjJ, hrjU⟩

private theorem r90p2_le_centOverO2 {G : Type} [Group G] [Finite G] {J N R H K : Subgroup G}
    (hJ : K ⊔ pCoreOf 2 J = J) (hKR : K ≤ normalizer (R : Set G))
    (hRJ : R ≤ normalizer (J : Set G)) (hR2 : IsPGroup 2 R) (hRH : R ≤ H)
    (hXnorm : H ≤ normalizer (perfInter890 J N : Set G))
    (hKNJ : perfInter890 J N ≤ J)
    (hcore : pCoreOf 2 (perfInter890 J N) = perfInter890 J N ⊓ pCoreOf 2 J) :
    R ≤ F08.CentOverO2 H (perfInter890 J N) := by
  intro r hr
  rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff]
  refine ⟨hRH hr, fun k hk => ?_⟩
  have hrn : r ∈ normalizer (perfInter890 J N : Set G) := hXnorm (hRH hr)
  have hrk : r * k * r⁻¹ ∈ perfInter890 J N :=
    (Subgroup.mem_normalizer_iff.1 hrn k).1 hk
  have hmemKN : r * k * r⁻¹ * k⁻¹ ∈ perfInter890 J N :=
    (perfInter890 J N).mul_mem hrk ((perfInter890 J N).inv_mem hk)
  have hmemQ : r * k * r⁻¹ * k⁻¹ ∈ pCoreOf 2 J :=
    r90p2_commutator_mem_pCoreOf hJ hRJ hKR hR2 r hr k (hKNJ hk)
  rw [hcore]
  exact ⟨hmemKN, hmemQ⟩

private theorem r90p2_isSylow_of_maximal {G : Type} [Group G] [Finite G]
    {K KN R H : Subgroup G} (hR2 : IsPGroup 2 R)
    (hRC : R ≤ F08.CentOverO2 H KN)
    (hCH : F08.CentOverO2 H KN ≤ H) (hKN : KN ≤ H) (hKKN : K ≤ KN)
    (hmax : ∀ R' : Subgroup G, R ≤ R' → R' ≤ H → IsPGroup 2 R' →
      K ≤ normalizer (R' : Set G) → R' = R) :
    IsSylowOf 2 R (F08.CentOverO2 H KN) := by
  classical
  set C : Subgroup G := F08.CentOverO2 H KN with hC
  have hRC' : R ≤ C := hRC
  have hRsub : IsPGroup 2 (R.subgroupOf C) := hR2.comap_subtype
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow hRsub
  have hPS : IsSylowOf 2 ((P : Subgroup C).map C.subtype) C := ⟨P, rfl⟩
  have hPSyl : IsSylowOf 2 ((P : Subgroup C).map C.subtype) (F08.CentOverO2 H KN) := hPS
  have hSX : ((P : Subgroup C).map C.subtype : Subgroup G) ≤ H :=
    (Subgroup.map_subtype_le (P : Subgroup C)).trans hCH
  have hSp : IsPGroup 2 ((P : Subgroup C).map C.subtype : Subgroup G) :=
    P.isPGroup'.map C.subtype
  have hKNnormS : KN ≤ normalizer (((P : Subgroup C).map C.subtype : Subgroup G) : Set G) :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.le_normalizer_of_isSylowOf_centOverO2
      hKN hPSyl
  have hKnormS : K ≤ normalizer (((P : Subgroup C).map C.subtype : Subgroup G) : Set G) :=
    hKKN.trans hKNnormS
  have hRS : R ≤ (P : Subgroup C).map C.subtype := by
    have hmapR : (R.subgroupOf C).map C.subtype = R := Subgroup.map_subgroupOf_eq_of_le hRC'
    rw [← hmapR]
    exact Subgroup.map_mono hP
  have hSeq : ((P : Subgroup C).map C.subtype : Subgroup G) = R :=
    hmax _ hRS hSX hSp hKnormS
  exact hSeq ▸ hPS

theorem r890_lemma5b1Syl : Lemma5b1Syl_890 := by
  intro G _ _ D L P J Y n hcfg hJ _hcore N R hN hRmax
  have hJM : J ≤ D.M := hcfg.memJ.1.le
  have hKKN : perfInter890 J (centralizer (Y : Set G)) ≤ perfInter890 J N := r90p1_le_perfInter hN
  have hcoreKN : pCoreOf 2 (perfInter890 J N) = perfInter890 J N ⊓ pCoreOf 2 J :=
    r90p2_pCoreOf_KN hJ hN
  have hKNX : perfInter890 J N ≤ N ⊓ D.M := r90p2_KN_le_X (J := J) hJM
  have hXnorm : N ⊓ D.M ≤ normalizer (perfInter890 J N : Set G) :=
    r90p2_X_le_normalizer_KN (J := J) hcfg.normal_J
  have hRJ : R ≤ normalizer (J : Set G) := (hRmax.1.trans inf_le_right).trans hcfg.normal_J
  have hRC : R ≤ F08.CentOverO2 (N ⊓ D.M) (perfInter890 J N) :=
    r90p2_le_centOverO2 hJ hRmax.2.2.1 hRJ hRmax.2.1 hRmax.1 hXnorm
      (r890_perfInter_le_left J N) hcoreKN
  exact r90p2_isSylow_of_maximal hRmax.2.1 hRC
    (fun x hx => (CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff.mp hx).1)
    hKNX hKKN hRmax.2.2.2

open CFSG.LocalAnalysis.UniquenessCase.UC22 in
theorem r890_lemma41 : Lemma41_890 := by
  intro G _ _ D L P J Y n c hKJ _ R hR
  have hRJ : R ≤ Subgroup.normalizer (J : Set G) := hR.1.trans c.normal_J
  have hRC : R ≤ F08.CentOverO2 D.M J := fun r hr =>
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff.2
      ⟨hR.1 hr, fun j hj => r90p2_commutator_mem_pCoreOf hKJ hRJ hR.2.2.1 hR.2.1 r hr j hj⟩
  exact r90p2_isSylow_of_maximal hR.2.1 hRC
    (fun x hx => (CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff.mp hx).1)
    (CFSG.LocalAnalysis.GLTheoremA.I142N.isSubnormal_le c.memJ.1)
    (r890_perfInter_le_left _ _) hR.2.2.2

private theorem r90p4_exists_lt {G : Type} [Group G] {K M R : Subgroup G} (hRM : R ≤ M)
    (hR : IsPGroup 2 R) (hKR : K ≤ Subgroup.normalizer (R : Set G)) (h : ¬ IsMaxKInv_890 K M R) :
    ∃ R' : Subgroup G, R < R' ∧ R' ≤ M ∧ IsPGroup 2 R' ∧
      K ≤ Subgroup.normalizer (R' : Set G) := by
  by_contra hcon
  refine h ⟨hRM, hR, hKR, fun R' hRR' hR'M hR'p hKR' => ?_⟩
  by_contra hne
  exact hcon ⟨R', lt_of_le_of_ne hRR' (Ne.symm hne), hR'M, hR'p, hKR'⟩

open CFSG.LocalAnalysis.UniquenessCase.UC22 in
private theorem r90p4_hmax {G : Type} [Group G] [Finite G] {D : Data G} {K R : Subgroup G}
    (h : ∀ N' R' : Subgroup G, KPair_890 D K N' R' → Nat.card R' ≤ Nat.card R) :
    ∀ N R'' : Subgroup G, N ∈ calMOf K → N ≠ D.M → R'' ≤ D.M ⊓ N → IsPGroup 2 R'' →
      K ≤ Subgroup.normalizer (R'' : Set G) → Nat.card R'' ≤ Nat.card R := by
  intro N R'' hN hNM hR'' hp hK
  by_cases hbot : R'' = ⊥
  · subst hbot
    rw [Subgroup.card_bot]
    exact Nat.card_pos
  · exact h N R'' ⟨hN, hNM, hR''.trans (inf_comm _ _).le, hp, hbot, hK⟩

theorem r890_lemma42 : Lemma42_890 := by
  intro G _ _ D K N R hP hbound hnmax
  obtain ⟨-, -, hRNM, hRp, hRne, hKR⟩ := hP
  obtain ⟨R', hRR', hR'M, hR'p, hKR'⟩ :=
    r90p4_exists_lt (hRNM.trans inf_le_right) hRp hKR hnmax
  exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.normalizer_le_of_lt
    hRp hRne hKR hR'p hRR' hR'M hKR' (r90p4_hmax hbound)

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 in
private theorem r90p5a_pCoreOf_le_centOverO2 {G : Type} [Group G] [Finite G] {M J : Subgroup G}
    (hJM : J ≤ M) (hMJ : M ≤ Subgroup.normalizer (J : Set G)) :
    pCoreOf 2 M ≤ F08.CentOverO2 M J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 M
  have hJQ : J ≤ Subgroup.normalizer (Q : Set G) :=
    hJM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  have hW : Q ⊓ J ≤ pCoreOf 2 J := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_inf_left
    exact fun j hj =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hJQ hj, Subgroup.le_normalizer hj⟩
  intro x hx
  have hxM : x ∈ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M hx
  refine CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff.2
    ⟨hxM, fun j hj => hW ⟨?_, ?_⟩⟩
  · have h1 : j * x⁻¹ * j⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 (hJQ hj) x⁻¹).1 (Q.inv_mem hx)
    have h2 := Q.mul_mem hx h1
    simpa [mul_assoc] using h2
  · have h1 : x * j * x⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 (hMJ hxM) j).1 hj
    exact J.mul_mem h1 (J.inv_mem hj)

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 in
private theorem r90p5a_pCoreOf_le {G : Type} [Group G] [Finite G] {M J R : Subgroup G}
    (hJM : J ≤ M) (hMJ : M ≤ Subgroup.normalizer (J : Set G))
    (hR : CFSG.ABGLocalTools.IsSylowOf 2 R (F08.CentOverO2 M J)) : pCoreOf 2 M ≤ R := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCM : F08.CentOverO2 M J ≤ M := fun x hx =>
    (CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff.1 hx).1
  have hS := hR.inf_of_le_normalizer (r90p5a_pCoreOf_le_centOverO2 hJM hMJ)
    (hCM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
  have hEq := hS.eq_of_le inf_le_right le_rfl (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
  exact hEq.le.trans inf_le_left

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 in
theorem r890_puSetup : PUSetup_890 := by
  intro G _ _ D L P J Y n c hLJ R hR
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLM : L ≤ D.M := CFSG.LocalAnalysis.GLTheoremA.I142N.isSubnormal_le c.set880.mem.1
  have hJM : J ≤ D.M := CFSG.LocalAnalysis.GLTheoremA.I142N.isSubnormal_le c.memJ.1
  have hLC : L ≤ F08.CentOverO2 D.M J := fun l hl =>
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff.2
      ⟨hLM hl, fun j hj => (hLJ (Subgroup.commutator_mem_commutator hl hj)).2⟩
  have hCM : F08.CentOverO2 D.M J ≤ D.M := fun x hx =>
    (CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff.1 hx).1
  have hRC := hR.le
  have hLRM : L ⊔ R ≤ D.M := sup_le hLM (hRC.trans hCM)
  refine ⟨hR.of_le le_sup_right (sup_le hLC hRC), ?_, ?_⟩
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 (hLRM.trans c.normal_L)
  · exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEleven.fstar_eq_pCoreOf_of_charTwo
      (CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le (D.standing.charTwo D.M D.maxLocal.1) hLRM
        ((r90p5a_pCoreOf_le hJM c.normal_J hR).trans le_sup_right))

open CFSG.LocalAnalysis.UniquenessCase.UC22 in
private theorem r90p5c_not_thin {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (h : IsSpor (Bar2 L) .J2) : ¬ F08.Thin8 L :=
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.not_thin8_of_two_le_pRank Nat.prime_three
    (by norm_num)
    (CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.two_le_pRank_of_bar2 Nat.prime_three
      (by norm_num) (two_le_pRank_three_of_isSpor_J2 h))

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.RankThreeUC.SourceSetting in
private theorem r90p5c_maxTwoLocals {G : Type} [Group G] [Finite G] {D : Data G}
    (h869 : F08.R869 D) {L : Subgroup G} (hL : L ∈ calC D.M) (hnt : ¬ F08.Thin8 L) :
    maxTwoLocalsContaining L = {D.M} := by
  have hN : calNOf L = {D.M} :=
    h869 L (Or.inl hL) L le_rfl (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L)) hnt
  simpa only [UniqueMax, calMOf, maxTwoLocalsContaining] using
    uc22p22u_uniqueMax_of_calN D (CFSG.LocalAnalysis.GLTheoremA.I142N.isSubnormal_le hL.1) hN

open CFSG.LocalAnalysis.RankThreeUC.SourceSetting.TwoGroupNormalizerMaxLocal in
theorem r890_puNormalizer : PUNormalizer_890 := by
  intro G _ _ D L P J Y n c h869 h885 C hC hCp hLC
  exact normalizer_le_of_maxTwoLocalsContaining_eq_singleton hC hCp hLC
    (r90p5c_maxTwoLocals h869 c.set880.mem (r90p5c_not_thin (h885 L P c.set880).1))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

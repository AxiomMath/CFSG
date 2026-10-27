module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InP11OfStrongly
import TauCeti.RepresentationTheory.CharacterTable.Solvable
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenGlueB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154UThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTen
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81 TwelveShort
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16h_e3_factor_permuting_three (D : Data G) (h111W : W3Thm111 G)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L) (hV₀ : V₀ = ⊥)
    (hm : MBarGT D.M V₀ V 2) {Y : Subgroup G} (hY3 : IsPGroup 3 ↥Y)
    (hperm : Permutes Y D.T) :
    ((Y ⊔ D.T) ⊓ Subgroup.centralizer (E3.cClos V 1 D.T : Set G)) ⊔
      ((Y ⊔ D.T) ⊓ Subgroup.normalizer (E3.wClos V 0 D.T : Set G)) = Y ⊔ D.T := by
  have hV1 : InCalV1 D.M D.T V := by
    rcases h.hyp16.hyp125.1 with ⟨hW, -⟩ | ⟨h0, -⟩
    · exact hW.1.1
    · exact (h0.1.1 hV₀).elim
  have hVV : InCalV D.M V := hV1.1
  have hVT : V ≤ D.T := by
    have hV2 : IsPGroup 2 V := CFSG.Open.IsElemAbelian.isPGroup hVV.2.2.2
    have hTM : IsSylowIn 2 D.T D.M := isSylowIn_of_le D D.sylowM.le
    have hnorm : (V.subgroupOf D.M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hVV.2.1).2 hVV.2.2.1
    exact IsSylowIn.le_of_normal hTM hVV.2.1 hnorm hV2
  have hm_bot : MBarGT D.M ⊥ V 2 := by rw [← hV₀]; exact hm
  have hspos' : 1 < E3.sParam hV1.1.2.2.2 :=
    lt_sParam_of_mBarGT D h111W hV1 hm_bot (mBarGT_mono hm_bot (by norm_num : 1 ≤ 2))
  have hspos : 1 < E3.sParam hV := by
    have heq : E3.sParam hV1.1.2.2.2 = E3.sParam hV :=
      congrArg (fun p => E3.sParam (V := V) p) (Subsingleton.elim hV1.1.2.2.2 hV)
    simpa [heq] using hspos'
  have hS : IsSylowIn 2 D.T (Y ⊔ D.T) := isSylowIn_of_le D le_sup_right
  have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hY3
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hT2
  have hdisj : Y ⊓ D.T = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num) Y D.T hY3 hT2)
  have hcard : Nat.card ↥(Y ⊔ D.T) = 3 ^ a * 2 ^ b := by
    rw [CFSG.ABGTheoremB.V56.card_sup_of_permutable hperm hdisj, ha, hb]
  have hsolv : Group.IsSolvable ↥(Y ⊔ D.T) :=
    TauCeti.isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_three Nat.prime_two hcard
  have hInE : E1.InE 1 (Y ⊔ D.T) :=
    (E1.inE_subgroupOf 1 (Y ⊔ D.T)).2
      (E1.inE_one_top_of_isSolvable (Nat.card ↥(Y ⊔ D.T)) ↥(Y ⊔ D.T) le_rfl hsolv)
  have h611 := six_eleven_three hV hS hInE (i := 0) (j := 1) (by simpa using hspos)
  simpa using h611

private theorem s16h_e3_good_v_data (D : Data G) {V₀ V L : Subgroup G}
    (h : Setting16 D V₀ V L) (hV₀ : V₀ = ⊥) :
    InCalV D.M V ∧ 8 ≤ Nat.card V ∧ V ≤ D.T := by
  have hV1 : InCalV1 D.M D.T V := by
    rcases h.hyp16.hyp125.1 with ⟨hW, -⟩ | ⟨h0, -⟩
    · exact hW.1.1
    · exact (h0.1.1 hV₀).elim
  have hVV : InCalV D.M V := hV1.1
  have hVbig : 8 ≤ Nat.card V := by
    rcases h.hyp16.hyp125.1 with ⟨hW, -⟩ | ⟨h0, -⟩
    · exact hW.1.2.1
    · exact (h0.1.1 hV₀).elim
  refine ⟨hVV, hVbig, ?_⟩
  have hV2 : IsPGroup 2 V := CFSG.Open.IsElemAbelian.isPGroup hVV.2.2.2
  have hTM : IsSylowIn 2 D.T D.M := isSylowIn_of_le D D.sylowM.le
  have hnorm : (V.subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVV.2.1).2 hVV.2.2.1
  exact IsSylowIn.le_of_normal hTM hVV.2.1 hnorm hV2

private theorem s16h_e3_good_cent_clos (D : Data G) {V : Subgroup G} {v : G} (hvV : v ∈ V)
    (hvT : ∀ t ∈ D.T, t * v = v * t)
    (hvC : Subgroup.centralizer ({v} : Set G) ≤ D.M) (hVT : V ≤ D.T) :
    ∀ j : ℕ, Subgroup.centralizer (E3.cClos V j D.T : Set G) ≤ D.M := by
  intro j
  have hv_mem : v ∈ E3.cClos V j D.T := by
    unfold E3.cClos
    exact Subgroup.mem_inf.mpr ⟨hVT hvV,
      Subgroup.mem_centralizer_iff.mpr (fun w hw => hvT w (E3.wClos_le j D.T hw))⟩
  exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hv_mem)).trans hvC

private theorem s16h_e3_good_v_le_wClos (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hVV : InCalV D.M V) (hVbig : 8 ≤ Nat.card V) (hVT : V ≤ D.T) :
    V ≤ E3.wClos V 1 D.T := by
  have hV2 : IsPGroup 2 V := CFSG.Open.IsElemAbelian.isPGroup hVV.2.2.2
  have hcardV : Nat.card ↥V = 2 ^ rk ↥V := card_eq_two_pow_of_isPGroup hV2
  have h3rk : 3 ≤ rk ↥V := by
    have h' : 8 ≤ 2 ^ rk ↥V := by rwa [hcardV] at hVbig
    have h'' : (2 : ℕ) ^ 3 ≤ 2 ^ rk ↥V := by norm_num; exact h'
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h''
  refine E3.le_wClos_of_mQuot_le_self hV hVT le_rfl ?_ ?_
  · rw [E3.mQuot_self]; norm_num
  · omega

private theorem s16h_e3_good_conj_mem_cClos (D : Data G) {V : Subgroup G} {v g : G}
    (hVW1 : V ≤ E3.wClos V 1 D.T) (hvV : v ∈ V)
    (hvT : ∀ t ∈ D.T, t * v = v * t)
    (hg : g ∈ Subgroup.normalizer (E3.wClos V 1 D.T : Set G)) :
    g * v * g⁻¹ ∈ E3.cClos V 1 D.T := by
  have hgv_mem : g * v * g⁻¹ ∈ E3.wClos V 1 D.T :=
    (Subgroup.mem_normalizer_iff.1 hg v).1 (hVW1 hvV)
  have hgv_cent : g * v * g⁻¹ ∈ Subgroup.centralizer (E3.wClos V 1 D.T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : g⁻¹ * w * g ∈ E3.wClos V 1 D.T :=
      (Subgroup.mem_normalizer_iff''.1 hg w).1 hw
    have hcomm : (g⁻¹ * w * g) * v = v * (g⁻¹ * w * g) :=
      hvT _ (E3.wClos_le 1 D.T hw')
    calc w * (g * v * g⁻¹) = g * ((g⁻¹ * w * g) * v) * g⁻¹ := by group
      _ = g * (v * (g⁻¹ * w * g)) * g⁻¹ := by rw [hcomm]
      _ = (g * v * g⁻¹) * w := by group
  unfold E3.cClos
  exact Subgroup.mem_inf.mpr ⟨E3.wClos_le 1 D.T hgv_mem, hgv_cent⟩

private theorem s16h_e3_good_normalizer_wClos (D : Data G)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    {V : Subgroup G} {v y : G} (hvV : v ∈ V) (hvT : ∀ t ∈ D.T, t * v = v * t)
    (hvC : Subgroup.centralizer ({v} : Set G) ≤ D.M) (hVW1 : V ≤ E3.wClos V 1 D.T)
    (hyord : orderOf y = 3)
    (hyC1 : y ∈ Subgroup.centralizer (E3.cClos V 1 D.T : Set G)) (hyM : y ∈ D.M) :
    Subgroup.normalizer (E3.wClos V 1 D.T : Set G) ≤ D.M := by
  intro g hg
  have hgv_C1 : g * v * g⁻¹ ∈ E3.cClos V 1 D.T :=
    s16h_e3_good_conj_mem_cClos D hVW1 hvV hvT hg
  have hycomm : (g * v * g⁻¹) * y = y * (g * v * g⁻¹) :=
    Subgroup.mem_centralizer_iff.1 hyC1 _ hgv_C1
  have hconj_v : g⁻¹ * y * g ∈ Subgroup.centralizer ({v} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    calc v * (g⁻¹ * y * g) = g⁻¹ * ((g * v * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * v * g⁻¹)) * g := by rw [hycomm]
      _ = (g⁻¹ * y * g) * v := by group
  have hconjM : g⁻¹ * y * g ∈ D.M := hvC hconj_v
  by_contra hgM
  have hyMmap : y ∈ D.M.map (MulAut.conj g).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * y * g, hconjM, ?_⟩
    change MulAut.conj g (g⁻¹ * y * g) = y
    rw [MulAut.conj_apply]
    group
  have hdvd : 3 ∣ Nat.card (D.M ⊓ D.M.map (MulAut.conj g).toMonoidHom : Subgroup G) := by
    have hmem : y ∈ D.M ⊓ D.M.map (MulAut.conj g).toMonoidHom := ⟨hyM, hyMmap⟩
    have h := Subgroup.orderOf_dvd_natCard (D.M ⊓ D.M.map (MulAut.conj g).toMonoidHom) hmem
    rwa [hyord] at h
  exact hsp.2.2 g hgM hdvd

private theorem s16h_e3_good_R_le_T (D : Data G) {V Y R : Subgroup G} {a b : ℕ}
    (hnot3 : ¬ 3 ∣ Nat.card R) (hcardH : Nat.card ↥(Y ⊔ D.T) = 3 ^ a * 2 ^ b)
    (hR_eq : R = (Y ⊔ D.T) ⊓ Subgroup.centralizer (E3.cClos V 1 D.T : Set G)) :
    R ≤ D.T := by
  have hR2 : IsPGroup 2 R := by
    rw [isPGroup_iff_card_dvd_pow]
    refine ⟨b, ?_⟩
    have hdvdH : Nat.card R ∣ Nat.card ↥(Y ⊔ D.T) := by
      rw [hR_eq]
      exact Subgroup.card_dvd_of_le inf_le_left
    rw [hcardH] at hdvdH
    have hcop : Nat.Coprime (Nat.card R) (3 ^ a) :=
      ((Nat.prime_three.coprime_iff_not_dvd).2 hnot3).symm.pow_right a
    exact (hcop.dvd_mul_left).1 hdvdH
  have hTc : D.T ≤ Subgroup.normalizer (E3.cClos V 1 D.T : Set G) :=
    Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_cClos (V := V) (i := 1) D.T)
  have hTNc : D.T ≤ Subgroup.normalizer
      (Subgroup.centralizer (E3.cClos V 1 D.T : Set G) : Set G) :=
    hTc.trans (CFSG.BenderSuzuki.le_normalizer_centralizer_of_le_normalizer
      (V := Subgroup.normalizer (E3.cClos V 1 D.T : Set G))
      (J := E3.cClos V 1 D.T) le_rfl)
  have hTR : D.T ≤ Subgroup.normalizer (R : Set G) := by
    rw [hR_eq]
    exact (le_inf (le_sup_right.trans Subgroup.le_normalizer) hTNc).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := Y ⊔ D.T)
        (K := Subgroup.centralizer (E3.cClos V 1 D.T : Set G)))
  have hS' : IsSylowIn 2 D.T (R ⊔ D.T) := isSylowIn_of_le D le_sup_right
  have hnormR : (R.subgroupOf (R ⊔ D.T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_left : R ≤ R ⊔ D.T)).2
      (sup_le Subgroup.le_normalizer hTR)
  exact IsSylowIn.le_of_normal hS' (le_sup_left : R ≤ R ⊔ D.T) hnormR hR2

private theorem s16h_e3_good_normalizer_wClos_zero (D : Data G) (h61 : UC6.R6_1 D)
    (h63 : UC6.R6_3 D) (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    {V Y : Subgroup G}
    (hfac : ((Y ⊔ D.T) ⊓ Subgroup.centralizer (E3.cClos V 1 D.T : Set G)) ⊔
      ((Y ⊔ D.T) ⊓ Subgroup.normalizer (E3.wClos V 0 D.T : Set G)) = Y ⊔ D.T)
    (hR_le_T : (Y ⊔ D.T) ⊓ Subgroup.centralizer (E3.cClos V 1 D.T : Set G) ≤ D.T)
    (hY3 : IsPGroup 3 ↥Y) (hYnc : ¬ IsCyclic ↥Y) (hYM : Y ≤ D.M)
    (hVV : InCalV D.M V) :
    Subgroup.normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
  have hTW0 : D.T ≤ Subgroup.normalizer (E3.wClos V 0 D.T : Set G) :=
    Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos (V := V) (i := 0) D.T)
  have hR_le_NH : (Y ⊔ D.T) ⊓ Subgroup.centralizer (E3.cClos V 1 D.T : Set G) ≤
      (Y ⊔ D.T) ⊓ Subgroup.normalizer (E3.wClos V 0 D.T : Set G) :=
    le_inf inf_le_left (hR_le_T.trans hTW0)
  have hH_eq : Y ⊔ D.T = (Y ⊔ D.T) ⊓ Subgroup.normalizer (E3.wClos V 0 D.T : Set G) :=
    hfac.symm.trans (sup_eq_right.mpr hR_le_NH)
  have hY_N : Y ≤ Subgroup.normalizer (E3.wClos V 0 D.T : Set G) := by
    intro y hy
    have hy' : y ∈ (Y ⊔ D.T) ⊓ Subgroup.normalizer (E3.wClos V 0 D.T : Set G) := by
      rw [← hH_eq]
      exact Subgroup.mem_sup_left hy
    exact (Subgroup.mem_inf.1 hy').2
  have huniq : UniqueMax D.M Y :=
    s16h_uniqueMax_of_noncyclic_three D h61 h63 hsp hY3 hYnc le_rfl hYM
  have hW0_ne : E3.wClos V 0 D.T ≠ ⊥ := wClos_zero_ne_bot D hVV
  have hW0_2 : IsPGroup 2 (E3.wClos V 0 D.T) := hT2.to_le (E3.wClos_le 0 D.T)
  exact normalizer_le_of_uniqueMax huniq hW0_ne hW0_2 hY_N

theorem false_of_permuting_three_big_of_stronglyEmbedded (D : Data G)
    (h63 : UC6.R6_3 D) (h126 : R126 D) (h1211 : R1211_1 D)
    (h111W : W3Thm111 G) (h6161ii : W3Lem616_1ii G)
    (hk : D.k = 1) (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hm : MBarGT D.M V₀ V 2) {Y : Subgroup G} (hYM : Y ≤ D.M) (hY3 : IsPGroup 3 ↥Y)
    (hYexp : ∀ y ∈ Y, y ^ 3 = 1) (hYnc : ¬ IsCyclic ↥Y) (hperm : Permutes Y D.T)
    (hbig : V₀ ≠ ⊥ ∨ 9 < Nat.card ↥Y) : False := by
  have hm' : MBarGT D.M V₀ V (D.k + 1) := by rw [hk]; exact hm
  have hP11 : F11.InP11 D Y :=
    inP11_of_strongly Nat.prime_three (by norm_num) hsp hYM hY3 hYexp hYnc hperm
  have hPStar : InPStar D V₀ Y := by
    rcases hbig with hne | hbig
    · exact (inPStar_iff_of_ne_bot hne Y).2 hP11
    · exact ⟨hP11, fun _ => ⟨3, Nat.prime_three, hY3, Or.inl (by norm_num; exact hbig)⟩⟩
  exact twelve_twelve D h63 h126 h1211 h111W h6161ii
    h.hyp16.hyp125 hm' Y hPStar

theorem false_of_permuting_three_good_of_stronglyEmbedded (D : Data G)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (h126 : R126 D)
    (h111W : W3Thm111 G) (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L) (hV₀ : V₀ = ⊥)
    (hm : MBarGT D.M V₀ V 2) {Y : Subgroup G} (hYM : Y ≤ D.M) (hY3 : IsPGroup 3 ↥Y)
    (hYnc : ¬ IsCyclic ↥Y) (hperm : Permutes Y D.T)
    {v : G} (hvV : v ∈ V) (hvT : ∀ t ∈ D.T, t * v = v * t)
    (hvC : Subgroup.centralizer ({v} : Set G) ≤ D.M) : False := by
  have hk : D.k = 1 := Data.k_eq_one_of_isStronglyPEmbedded D hsp
  have hV : IsElemAbelian 2 V := h.hyp16.hyp125.isElemAbelian
  obtain ⟨hVV, hVbig, hVT⟩ := s16h_e3_good_v_data D h hV₀
  have hHM : Y ⊔ D.T ≤ D.M := sup_le hYM D.sylowM.le
  have hfac := s16h_e3_factor_permuting_three D h111W hV h hV₀ hm hY3 hperm
  have hcent_clos := s16h_e3_good_cent_clos D hvV hvT hvC hVT
  have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hY3
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hT2
  have hdisj : Y ⊓ D.T = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num) Y D.T hY3 hT2)
  have hcardH : Nat.card ↥(Y ⊔ D.T) = 3 ^ a * 2 ^ b := by
    rw [CFSG.ABGTheoremB.V56.card_sup_of_permutable hperm hdisj, ha, hb]
  have hm1 : MBarGT D.M V₀ V (D.k + 1) := by rw [hk]; exact hm
  have hm0 : MBarGT D.M V₀ V (D.k + 0) := by
    rw [hk]
    exact mBarGT_mono hm (by norm_num)
  let R : Subgroup G := (Y ⊔ D.T) ⊓ Subgroup.centralizer (E3.cClos V 1 D.T : Set G)
  by_cases hcase : ∃ y ∈ R, orderOf y = 3
  · obtain ⟨y, hyR, hyord⟩ := hcase
    have hyH : y ∈ Y ⊔ D.T := (Subgroup.mem_inf.1 hyR).1
    have hyC1 : y ∈ Subgroup.centralizer (E3.cClos V 1 D.T : Set G) :=
      (Subgroup.mem_inf.1 hyR).2
    have hyM : y ∈ D.M := hHM hyH
    have hN1 : Subgroup.normalizer (E3.wClos V 1 D.T : Set G) ≤ D.M :=
      s16h_e3_good_normalizer_wClos D hsp hvV hvT hvC
        (s16h_e3_good_v_le_wClos D hV hVV hVbig hVT) hyord hyC1 hyM
    rcases twelve_ten_two D hx h61 h126 h111W h.hyp16.hyp125 hV₀ (i := 1) hm1 with hN | hC
    · exact hN hN1
    · exact hC (hcent_clos (D.k + 1))
  · have hnot3 : ¬ 3 ∣ Nat.card R := by
      intro h3dvd
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 (G := R) h3dvd
      exact hcase ⟨(z : G), z.2, by rw [Subgroup.orderOf_coe]; exact hz⟩
    have hR_le_T : R ≤ D.T := s16h_e3_good_R_le_T D hnot3 hcardH rfl
    have hNW0 := s16h_e3_good_normalizer_wClos_zero D h61 h63 hsp hfac hR_le_T
      hY3 hYnc hYM hVV
    rcases twelve_ten_two D hx h61 h126 h111W h.hyp16.hyp125 hV₀ (i := 0) hm0 with hN | hC
    · exact hN hNW0
    · exact hC (hcent_clos (D.k + 0))

theorem false_of_permuting_three_of_stronglyEmbedded (D : Data G)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (h126 : R126 D)
    (h1211 : R1211_1 D) (h111W : W3Thm111 G) (h6161ii : W3Lem616_1ii G)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hm : MBarGT D.M V₀ V 2) {Y : Subgroup G} (hYM : Y ≤ D.M) (hY3 : IsPGroup 3 ↥Y)
    (hYexp : ∀ y ∈ Y, y ^ 3 = 1) (hYnc : ¬ IsCyclic ↥Y) (hperm : Permutes Y D.T)
    (hcase : V₀ ≠ ⊥ ∨ 9 < Nat.card ↥Y ∨
      ∃ v ∈ V, (∀ t ∈ D.T, t * v = v * t) ∧ Subgroup.centralizer ({v} : Set G) ≤ D.M) :
    False := by
  have hk : D.k = 1 := Data.k_eq_one_of_isStronglyPEmbedded D hsp
  by_cases hV₀ : V₀ = ⊥
  · rcases hcase with hne | hbig | ⟨v, hvV, hvT, hvC⟩
    · exact absurd hV₀ hne
    · exact false_of_permuting_three_big_of_stronglyEmbedded D h63 h126 h1211 h111W h6161ii
        hk hsp h hm hYM hY3 hYexp hYnc hperm (Or.inr hbig)
    · exact false_of_permuting_three_good_of_stronglyEmbedded D hx h61 h63 h126 h111W hsp
        h hV₀ hm hYM hY3 hYnc hperm hvV hvT hvC
  · exact false_of_permuting_three_big_of_stronglyEmbedded D h63 h126 h1211 h111W h6161ii
      hk hsp h hm hYM hY3 hYexp hYnc hperm (Or.inl hV₀)

theorem false_of_permuting_three_of_weakClosure (D : Data G)
    (hx : DataExt D) (hSig : UC6S846.SigmaStd D)
    (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (h126 : R126 D) (h1211 : R1211_1 D)
    (h111W : W3Thm111 G) (h6161ii : W3Lem616_1ii G) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L) (h3 : 3 ∈ D.sig)
    (hm : MBarGT D.M V₀ V 2) {Y : Subgroup G} (hYM : Y ≤ D.M) (hY3 : IsPGroup 3 ↥Y)
    (hYexp : ∀ y ∈ Y, y ^ 3 = 1) (hYnc : ¬ IsCyclic ↥Y) (hperm : Permutes Y D.T)
    (hcase : V₀ ≠ ⊥ ∨ 9 < Nat.card ↥Y ∨
      ∃ v ∈ V, (∀ t ∈ D.T, t * v = v * t) ∧ Subgroup.centralizer ({v} : Set G) ≤ D.M) :
    False := by
  exact false_of_permuting_three_of_stronglyEmbedded D hx h61 h63 h126 h1211 h111W h6161ii
    (hSig.sig1_sp 3 (hσ ▸ h3)) h hm hYM hY3 hYexp hYnc hperm hcase

theorem s16h_e3_false_of_permuting_three (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L) (h3 : 3 ∈ D.sig)
    (hm : MBarGT D.M V₀ V 2) {Y : Subgroup G} (hYM : Y ≤ D.M) (hY3 : IsPGroup 3 ↥Y)
    (hYexp : ∀ y ∈ Y, y ^ 3 = 1) (hYnc : ¬ IsCyclic ↥Y) (hperm : Permutes Y D.T)
    (hcase : V₀ ≠ ⊥ ∨ 9 < Nat.card ↥Y ∨
      ∃ v ∈ V, (∀ t ∈ D.T, t * v = v * t) ∧ Subgroup.centralizer ({v} : Set G) ≤ D.M) :
    False :=
  false_of_permuting_three_of_weakClosure D S.hx S.hSig S.h61 S.h63 S.h126 S.h1211 S.h111W
    S.h6161ii hσ h h3 hm hYM hY3 hYexp hYnc hperm hcase

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

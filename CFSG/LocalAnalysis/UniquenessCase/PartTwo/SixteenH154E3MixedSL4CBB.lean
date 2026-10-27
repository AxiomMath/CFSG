module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTen
import TauCeti.RepresentationTheory.CharacterTable.Solvable
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81 TwelveShort
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_factor_permuting_three_of_mbar (D : Data G) (S : s16h_Std D)
    (hσ : D.sig = D.sig1) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (h : Setting16 D V₀ V L) (hV₀ : V₀ = ⊥) (hm : MBarGT D.M V₀ V D.k)
    {Y : Subgroup G} (hYM : Y ≤ D.M) (hY3 : IsPGroup 3 ↥Y) (hperm : Permutes Y D.T) :
    ((Y ⊔ D.T) ⊓ Subgroup.centralizer (E3.cClos V 1 D.T : Set G)) ⊔
      ((Y ⊔ D.T) ⊓ Subgroup.normalizer (E3.wClos V 0 D.T : Set G)) = Y ⊔ D.T := by
  have hV1 : InCalV1 D.M D.T V := by
    rcases h.hyp16.hyp125.1 with ⟨hW, -⟩ | ⟨h0, -⟩
    · exact hW.1.1
    · exact (h0.1.1 hV₀).elim
  have hVV : InCalV D.M V := hV1.1
  have hm_bot : MBarGT D.M ⊥ V D.k := by rw [← hV₀]; exact hm
  have hVbig : 4 ≤ Nat.card V := by
    rcases h.hyp16.hyp125.1 with ⟨hW, -⟩ | ⟨h0, -⟩
    · exact le_trans (by norm_num) hW.1.2.1
    · exact (h0.1.1 hV₀).elim
  have hspos' : 1 < E3.sParam hV1.1.2.2.2 := by
    have h1 := TwelveTen.one_lt_rMV D S.hx S.h61 hVV hVbig
    have hr : (1 : ℕ∞) < E3.rParam V := by
      rwa [rMV_eq_rParam_of_inCalV D hVV] at h1
    have hm' : 1 < E3.mParam (autI hV1.1.2.2.2 ⊤) := by
      have hle : 1 ≤ D.k := one_le_k D
      exact lt_of_le_of_lt hle ((mBarGT_bot_iff_lt_mParam_autI D hVV D.k).1 hm_bot)
    exact E3.lt_sParam_of_lt hV1.1.2.2.2 hr hm'
  have hspos : 1 < E3.sParam hV := by
    have heq : E3.sParam hV1.1.2.2.2 = E3.sParam hV :=
      congrArg (fun p => E3.sParam (V := V) p) (Subsingleton.elim hV1.1.2.2.2 hV)
    simpa [heq] using hspos'
  have hS : IsSylowIn 2 D.T (Y ⊔ D.T) := isSylowIn_of_le D le_sup_right
  have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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

theorem s16h_e3_false_of_permuting_three_no3 (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L) (hV₀ : V₀ = ⊥)
    (h3 : 3 ∈ D.sig) (hm : MBarGT D.M V₀ V D.k)
    {Y : Subgroup G} (hYM : Y ≤ D.M) (hY3 : IsPGroup 3 ↥Y)
    (hYnc : ¬ IsCyclic ↥Y) (hperm : Permutes Y D.T)
    (hno3 : ∀ r ∈ (Y ⊔ D.T) ⊓ Subgroup.centralizer (E3.cClos V 1 D.T : Set G),
      orderOf r ≠ 3)
    {v : G} (hvc : v ∈ E3.cClos V (D.k + 0) D.T) (hvC : Subgroup.centralizer ({v} : Set G) ≤ D.M) :
    False := by
  have hV1 : InCalV1 D.M D.T V := by
    rcases h.hyp16.hyp125.1 with ⟨hW, -⟩ | ⟨h0, -⟩
    · exact hW.1.1
    · exact (h0.1.1 hV₀).elim
  have hVV : InCalV D.M V := hV1.1
  have hHM : Y ⊔ D.T ≤ D.M := sup_le hYM D.sylowM.le
  have hfac := s16h_e3_factor_permuting_three_of_mbar D S hσ hV h hV₀ hm hYM hY3 hperm
  have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hY3
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hT2
  have hdisj : Y ⊓ D.T = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num) Y D.T hY3 hT2)
  have hcardH : Nat.card ↥(Y ⊔ D.T) = 3 ^ a * 2 ^ b := by
    rw [CFSG.ABGTheoremB.V56.card_sup_of_permutable hperm hdisj, ha, hb]
  let R : Subgroup G := (Y ⊔ D.T) ⊓ Subgroup.centralizer (E3.cClos V 1 D.T : Set G)
  have hR_eq : R = (Y ⊔ D.T) ⊓ Subgroup.centralizer (E3.cClos V 1 D.T : Set G) := rfl
  have hnot3 : ¬ 3 ∣ Nat.card R := by
    intro h3dvd
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 (G := R) h3dvd
    exact hno3 (z : G) z.2 (by rw [Subgroup.orderOf_coe]; exact hz)
  have hR2 : IsPGroup 2 R := by
    rw [isPGroup_iff_card_dvd_pow]
    refine ⟨b, ?_⟩
    have hdvdH : Nat.card R ∣ Nat.card ↥(Y ⊔ D.T) := Subgroup.card_dvd_of_le inf_le_left
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
  have hR_le_T : R ≤ D.T :=
    IsSylowIn.le_of_normal hS' (le_sup_left : R ≤ R ⊔ D.T) hnormR hR2
  have hTW0 : D.T ≤ Subgroup.normalizer (E3.wClos V 0 D.T : Set G) :=
    Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos (V := V) (i := 0) D.T)
  have hR_le_NH : R ≤ (Y ⊔ D.T) ⊓ Subgroup.normalizer (E3.wClos V 0 D.T : Set G) :=
    le_inf inf_le_left (hR_le_T.trans hTW0)
  have hH_eq : Y ⊔ D.T = (Y ⊔ D.T) ⊓ Subgroup.normalizer (E3.wClos V 0 D.T : Set G) :=
    hfac.symm.trans (sup_eq_right.mpr hR_le_NH)
  have hY_N : Y ≤ Subgroup.normalizer (E3.wClos V 0 D.T : Set G) := by
    intro y hy
    have hy' : y ∈ (Y ⊔ D.T) ⊓ Subgroup.normalizer (E3.wClos V 0 D.T : Set G) := by
      rw [← hH_eq]
      exact Subgroup.mem_sup_left hy
    exact (Subgroup.mem_inf.1 hy').2
  have huniq : UniqueMax D.M Y := S.h61 3 h3 Y hYM hY3 hYnc
  have hW0_ne : E3.wClos V 0 D.T ≠ ⊥ := wClos_zero_ne_bot D hVV
  have hW0_2 : IsPGroup 2 (E3.wClos V 0 D.T) := hT2.to_le (E3.wClos_le 0 D.T)
  have hNW0 : Subgroup.normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M :=
    normalizer_le_of_uniqueMax huniq hW0_ne hW0_2 hY_N
  have hcent_clos : Subgroup.centralizer (E3.cClos V (D.k + 0) D.T : Set G) ≤ D.M :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hvc)).trans hvC
  rcases twelve_ten_two D S.hx S.h61 S.h126 S.h111W h.hyp151.hyp125 hV₀ (i := 0)
    (by simpa using hm) with hN | hC
  · exact hN hNW0
  · exact hC hcent_clos

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

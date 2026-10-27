module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenEightThreeY
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenEightThreeFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenEightOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenEightF
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem4
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem le_cClos_of_six_three (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    {n : ℕ} (h63 : ∀ v ∈ V, (∀ w ∈ E3.wClos V n D.T, ⁅v, w⁆ ∈ V₀) →
      v ∈ centralizer (E3.wClos V n D.T : Set G)) :
    V₀ ≤ E3.cClos V n D.T := by
  intro v hv
  have hvV : v ∈ V := h.pairFacts.le hv
  refine ⟨s15_13A_le_T h hvV, h63 v hvV fun w hw => ?_⟩
  have hwM : w ∈ D.M := D.sylowM.le (E3.wClos_le n D.T hw)
  have hw0 : w * v⁻¹ * w⁻¹ ∈ V₀ :=
    (mem_normalizer_iff.1 (h.pairFacts.le_normalizer₀ hwM) v⁻¹).1 (V₀.inv_mem hv)
  have he : ⁅v, w⁆ = v * (w * v⁻¹ * w⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [he]
  exact V₀.mul_mem hv hw0

theorem exists_mem_cClos_not_mem_V₀_of_six_three (D : Data G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hV₀ : V₀ ≠ ⊥) {n : ℕ}
    (h63 : ∀ v ∈ V, (∀ w ∈ E3.wClos V n D.T, ⁅v, w⁆ ∈ V₀) →
      v ∈ centralizer (E3.wClos V n D.T : Set G)) :
    ∃ v ∈ V, v ∉ V₀ ∧ v ∈ E3.cClos V n D.T := by
  have hV := h.isElemAbelian
  have hP := h.pairFacts
  have hne : V₀ ≠ V := (TwelveTwentyThree.ne_and_conjGenerated_of_hyp125 h hV₀).1
  have hnt : Nontrivial (Vtil V₀ V hV) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have hc := card_Vtil_eq V₀ V hV hP.le
    by_contra hle
    have hpos : 0 < Nat.card (Vtil V₀ V hV) := Nat.card_pos
    have h1 : Nat.card (Vtil V₀ V hV) = 1 := by omega
    rw [h1, mul_one] at hc
    exact hne (Subgroup.eq_of_le_of_card_ge hP.le hc.le)
  have hTbar2 : IsPGroup 2 ↥(barSub V₀ V hV D.T) :=
    s15_LP_isPGroup_barSub hV D.sylowM.isPGroup
  have hfix : fixV (barSub V₀ V hV D.T) ≠ ⊥ :=
    @CFSG.Quasithin.MS93.S38E.fixV_ne_bot_of_isPGroup (Vtil V₀ V hV) _ _ hnt
      (s15_Infra_vtil_sq_eq_one V₀ V hV) (barSub V₀ V hV D.T) hTbar2
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hfix
  obtain ⟨x, hx⟩ := mkTil_surjective V₀ V hV (y : Vtil V₀ V hV)
  refine ⟨x.val, x.val_mem, ?_, s15_13A_le_T (D := D) h x.val_mem, ?_⟩
  · intro hv0
    apply hy1
    have h1 : mkTil V₀ V hV x = 1 :=
      (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) x).2 (by
        change x.val ∈ V₀
        exact hv0)
    rw [hx] at h1
    exact Subtype.ext h1
  · have hvpre : x.val ∈ preCTilde V₀ V D.T hV := by
      rw [preCTilde]
      exact (mem_preTil V₀ V hV _).2 ⟨x, rfl, by rw [hx]; exact y.2⟩
    have hDT : D.T ≤ stabTil V₀ V :=
      le_inf (D.sylowM.le.trans (le_of_eq h.normalizer_eq.symm))
        (D.sylowM.le.trans hP.le_normalizer₀)
    have hvT : ∀ t ∈ D.T, ⁅x.val, t⁆ ∈ V₀ := fun t ht =>
      (mem_preCTilde_iff hV hDT x.val_mem).1 hvpre t ht
    exact h63 x.val x.val_mem fun w hw => hvT w (E3.wClos_le n D.T hw)

theorem barSub_eq_bot_of_normal_of_le_centralizer (D : Data G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hV₀ : V₀ ≠ ⊥) {J : Subgroup G} (hJM : J ≤ D.M)
    (hMJ : D.M ≤ normalizer (J : Set G)) {v : G} (hvV : v ∈ V) (hv0 : v ∉ V₀)
    (hJv : J ≤ centralizer ({v} : Set G)) : barSub V₀ V h.isElemAbelian J = ⊥ := by
  have hV := h.isElemAbelian
  have hP := h.pairFacts
  have hMstab : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hstabJ : J ≤ stabTil V₀ V := hJM.trans hMstab
  have hfixne : fixV (barSub V₀ V hV J) ≠ ⊥ := by
    intro hbot
    have hvpre : v ∈ preCTilde V₀ V J hV := by
      rw [mem_preCTilde_iff hV hstabJ hvV]
      intro d hd
      have hcomm : v * d = d * v :=
        Subgroup.mem_centralizer_iff.1 (hJv hd) v (Set.mem_singleton v)
      rw [commutatorElement_eq_one_iff_mul_comm.2 hcomm]
      exact V₀.one_mem
    have hvpre' : v ∈ preTil V₀ V hV (fixV (barSub V₀ V hV J)) := hvpre
    rw [hbot, preTil_bot, inf_eq_right.mpr hP.le] at hvpre'
    exact hv0 hvpre'
  have hconj : ConjGenerated D.M V₀ V :=
    (TwelveTwentyThree.ne_and_conjGenerated_of_hyp125 h hV₀).2
  have hfix : fixV (barSub V₀ V hV J) = ⊤ := by
    have hnormal : ((barSub V₀ V hV J).subgroupOf (Mbar D.M V₀ V hV)).Normal :=
      barSub_subgroupOf_mbar_normal hV hJM hMJ
    have hstable : StableUnder (Mbar D.M V₀ V hV) (fixV (barSub V₀ V hV J)) := by
      refine stableUnder_fixV (fun y hy k hk => ?_)
      have hle : barSub V₀ V hV J ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hJM
      have hkmem : (⟨k, hle hk⟩ : Mbar D.M V₀ V hV) ∈
          (barSub V₀ V hV J).subgroupOf (Mbar D.M V₀ V hV) :=
        Subgroup.mem_subgroupOf.2 hk
      have h1 := hnormal.conj_mem (⟨k, hle hk⟩ : Mbar D.M V₀ V hV) hkmem
        (⟨y, hy⟩ : Mbar D.M V₀ V hV)
      simpa using Subgroup.mem_subgroupOf.1 h1
    rcases eq_bot_or_eq_top_of_stable hV hP.le_normalizer hP.le_normalizer₀ hconj
      hstable with hbot | htop
    · exact absurd hbot hfixne
    · exact htop
  by_contra hne
  exact fixV_ne_top hne hfix

theorem le_centralizer_of_barSub_eq_bot (D : Data G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) {J : Subgroup G} (hJM : J ≤ D.M)
    (hJbar : barSub V₀ V h.isElemAbelian J = ⊥) (hJ0 : J ≤ centralizer (V₀ : Set G)) :
    (⁅J, J⁆ = J → J ≤ centralizer (V : Set G)) ∧
      ∀ y ∈ J, Odd (orderOf y) → y ∈ centralizer (V : Set G) := by
  have hV := h.isElemAbelian
  have hP := h.pairFacts
  have hJC : J ≤ F11.CTilde D.M V₀ V :=
    (barSub_eq_bot_iff hV hP.le_normalizer hP.le_normalizer₀ hJM).1 hJbar
  have hmod : ∀ l ∈ J, ∀ v ∈ V, l * v * l⁻¹ * v⁻¹ ∈ V₀ := fun l hl v hv =>
    centralizesMod_of_mem_cTilde hV hP.le_normalizer hP.le_normalizer₀ (hJC hl) v hv
  have hV₀ab : ∀ a ∈ V₀, ∀ b ∈ V₀, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hP.elemAbelian₀.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  refine ⟨fun hperf => ElevenNine.le_centralizer_of_perfect_of_sub hperf hV₀ab hJ0 hmod, ?_⟩
  intro y hy hodd
  exact CFSG.Quasithin.H13.mem_centralizer_of_odd_ch62 hV hP.le hodd (pow_orderOf_eq_one y)
    (fun u hu => ((Subgroup.mem_centralizer_iff.1 (hJ0 hy)) u hu).symm) (hmod y hy)

theorem uniqueMax_of_isU3_le (D : Data G) (h61 : UC6.R6_1 D) {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) (hU3 : IsU3 (Bar2 L) 2) {H : Subgroup G}
    (hLH : L ≤ H) (hHM : H ≤ D.M) : UniqueMax D.M H := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hbr5 : CFSG.pRank 5 ↥(⊤ : Subgroup (Bar2 L)) =
      CFSG.Open.pRank 5 (⊤ : Subgroup (Bar2 L)) :=
    (CFSG.SectionRank.pRank_eq_open_pRank_top 5 ↥(⊤ : Subgroup (Bar2 L))).trans
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 5) (⊤ : Subgroup (Bar2 L))).symm
  have hr2 : CFSG.Open.pRank 5 (⊤ : Subgroup (Bar2 L)) = 2 :=
    hbr5.symm.trans (Inputs1719.kU34Data_fiveRank (Bar2 L) hU3)
  have hrankL : 2 ≤ CFSG.Open.pRank 5 L :=
    S17.two_le_pRank_of_bar2 Nat.prime_five (by norm_num) (by rw [hr2])
  obtain ⟨E, hEL, hEel, hEcard⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank (M := L) Nat.prime_five (k := 2) hrankL
  have hEp : IsPGroup 5 E := by
    intro g
    exact ⟨1, Subtype.ext (by simpa using hEel.2 (g : G) g.2)⟩
  have hEnc : ¬ IsCyclic E :=
    CFSG.LocalAnalysis.RankThreeUC.S15.not_isCyclic_of_isElemAbelian Nat.prime_five
      (by norm_num) hEel hEcard
  exact c23_uniqueMax_of_noncyclic D h61 (h.p_eq ▸ h.hyp.hp) hEp hEnc (hEL.trans hLH) hHM

theorem not_normalizer_wClos_zero_le_19 (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h126 : R126 D) {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) (h81 : R19_8_1At D V₀ V p L K h)
    (h82 : R19_8_2At D V₀ V p L K h) :
    ¬ normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have hV₀ : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.hyp.big
  have hm4 : mBar D.M V₀ V h.hyp.isElemAbelian = 4 := h82
  have hk : D.k ≤ 2 := TwelveSeven.k_le_two D
  have hkm : 0 + D.k < mBar D.M V₀ V h.hyp.isElemAbelian := by omega
  have hkr : ((0 + D.k : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_lt_of_le (ENat.natCast_lt_natCast.2 (by omega)) h81.1
  have hno : ∀ g : G, ¬ InCalO1 (0 + D.k) D.M V₀ V g := by
    intro g hg
    have hmem : conjSubgroup V g ∈ calO (0 + D.k) D.M V₀ V := ⟨g, rfl, hg.1⟩
    rw [h81.2.1 (0 + D.k) hkm] at hmem
    exact hmem
  exact S18.not_normalizer_wClos_le_of_no_calO1 D hx h61 h127 h1114 h126 h.hyp.hyp125 hV₀
    hkr hkm hno

theorem false_of_uniqueMax_normalizer_19 (D : Data G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1114 : R1114 D) (h126 : R126 D) {V₀ V : Subgroup G}
    {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) (h81 : R19_8_1At D V₀ V p L K h)
    (h82 : R19_8_2At D V₀ V p L K h)
    (hU : UniqueMax D.M (D.M ⊓ normalizer (E3.wClos V 0 D.T : Set G))) : False := by
  have hp125 := h.hyp.hyp125
  have hW0le : V ≤ E3.wClos V 0 D.T := s15_13A_le_wClos hp125
  have hW0ne : E3.wClos V 0 D.T ≠ ⊥ := fun hbot =>
    hp125.pairFacts.ne_bot (le_bot_iff.1 (hbot ▸ hW0le))
  have hW02 : IsPGroup 2 (E3.wClos V 0 D.T) :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM).2.1.to_le (E3.wClos_le 0 D.T)
  exact not_normalizer_wClos_zero_le_19 D hx h61 h127 h1114 h126 h h81 h82
    (uc22p22p_le_of_uniqueMax hU ⟨E3.wClos V 0 D.T, hW0ne, hW02, rfl⟩ inf_le_right)

theorem alt_18_1_3_19 (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1114 : R1114 D) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (h81 : R19_8_1At D V₀ V p L K h)
    (h82 : R19_8_2At D V₀ V p L K h) {H : Subgroup G} (hTH : D.T ≤ H) (hFH : InFSq 2 H) :
    H ≤ normalizer (E3.wClos V 0 D.T : Set G) ∨
      CFSG.Quasithin.twoResidual H ≤ centralizer (E3.cClos V 2 D.T : Set G) := by
  have hV₀ : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.hyp.big
  have hm4 : mBar D.M V₀ V h.hyp.isElemAbelian = 4 := h82
  have hH := (weakClosureSetting_of_hyp125 D hx h61 h127 h1114 h.hyp.hyp125 hV₀).hyp6H
  have hkr : ((2 : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_lt_of_le (ENat.natCast_lt_natCast.2 (by omega)) h81.1
  have hno : ∀ g : G, ¬ InCalO1 2 D.M V₀ V g := by
    intro g hg
    have hmem : conjSubgroup V g ∈ calO 2 D.M V₀ V := ⟨g, rfl, hg.1⟩
    rw [h81.2.1 2 (by omega)] at hmem
    exact hmem
  rcases TwelveEighteen.twelve_eighteen_three_of_no_calO1 hH hV₀ (i := 0) (n := 2) (k := 2)
    le_rfl hkr (by omega) hno (TwelveShort.isSylowIn_of_le D hTH) hFH with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Subgroup.le_centralizer_iff.1
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1))

theorem gap19_8_3At_of_five (D : Data G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1114 : R1114 D) (h126 : R126 D)
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    (hY5 : IsL2 (Bar2 L) 2 → ∃ y ∈ D.M, orderOf y = 5 ∧ Permutes (Subgroup.zpowers y) D.T ∧
      InFSq 2 (Subgroup.zpowers y ⊔ D.T) ∧
      UC22.conjClosure D.M (Subgroup.zpowers y) ≤
        CFSG.Quasithin.twoResidual (Subgroup.zpowers y ⊔ D.T) ∧
      ∀ J : Subgroup G, J ≤ D.M → ⁅J, J⁆ = J →
        ⁅Subgroup.zpowers y, J⁆ ≤ pCoreOf 2 D.M)
    (hF : ((L.subgroupOf D.M).Normal ∧ (K.subgroupOf D.M).Normal ∧ InFSq 2 (L ⊔ D.T) ∧
        InFSq 2 (K ⊔ D.T)) ∨ InFSq 2 (L ⊔ K ⊔ D.T)) :
    Gap19_8_3At D V₀ V p L K h := by
  intro h3 h81 h82 _ h63
  exfalso
  have hV₀ : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.hyp.big
  have hp125 := h.hyp.hyp125
  have hV := h.hyp.isElemAbelian
  have hP := hp125.pairFacts
  have h5 : 5 ∈ D.sig := h.p_eq ▸ h.hyp.hp
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hK.1
  have h5L : 5 ∣ Nat.card L := (h.p_eq ▸ h.hyp.hL.2 : 5 ∈ piSet L).2
  have h5K : 5 ∣ Nat.card K := UC22.InS3.UC49.five_dvd_card_of_isAlt h.hKshape
  have hLp : ⁅L, L⁆ = L := h.hyp.hL.1.2.1
  have hKp : ⁅K, K⁆ = K := h.hK.2.1
  have hLC0 : L ≤ centralizer (V₀ : Set G) :=
    le_sup_left.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h3)
  have hKC0 : K ≤ centralizer (V₀ : Set G) :=
    le_sup_right.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h3)
  have hV0C : V₀ ≤ E3.cClos V 2 D.T := le_cClos_of_six_three D hp125 h63
  obtain ⟨v, hvV, hv0, hvc⟩ := exists_mem_cClos_not_mem_V₀_of_six_three D hp125 hV₀ h63
  have hCv : centralizer (E3.cClos V 2 D.T : Set G) ≤ centralizer ({v} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 hvc)
  have hC0 : centralizer (E3.cClos V 2 D.T : Set G) ≤ centralizer (V₀ : Set G) :=
    Subgroup.centralizer_le hV0C
  have hbar : ∀ J : Subgroup G, J ≤ D.M → D.M ≤ normalizer (J : Set G) →
      J ≤ centralizer (E3.cClos V 2 D.T : Set G) → barSub V₀ V hV J = ⊥ :=
    fun J hJM hMJ hJC =>
      barSub_eq_bot_of_normal_of_le_centralizer D hp125 hV₀ hJM hMJ hvV hv0 (hJC.trans hCv)
  have halt : ∀ H : Subgroup G, D.T ≤ H → InFSq 2 H →
      H ≤ normalizer (E3.wClos V 0 D.T : Set G) ∨
        CFSG.Quasithin.twoResidual H ≤ centralizer (E3.cClos V 2 D.T : Set G) :=
    fun H hTH hFH => alt_18_1_3_19 D hx h61 h127 h1114 h h81 h82 hTH hFH
  have hres : ∀ {J H : Subgroup G}, J ≤ H → ⁅J, J⁆ = J →
      J ≤ CFSG.Quasithin.twoResidual H :=
    fun hJH hJ => (CFSG.Quasithin.C124.twoResidual_eq_self_of_perfect' hJ).symm.le.trans
      (CFSG.Quasithin.F6.twoResidual_mono hJH)
  have hfalseN : ∀ {Y J : Subgroup G}, Y ≤ D.M → J ≤ D.M →
      Y ≤ normalizer (E3.wClos V 0 D.T : Set G) → J ≤ normalizer (E3.wClos V 0 D.T : Set G) →
      ⁅Y, J⁆ ≤ pCoreOf 2 D.M → ⁅J, J⁆ = J → 5 ∣ Nat.card J → 5 ∣ Nat.card Y → False :=
    fun hYM hJM hYN hJN hYJ hJp h5J h5Y =>
      false_of_uniqueMax_normalizer_19 D hx h61 h127 h1114 h126 h h81 h82
        (uniqueMax_of_commutator_le_pCoreOf D h61 h5 inf_le_left (le_inf hYM hYN)
          (le_inf hJM hJN) hYJ hJp h5J h5Y)
  have hfalseC : ∀ {X : Subgroup G}, X ≤ centralizer (V : Set G) → UniqueMax D.M X → False :=
    fun hXC hU =>
      (twelve_nine D h127 hp125).1 (uc22p22u_isTI_of_uniqueMax D hV hP.le_normalizer hXC hU)
  have hLK : ⁅L, K⁆ ≤ pCoreOf 2 D.M :=
    ((calC_commutator_le_of_ne h.hyp.hL.1 h.hK (Ne.symm h.hne)).trans inf_le_left).trans
      (UC22.P22s.pCoreOf_le_of_isSubnormal h.hyp.hL.1.1)
  have hKL : ⁅K, L⁆ ≤ pCoreOf 2 D.M := by rw [Subgroup.commutator_comm]; exact hLK
  have hbot2 : barSub V₀ V hV L = ⊥ → barSub V₀ V hV K = ⊥ → False := fun hL hK => by
    rcases barSub_ne_bot_or_19 D h61 h127 h h3 with hL' | hK'
    · exact hL' hL
    · exact hK' hK
  rcases hF with ⟨hLn, hKn, hFL, hFK⟩ | hFLK
  ·
    have hMLn : D.M ≤ normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hLn
    have hMKn : D.M ≤ normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).1 hKn
    have hJV : ∀ {J : Subgroup G}, J ≤ D.M → D.M ≤ normalizer (J : Set G) → ⁅J, J⁆ = J →
        J ≤ centralizer (E3.cClos V 2 D.T : Set G) →
        barSub V₀ V hV J = ⊥ ∧ J ≤ centralizer (V : Set G) := fun hJM hMJ hJp hJC =>
      ⟨hbar _ hJM hMJ hJC, (le_centralizer_of_barSub_eq_bot D hp125 hJM
        (hbar _ hJM hMJ hJC) (hJC.trans hC0)).1 hJp⟩
    rcases h.shape with hL2 | hU3
    ·
      have hmixed : ∀ {J₁ J₂ : Subgroup G}, J₁ ≤ D.M → J₂ ≤ D.M → ⁅J₁, J₁⁆ = J₁ →
          ⁅J₂, J₂⁆ = J₂ → 5 ∣ Nat.card J₁ → 5 ∣ Nat.card J₂ →
          J₁ ≤ normalizer (E3.wClos V 0 D.T : Set G) → J₂ ≤ centralizer (V : Set G) →
          False := by
        intro J₁ J₂ hJ₁M hJ₂M hJ₁p hJ₂p h5J₁ h5J₂ hJ₁N hJ₂V
        obtain ⟨y, hyM, hy5, -, hFY, hYres, hYJ⟩ := hY5 hL2
        have h5Y : 5 ∣ Nat.card (Subgroup.zpowers y) := by rw [Nat.card_zpowers, hy5]
        have hYM : Subgroup.zpowers y ≤ D.M := Subgroup.zpowers_le.2 hyM
        rcases halt _ le_sup_right hFY with hYN | hYC
        · exact hfalseN hYM hJ₁M (le_sup_left.trans hYN) hJ₁N (hYJ J₁ hJ₁M hJ₁p) hJ₁p h5J₁
            h5Y
        · set N : Subgroup G := UC22.conjClosure D.M (Subgroup.zpowers y)
          have hNM : N ≤ D.M := TwelveTwentyThree.conjClosure_le hYM
          have hMN : D.M ≤ normalizer (N : Set G) :=
            TwelveTwentyThree.le_normalizer_conjClosure D.M _
          have hNC : N ≤ centralizer (E3.cClos V 2 D.T : Set G) := hYres.trans hYC
          have hyN : y ∈ N := TwelveTwentyThree.le_conjClosure D.M _ (Subgroup.mem_zpowers y)
          have hyV : y ∈ centralizer (V : Set G) :=
            (le_centralizer_of_barSub_eq_bot D hp125 hNM (hbar N hNM hMN hNC)
              (hNC.trans hC0)).2 y hyN (by rw [hy5]; decide)
          have hYV : Subgroup.zpowers y ≤ centralizer (V : Set G) := Subgroup.zpowers_le.2 hyV
          exact hfalseC (sup_le hYV hJ₂V)
            (uniqueMax_of_commutator_le_pCoreOf D h61 h5 (sup_le hYM hJ₂M) le_sup_left
              le_sup_right (hYJ J₂ hJ₂M hJ₂p) hJ₂p h5J₂ h5Y)
      rcases halt _ le_sup_right hFL with hLN | hLC
      · rcases halt _ le_sup_right hFK with hKN | hKC
        · exact hfalseN hLM hKM (le_sup_left.trans hLN) (le_sup_left.trans hKN) hLK hKp h5K h5L
        · exact hmixed hLM hKM hLp hKp h5L h5K (le_sup_left.trans hLN)
            (hJV hKM hMKn hKp ((hres le_sup_left hKp).trans hKC)).2
      · have hL' := hJV hLM hMLn hLp ((hres le_sup_left hLp).trans hLC)
        rcases halt _ le_sup_right hFK with hKN | hKC
        · exact hmixed hKM hLM hKp hLp h5K h5L (le_sup_left.trans hKN) hL'.2
        · exact hbot2 hL'.1 (hJV hKM hMKn hKp ((hres le_sup_left hKp).trans hKC)).1
    ·
      rcases halt _ le_sup_right hFL with hLN | hLC
      · exact false_of_uniqueMax_normalizer_19 D hx h61 h127 h1114 h126 h h81 h82
          (uniqueMax_of_isU3_le D h61 h hU3 (le_inf hLM (le_sup_left.trans hLN))
            inf_le_left)
      · exact hfalseC (hJV hLM hMLn hLp ((hres le_sup_left hLp).trans hLC)).2
          (uniqueMax_of_isU3_le D h61 h hU3 le_rfl hLM)
  ·
    rcases halt _ le_sup_right hFLK with hN | hC
    · exact hfalseN hLM hKM ((le_sup_left.trans le_sup_left).trans hN)
        ((le_sup_right.trans le_sup_left).trans hN) hLK hKp h5K h5L
    · have hLC : L ≤ centralizer (E3.cClos V 2 D.T : Set G) :=
        (hres (le_sup_left.trans le_sup_left) hLp).trans hC
      have hKC : K ≤ centralizer (E3.cClos V 2 D.T : Set G) :=
        (hres (le_sup_right.trans le_sup_left) hKp).trans hC
      rcases dichotomy_19 h with ⟨hXeq, -⟩ | ⟨-, hLn, hKn⟩
      · have hX : barSub V₀ V hV (L ⊔ K) = ⊥ := by
          refine hbar _ (sup_le hLM hKM) ?_ (sup_le hLC hKC)
          rw [← hXeq]
          exact TwelveTwentyThree.le_normalizer_conjClosure D.M L
        exact hbot2 (le_bot_iff.1 (hX ▸ barSub_mono V₀ V hV le_sup_left))
          (le_bot_iff.1 (hX ▸ barSub_mono V₀ V hV le_sup_right))
      · exact hbot2
          (hbar L hLM ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hLn) hLC)
          (hbar K hKM ((Subgroup.normal_subgroupOf_iff_le_normalizer hKM).1 hKn) hKC)

theorem gap19_8_3At_holds (D : Data G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1114 : R1114 D) (h126 : R126 D)
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    (h68 : S17.R17_68At D V₀ V)
    (hF : ((L.subgroupOf D.M).Normal ∧ (K.subgroupOf D.M).Normal ∧ InFSq 2 (L ⊔ D.T) ∧
        InFSq 2 (K ⊔ D.T)) ∨ InFSq 2 (L ⊔ K ⊔ D.T)) :
    Gap19_8_3At D V₀ V p L K h :=
  gap19_8_3At_of_five D hx h61 h127 h1114 h126 h
    (fun hL2 => exists_five_elem_19 D h h68 hL2) hF

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

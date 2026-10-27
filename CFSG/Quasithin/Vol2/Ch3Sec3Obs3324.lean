module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem338
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.EmptyFaithful.SzN15Br2
public import CFSG.Quasithin.EmptyFaithful.SBc11List
public import CFSG.Quasithin.EmptyFaithful.LRed3FourB
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)

namespace Obs3324

variable {G : Type} [Group G]

theorem nonempty_quot_equiv {L : Subgroup G} {H : Type} [Group H] (α : ↥L →* H)
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L) :
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* H) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)⟩

noncomputable def quotCenterEquiv {X : Type} [Group X] (hc : Subgroup.center X = ⊥) :
    X ⧸ Subgroup.center X ≃* X :=
  (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot

theorem isPSU_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : IsPSU 3 3 1 Y) :
    IsPSU 3 3 1 X := by
  obtain ⟨hv, K, hK1, hK2, hK3, ⟨f⟩⟩ := h
  exact ⟨hv, K, hK1, hK2, hK3, ⟨e.trans f⟩⟩

theorem exists_ne_zero_one {K : Type} [Field K] [Finite K] (hK : 2 < Nat.card K) :
    ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective (fun x : K => decide (x = 0)) := by
    intro a b hab
    by_cases ha : a = 0 <;> by_cases hb : b = 0
    · rw [ha, hb]
    · simp [ha, hb] at hab
    · simp [ha, hb] at hab
    · rw [hcon a ha, hcon b hb]
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  omega

theorem commutator_quasithinG2_eq {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 < n)
    (hK : Nat.card K = 2 ^ n) : ⁅quasithinG2 K, quasithinG2 K⁆ = quasithinG2 K := by
  have : CharP K 2 := FFC.charP_two_of_card_pow hK
  have h4 : 2 < Nat.card K := by
    rw [hK]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_one h4
  rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
    JonesParshall.cayley_commutator_eq hc0 hc1]

theorem lieModel_of_alt5 {X : Type} [Group X]
    (e : X ≃* alternatingGroup (Fin 5)) : LieModel X .PSL 2 2 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl (by rw [hK]; norm_num))
  exact Or.inl ⟨by decide, ⟨Nat.prime_two, by norm_num, by decide⟩, GaloisField 2 2,
    inferInstance, inferInstance, hK, ⟨e.trans e5.symm⟩⟩

theorem isPSU_of_g2Two
    {X : Type} [Group X] {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (e : X ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆) : IsPSU 3 3 1 X := by
  obtain ⟨eP⟩ := lred3_equiv_g2derived_psu33 hK
  have hK9 : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : ((3 : ℕ), 3 ^ 1) ≠ (3, 2) := fun h => absurd (congrArg Prod.snd h) (by norm_num)
  exact ⟨⟨Nat.prime_three, le_rfl, le_rfl, hne⟩, GaloisField 3 (2 * 1), inferInstance,
    inferInstance, hK9, ⟨e.trans eP.symm⟩⟩

variable [Finite G]

theorem quot_data {L W : Subgroup G} (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hker : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G))
    (hnt : ¬ L ≤ Subgroup.centralizer (W : Set G))
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) :
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      ↥(autOn L W) ⧸ Subgroup.center ↥(autOn L W)) ∧
    Nat.card ↥(autOn L W) ≤ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have hs := S153D.autOnQuot_surjective hLW hker
  exact ⟨⟨CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hq hs
      (CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq
        (S153D.exists_autOnQuot_ne_one hLW hker hnt))⟩,
    Nat.card_le_card_of_surjective _ hs⟩

theorem false_of_sp4_or_sl3 {L W : Subgroup G} (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hker : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G))
    (hnt : ¬ L ≤ Subgroup.centralizer (W : Set G))
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hcard : Nat.card ↥(autOn L W) = 360 ∨ Nat.card ↥(autOn L W) = 6048 ∨
      Nat.card ↥(autOn L W) = 1080)
    (hb : IsSp4Block L ∨ ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F)
      (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)), Fintype.card F = 2 ^ n ∧
      IsModO2Surj L α) : False := by
  have hle := (quot_data hLW hker hnt hq).2
  rcases hb with ⟨-, F, _, _, hF, α, hαs, hαk, -⟩ | ⟨n, F, _, _, α, hF, hmod⟩
  · have hx := SzN15.xOrd_autOn hLW hker hnt hq
      (Or.inr ⟨F, inferInstance, inferInstance, hF, nonempty_quot_equiv α hαs hαk⟩)
    have := hx.1
    rcases hcard with h | h | h <;> omega
  · obtain ⟨e⟩ := nonempty_quot_equiv α hmod.1 hmod.2
    have h1 : 1 < Fintype.card F := Fintype.one_lt_card
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · simp at hF
        omega
      · have hFc : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hF, pow_one]
        have h168 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168 := by
          rw [Nat.card_congr e.toEquiv, CFSG.SectionRank.OddCover.card_statedSL_three, hFc]
          norm_num
        rcases hcard with h | h | h <;> omega
    · have hx := SzN15.xOrd_autOn hLW hker hnt hq
        (Or.inl ⟨n, F, inferInstance, inferInstance, hn, hF, ⟨e⟩⟩)
      have := hx.1
      rcases hcard with h | h | h <;> omega

theorem of_c132
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (hC32 : CFSG.Quasithin.ASInputs.AS_C_1_32)
    {T M L D : Subgroup G} (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hr : IsRankTwoLie2Derived ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)))
    (hcard : Nat.card ↥(autOn L (vPlus L T)) = 360 ∨ Nat.card ↥(autOn L (vPlus L T)) = 6048 ∨
      Nat.card ↥(autOn L (vPlus L T)) = 1080) :
    IsAltBlockType L 6 ∨ CFSG.Quasithin.IsHatA6Block L ∨ IsG2Block L := by
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_left.trans hred.2.2.2.1
  have hOQ : pCoreOf 2 L ≤ qL L T :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T) le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTL))
  have hQV : qL L T ≤ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.le_centralizer_iff.mp (hred.1.trans inf_le_right)
  have hnt := h.not_L_le_centralizer h38 h39
  have hMS := h.isMSPair h38 h39 hr hTL
  rcases hC32 G (L ⊔ T) T L hMS h.toSetup331.mem_cComp
      (Subgroup.coe_mul_of_right_le_normalizer_left L T hTL) with hb | hb | hb | hb | hb
  · exact Or.inr (Or.inr hb)
  · exact Or.inl hb
  · exact (false_of_sp4_or_sl3 hLV (hOQ.trans hQV) hnt h.Lq hcard (Or.inl hb)).elim
  · exact Or.inr (Or.inl hb)
  · exact (false_of_sp4_or_sl3 hLV (hOQ.trans hQV) hnt h.Lq hcard (Or.inr hb)).elim

end Obs3324

theorem obs3_3_24_of
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h51 : AsB51) (h10 : Stmt3_3_10)
    (h14 : Stmt3_3_14) (h16 : Stmt3_3_16) (h19 : Stmt3_3_19) (h21 : Stmt3_3_21)
    (h22 : Stmt3_3_22) (hC32 : CFSG.Quasithin.ASInputs.AS_C_1_32) : Obs3_3_24 := by
  intro G _ _ T M L D h
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  have hnL2 := (h10 G T M L D h).2.1
  rw [hML] at hnL2
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_left.trans hred.2.2.2.1
  have hOQ : pCoreOf 2 L ≤ qL L T :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T) le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTL))
  have hQV : qL L T ≤ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.le_centralizer_iff.mp (hred.1.trans inf_le_right)
  obtain ⟨⟨eZ⟩, -⟩ := Obs3324.quot_data hLV (hOQ.trans hQV) (h.not_L_le_centralizer h38 h39) h.Lq
  have hfin : IsRankTwoLie2Derived
      ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) →
      (Nat.card ↥(autOn L (vPlus L T)) = 360 ∨ Nat.card ↥(autOn L (vPlus L T)) = 6048 ∨
        Nat.card ↥(autOn L (vPlus L T)) = 1080) →
      IsAltBlockType L 6 ∨ CFSG.Quasithin.IsHatA6Block L ∨ IsG2Block L ∨
        IsPSL 3 2 1 ↥(autOn L (vPlus L T)) := fun hr hcard => by
    rcases Obs3324.of_c132 h38 h39 hC32 h hTL hr hcard with hb | hb | hb
    · exact Or.inl hb
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr (Or.inl hb))
  have hA6 : Nonempty (↥(autOn L (vPlus L T)) ≃* alternatingGroup (Fin 6)) →
      IsAltBlockType L 6 ∨ CFSG.Quasithin.IsHatA6Block L ∨ IsG2Block L ∨
        IsPSL 3 2 1 ↥(autOn L (vPlus L T)) := fun ⟨e⟩ => by
    have hc0 := SBc11.center_eq_bot_of_list (Or.inr (Or.inl ⟨e⟩))
    exact hfin (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨eZ.trans ((Obs3324.quotCenterEquiv hc0).trans e)⟩)))))
      (Or.inl (SBc11.card_of_isAlt_six ⟨e⟩))
  obtain ⟨_, hc⟩ := h.lemma_3_3_8_of_le h38 h39 h51 hTL
  rcases hc with h1 | h2 | h3 | h4 | h5 | h6 | h7
  ·
    obtain ⟨t, ht, htN, -⟩ := h1
    exact absurd (hTL ht) htN
  ·
    obtain ⟨n, -, hn, -⟩ := h2
    rw [hML] at hn
    exact absurd hn (hnL2 n)
  ·
    rcases h3 with ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩
    · rw [hML] at e
      exact absurd (Obs3324.lieModel_of_alt5 e) (hnL2 2)
    · rw [hML] at e
      exact ((h22 G T M L D h).false e).elim
  ·
    rcases h4 with ⟨n, K, _, _, hK, ⟨e⟩, -⟩ | ⟨n, K, _, _, hn, hK, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ |
      ⟨n, K, _, _, hK, ⟨e⟩, -⟩
    ·
      rw [hML] at e
      rcases Nat.lt_or_ge n 2 with hn | hn
      · interval_cases n
        · have h1 := Finite.one_lt_card (α := K)
          rw [hK] at h1
          norm_num at h1
        · exact Or.inr (Or.inr (Or.inr (Vol2Native.A312L.Seven.isPSL_three_two
            (e.trans (statedSLEquivZModTwo (by rw [hK, pow_one]))))))
      · exact ((h16 G T M L D h n K hn hK).1.false e).elim
    ·
      rw [hML] at e
      exact ((h16 G T M L D h n K hn hK).2.1.false e).elim
    ·
      rw [hML] at e
      exact hA6 ⟨e⟩
    ·
      rw [hML] at e
      rcases Nat.lt_or_ge n 2 with hn | hn
      · interval_cases n
        · have h1 := Finite.one_lt_card (α := K)
          rw [hK] at h1
          norm_num at h1
        · have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
          have hP : IsPSU 3 3 1 ↥(autOn L (vPlus L T)) :=
            Obs3324.isPSU_of_g2Two hK2 e
          have hc0 := SBc11.center_eq_bot_of_list (Or.inr (Or.inr hP))
          exact hfin (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            (Obs3324.isPSU_of_equiv (eZ.trans (Obs3324.quotCenterEquiv hc0)) hP))))))))
            (Or.inr (Or.inl (SBc11.card_of_isPSU_three_three hP)))
      · rw [Obs3324.commutator_quasithinG2_eq hn hK] at e
        exact ((h16 G T M L D h n K hn hK).2.2.false e).elim
  ·
    obtain ⟨⟨e⟩, -⟩ := h5
    rw [hML] at e
    exact ((h22 G T M L D h).false e).elim
  ·
    obtain ⟨-, hZ, ⟨e⟩, -⟩ := h6
    rw [hML] at hZ e
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center ↥(autOn L (vPlus L T)))
    rw [Nat.card_congr e.toEquiv, SBc11.card_of_isAlt_six ⟨MulEquiv.refl _⟩, hZ] at hcard
    exact hfin (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨eZ.trans e⟩)))))
      (Or.inr (Or.inr hcard))
  ·
    obtain ⟨n, hn, ⟨e⟩, -⟩ := h7
    rw [hML] at e
    rcases hn with rfl | rfl
    · exact ((h21 G T M L D h).false e).elim
    · exact ((h19 G T M L D h).false e).elim

end CFSG.Quasithin.H13

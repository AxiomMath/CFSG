module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Excl
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Rank
public import CFSG.Quasithin.Vol2.Ch12Sec2Setting
public import CFSG.Quasithin.H13.FiveMenu
public import CFSG.Quasithin.H13.FiveAltCover
public import CFSG.Quasithin.SteinbergBMCoreQuotientCenterOdd
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo

public section

namespace CFSG.Quasithin.H13.Lem8

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.L34

theorem center_eq_bot_of_nonabelian {X : Type*} [Group X] [IsSimpleGroup X]
    (hX : ∃ a b : X, a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hX
    have hb : b ∈ Subgroup.center X := by
      rw [h]
      exact Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.mp hb a)

theorem center_eq_bot_of_isQuasisimple {X : Type*} [Group X] [IsSimpleGroup X]
    (hX : CFSG.IsQuasisimple X) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hX.2.2
    have : Subsingleton (X ⧸ Subgroup.center X) := QuotientGroup.subsingleton_iff.mpr h
    exact hab (Subsingleton.elim _ _)

theorem card_center_eq_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    Nat.card (Subgroup.center X) = Nat.card (Subgroup.center Y) :=
  Nat.card_congr (Subgroup.centerCongr e).toEquiv

theorem center_eq_bot_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  apply Subgroup.eq_bot_of_card_eq
  rw [card_center_eq_of_mulEquiv e, h, Subgroup.card_bot]

theorem center_alternatingGroup_eq_bot {n : ℕ} (hn : 5 ≤ n) :
    Subgroup.center (alternatingGroup (Fin n)) = ⊥ := by
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; exact hn)
  exact center_eq_bot_of_nonabelian (alternatingGroup_nonabelian (by omega))

theorem card_alternatingGroup_fin {n : ℕ} (hn : 2 ≤ n) :
    Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [nat_card_alternatingGroup, Nat.card_fin]

structure RankTwoFacts (Q : Type) [Group Q] [Finite Q] : Prop where
  rank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Q)
  card : ListOrd (Nat.card Q)
  a8 : Nat.card Q = 20160 → Nonempty (Q ≃* alternatingGroup (Fin 8))
  center : Subgroup.center Q = ⊥ ∨ ∃ n : ℕ, (n = 6 ∨ n = 7) ∧ Group.IsPerfect Q ∧
    Nat.card (Subgroup.center Q) = 3 ∧
    Nonempty (Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin n))
  hat : Subgroup.center Q ≠ ⊥ → Nat.card Q = 1080 ∨ Nat.card Q = 7560

theorem rankTwoFacts_alt {Q : Type} [Group Q] [Finite Q] {n : ℕ} (hn : n = 6 ∨ n = 7 ∨ n = 8)
    (e : Q ≃* alternatingGroup (Fin n)) : RankTwoFacts Q := by
  have hcard : Nat.card Q = n.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup_fin (by omega)]
  have hZ : Subgroup.center Q = ⊥ :=
    center_eq_bot_of_mulEquiv e (center_alternatingGroup_eq_bot (by omega))
  refine ⟨?_, ?_, ?_, Or.inl hZ, fun h => absurd hZ h⟩
  · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    rcases hn with rfl | rfl | rfl
    · exact Rank8.two_le_pRank_alternating_six
    · exact Rank8.two_le_pRank_alternating_seven
    · exact Rank8.two_le_pRank_alternating_eight
  · rw [hcard]
    unfold ListOrd
    rcases hn with rfl | rfl | rfl <;> decide
  · intro h20
    rcases hn with rfl | rfl | rfl
    · rw [hcard] at h20
      exact absurd h20 (by decide)
    · rw [hcard] at h20
      exact absurd h20 (by decide)
    · exact ⟨e⟩

theorem rankTwoFacts_hat {Q : Type} [Group Q] [Finite Q] {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hperf : Group.IsPerfect Q) (hZ : Nat.card (Subgroup.center Q) = 3)
    (e : Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin n)) : RankTwoFacts Q := by
  have hcard : Nat.card Q = 3 * (n.factorial / 2) := by
    rw [(Subgroup.center Q).card_eq_card_quotient_mul_card_subgroup, hZ,
      Nat.card_congr e.toEquiv, card_alternatingGroup_fin (by omega), mul_comm]
  have hhat : Nat.card Q = 1080 ∨ Nat.card Q = 7560 := by
    rw [hcard]
    rcases hn with rfl | rfl <;> decide
  refine ⟨Rank8.two_le_pRank_of_isHatAlt hn hZ e, ?_, ?_, Or.inr ⟨n, hn, hperf, hZ, ⟨e⟩⟩,
    fun _ => hhat⟩
  · unfold ListOrd
    omega
  · intro h
    omega

theorem rankTwoFacts_sl_four {Q : Type} [Group Q] [Finite Q]
    (e : Q ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) : RankTwoFacts Q := by
  obtain ⟨eA⟩ := (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff Q).mp
    (lieModel_psl_of_mulEquiv_sl_zmod_two (by norm_num) e)
  exact rankTwoFacts_alt (Or.inr (Or.inr rfl)) eA

theorem card_sl_five_zmod_two :
    Nat.card (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) = 9999360 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), Nat.card_zmod]
  decide

theorem center_sl_five_zmod_two :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have key : ∀ s : ZMod 2, s ^ 5 = 1 → s = 1 := by decide
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, key r hr, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem rankTwoFacts_sl_five {Q : Type} [Group Q] [Finite Q]
    (e : Q ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) : RankTwoFacts Q := by
  have hcard : Nat.card Q = 9999360 := by
    rw [Nat.card_congr e.toEquiv, card_sl_five_zmod_two]
  have hZ : Subgroup.center Q = ⊥ := center_eq_bot_of_mulEquiv e center_sl_five_zmod_two
  refine ⟨?_, ?_, ?_, Or.inl hZ, fun h => absurd hZ h⟩
  · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    exact Rank8.two_le_pRank_sl_five
  · rw [hcard]
    unfold ListOrd
    decide
  · intro h
    omega

theorem rankTwoFacts_psu {Q : Type} [Group Q] [Finite Q] (hq : CFSG.IsQuasisimple Q)
    (h : LieModel Q .PSU 3 3 1) : RankTwoFacts Q := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
  have hF9 : Nat.card F = 9 := by rw [hF]; norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsimple : IsSimpleGroup (StatedProj (StatedSU 3 (3 ^ 1) F)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 3 1 hF 3 le_rfl
      (by decide)
  have : IsSimpleGroup Q := e.isSimpleGroup
  have hZ : Subgroup.center Q = ⊥ := center_eq_bot_of_isQuasisimple hq
  have hbot :=
    CFSG.LinearGroups.UnitaryThreeOverNine.statedScalars_subgroupOf_statedSU_eq_bot hF9
  let e2 : StatedProj (StatedSU 3 3 F) ≃* ↥(StatedSU 3 3 F) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  let e3 : Q ≃* ↥(StatedSU 3 3 F) := e.trans e2
  have hcard : Nat.card Q = 6048 := by
    rw [Nat.card_congr e3.toEquiv, CFSG.LinearGroups.UnitaryThreeOverNine.card_statedSU hF9]
  refine ⟨?_, ?_, ?_, Or.inl hZ, fun h => absurd hZ h⟩
  · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e3]
    exact Rank8.two_le_pRank_su_three_three hF9
  · rw [hcard]
    unfold ListOrd
    decide
  · intro h
    omega

theorem cases_of_hyp1223 (h1222 : Stmt12_2_2) {G : Type} [Group G] [Finite G]
    {T L V : Subgroup G} (hH : Hyp1223 G T L V) :
    (∃ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 5) ∧
        Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) ∨
      LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 ∨
      ∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸
        Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin n)) := by
  obtain ⟨-, -, hall⟩ := ((h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨-, -, -, hcomm, hmod⟩ := hall V hH.irrPlus
  have hq := hH.quasisimple
  rcases hmod with ⟨n, hn, ⟨e⟩, -⟩ | ⟨⟨e⟩, -, -⟩ | ⟨⟨e⟩, -, -⟩ |
      ⟨n, hn5, hn8, ⟨φ, hφ, -⟩, -⟩ | ⟨-, φ, hφ, -⟩ | ⟨hU, -⟩ | ⟨-, -, hA6, -⟩
  · exact Or.inl ⟨n, hn, ⟨e⟩⟩
  · exact Or.inl ⟨3, Or.inl rfl, ⟨e⟩⟩
  · exact Or.inl ⟨5, Or.inr (Or.inr rfl), ⟨e⟩⟩
  · have hle := pCore_le_ker_of_surjective_alternating hn5 φ hφ
    have : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; exact hn5)
    obtain ⟨-, e, -⟩ := SteinbergBM.five_quasisimple_centerless_image hq
      (alternatingGroup_nonabelian (by omega)) (QuotientGroup.lift (CFSG.pCore 2 ↥L) φ hle)
      (QuotientGroup.lift_surjective_of_surjective _ φ hφ hle)
    exact Or.inr (Or.inr ⟨n, hn5, hn8, ⟨e⟩⟩)
  · have hle := pCore_le_ker_of_surjective_alternating (by norm_num) φ hφ
    have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
    obtain ⟨-, e, -⟩ := SteinbergBM.five_quasisimple_centerless_image hq
      (alternatingGroup_nonabelian (by norm_num)) (QuotientGroup.lift (CFSG.pCore 2 ↥L) φ hle)
      (QuotientGroup.lift_surjective_of_surjective _ φ hφ hle)
    exact Or.inr (Or.inr ⟨7, by norm_num, by norm_num, ⟨e⟩⟩)
  · exact Or.inr (Or.inl hU)
  · exact Or.inr (Or.inr ⟨6, by norm_num, by norm_num, hA6⟩)

theorem rankTwoFacts_or_small (h1222 : Stmt12_2_2) {G : Type} [Group G] [Finite G]
    {T L V : Subgroup G} (hH : Hyp1223 G T L V) :
    (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 5)) ∨
      LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1) ∨ RankTwoFacts (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have hq := hH.quasisimple
  obtain ⟨-, -, hodd⟩ := SteinbergBM.five_core_quotient_center_odd hq
  rcases cases_of_hyp1223 h1222 hH with ⟨n, hn, ⟨e⟩⟩ | hU | ⟨n, hn5, hn8, ⟨e⟩⟩
  · rcases hn with rfl | rfl | rfl
    · exact Or.inl (Or.inr (lieModel_psl_of_mulEquiv_sl_zmod_two le_rfl e))
    · exact Or.inr (rankTwoFacts_sl_four e)
    · exact Or.inr (rankTwoFacts_sl_five e)
  · exact Or.inr (rankTwoFacts_psu hq hU)
  · have hn' : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    obtain ⟨h58, h67, -⟩ := five_alternating_small_central_cover_reduction hq hodd hn' e
    rcases hn' with rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inl (h58 (Or.inl rfl)).2)
    · obtain ⟨-, h1, h3⟩ := h67 (Or.inl rfl)
      by_cases hc : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 1
      · obtain ⟨e'⟩ := h1 hc
        exact Or.inr (rankTwoFacts_alt (Or.inl rfl) e')
      · obtain ⟨hp, hZ, ⟨e'⟩⟩ := h3 hc
        exact Or.inr (rankTwoFacts_hat (Or.inl rfl) hp hZ e')
    · obtain ⟨-, h1, h3⟩ := h67 (Or.inr rfl)
      by_cases hc : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 1
      · obtain ⟨e'⟩ := h1 hc
        exact Or.inr (rankTwoFacts_alt (Or.inr (Or.inl rfl)) e')
      · obtain ⟨hp, hZ, ⟨e'⟩⟩ := h3 hc
        exact Or.inr (rankTwoFacts_hat (Or.inr rfl) hp hZ e')
    · obtain ⟨-, ⟨e'⟩⟩ := h58 (Or.inr rfl)
      exact Or.inr (rankTwoFacts_alt (Or.inr (Or.inr rfl)) e')

abbrev m22Word : Equiv.Perm (Fin 22) :=
  CFSG.Sporadic.Mathieu.m22gA * CFSG.Sporadic.Mathieu.m22gB * CFSG.Sporadic.Mathieu.m22gA *
    CFSG.Sporadic.Mathieu.m22gB

theorem orderOf_m22Word : orderOf m22Word = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem eleven_dvd_card_M22 : 11 ∣ Nat.card (NativeSporadic.Carrier .M22) := by
  have hmem : m22Word ∈ NativeSporadic.M22 := by
    rw [CFSG.Sporadic.Mathieu.m22_eq]
    have ha : CFSG.Sporadic.Mathieu.m22gA ∈
        Subgroup.closure {CFSG.Sporadic.Mathieu.m22gA, CFSG.Sporadic.Mathieu.m22gB} :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have hb : CFSG.Sporadic.Mathieu.m22gB ∈
        Subgroup.closure {CFSG.Sporadic.Mathieu.m22gA, CFSG.Sporadic.Mathieu.m22gB} :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) ha) hb
  have h := orderOf_dvd_natCard (⟨m22Word, hmem⟩ : NativeSporadic.M22)
  rw [Subgroup.orderOf_mk, orderOf_m22Word] at h
  exact h

theorem not_isHat_M22 {X : Type} [Group X] (hX : ListOrd (Nat.card X)) :
    ¬ IsHat X (NativeSporadic.Carrier .M22) := by
  rintro ⟨-, -, ⟨e⟩⟩
  have h11 : 11 ∣ Nat.card (X ⧸ Subgroup.center X) := by
    rw [Nat.card_congr e.toEquiv]
    exact eleven_dvd_card_M22
  have h := h11.trans (Subgroup.card_quotient_dvd_card _)
  unfold ListOrd at hX
  rcases hX with h' | h' | h' | h' | h' | h' | h' <;> rw [h'] at h <;> norm_num at h

end CFSG.Quasithin.H13.Lem8

module

public import CFSG.Milestones.ASVolI.C135.Eta
public import CFSG.Milestones.ASVolI.C135.N1

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL)

variable {G : Type} [Group G]

section Bridge

theorem burnsideC135_exists_modO2 {L : Subgroup G} {F : Type} [Field F]
    (e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) F) :
    ∃ α : ↥L →* ↥(StatedSL 3 F), IsModO2Surj L α := by
  refine ⟨(specialLinearGroupEquivStatedSL 3 F).toMonoidHom.comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))), ?_, ?_⟩
  · exact (specialLinearGroupEquivStatedSL 3 F).surjective.comp
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
  · ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem burnsideC135_sl3_card_lt {q q' : ℕ} (hq : 2 ≤ q) (hlt : q < q') :
    q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) < q' ^ 3 * ((q' ^ 2 - 1) * (q' ^ 3 - 1)) := by
  have h1 : q ^ 3 < q' ^ 3 := Nat.pow_lt_pow_left hlt (by norm_num)
  have h2 : q ^ 2 < q' ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
  have h3 : 2 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have h4 : 2 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h5 : q ^ 2 - 1 < q' ^ 2 - 1 := by omega
  have h6 : q ^ 3 - 1 < q' ^ 3 - 1 := by omega
  have h7 : (q ^ 2 - 1) * (q ^ 3 - 1) < (q' ^ 2 - 1) * (q' ^ 3 - 1) :=
    mul_lt_mul'' h5 h6 (Nat.zero_le _) (Nat.zero_le _)
  exact mul_lt_mul'' h1 h7 (Nat.zero_le _) (Nat.zero_le _)

theorem burnsideC135_n_eq {L : Subgroup G} {F F' : Type} [Field F] [Fintype F] [Field F']
    [Fintype F'] {n n' : ℕ} (hF : Fintype.card F = 2 ^ n) (hF' : Fintype.card F' = 2 ^ n')
    (e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    {α' : ↥L →* ↥(StatedSL 3 F')} (hα' : IsModO2Surj L α') : n = n' := by
  have h1 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) :=
    Nat.card_congr e.toEquiv
  have h2 : Nat.card (↥L ⧸ α'.ker) = Nat.card ↥(StatedSL 3 F') :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α' hα'.1).toEquiv
  rw [hα'.2, h1, ← CFSG.Open.StatedAPI.card_statedSL, CFSG.Open.StatedAPI.card_statedSL_three,
    CFSG.Open.StatedAPI.card_statedSL_three] at h2
  have hq : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have hq' : Nat.card F' = 2 ^ n' := by rw [Nat.card_eq_fintype_card, hF']
  have h2F : 2 ≤ Nat.card F := Finite.one_lt_card
  have h2F' : 2 ≤ Nat.card F' := Finite.one_lt_card
  have hcard : Nat.card F = Nat.card F' := by
    rcases lt_trichotomy (Nat.card F) (Nat.card F') with h | h | h
    · exact absurd h2 (burnsideC135_sl3_card_lt h2F h).ne
    · exact h
    · exact absurd h2 (burnsideC135_sl3_card_lt h2F' h).ne'
  rw [hq, hq'] at hcard
  exact Nat.pow_right_injective le_rfl hcard

theorem burnsideC135_one_le_n {F : Type} [Field F] [Fintype F] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    have : 1 < Fintype.card F := Fintype.one_lt_card
    rw [hF] at this
    norm_num at this
  · exact h

end Bridge

section Case

variable [Finite G]

theorem burnsideC135_case_of_chief (h134 : burnsideC135_C134W) {X R L : Subgroup G}
    (hMS : IsMSPairWith X R L) {F : Type} [Field F] [Fintype F] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) (e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    {m : ℕ} (hm : m ≠ 6) (hchief : IsChiefSeriesFrom L (pCoreOf 2 L) (pCoreOf 2 L) m) :
    ∃ i, MS93.IsC134CaseCorr i X R L ∧ burnsideC135_caseCount i = m := by
  obtain ⟨hMSp, hL, hG⟩ := hMS
  have hLX : L ≤ X := MS93.le_of_coe_eq_mul_left hG
  have hXL : X ≤ Subgroup.normalizer (L : Set G) := by
    have h := MS93.le_normalizer_oddGen X
    rwa [← MS93.isMSPair_eq_oddGen hMSp hL hG] at h
  obtain ⟨α, hα⟩ := burnsideC135_exists_modO2 e
  obtain ⟨i, hi | hi⟩ := h134 G X R L hMSp hL hG ⟨n, F, inferInstance, inferInstance, α, hF, hα⟩
  · exact ⟨i, hi.2, F112W.isChiefSeriesFrom_unique (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
      (burnsideC135_chief_of_case hLX hXL (perfect_of_mem_cComp hL) hi.2) hchief⟩
  · exact absurd (F112W.isChiefSeriesFrom_unique (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
      (burnsideC135_chief_of_case4W hLX hXL (perfect_of_mem_cComp hL) hi.2) hchief).symm hm

theorem burnsideC135_caseCount_eq_two {i : ℕ} (h : burnsideC135_caseCount i = 2) : i = 2 := by
  unfold burnsideC135_caseCount at h
  split at h <;> first | rfl | omega

theorem burnsideC135_caseCount_eq_three {i : ℕ} (h : burnsideC135_caseCount i = 3) : i = 3 := by
  unfold burnsideC135_caseCount at h
  split at h <;> first | rfl | omega

end Case

theorem burnsideC135_C_1_36_ofW (h134 : burnsideC135_C134W) : C_1_36 := by
  intro G _ _ X R L S n hMS hS ⟨F, _, _, hF, ⟨e⟩⟩ hCL hchief
  obtain ⟨i, hi, hci⟩ := burnsideC135_case_of_chief h134 hMS hF e (by norm_num) hchief
  have hi2 : i = 2 := burnsideC135_caseCount_eq_two hci
  subst hi2
  obtain ⟨⟨n', F', _, _, α', hF', hα', hN⟩, -⟩ := hi
  have hnn : n = n' := burnsideC135_n_eq hF hF' e hα'
  rw [← hnn] at hF'
  obtain ⟨hMSp, hL, hG⟩ := hMS
  have hXL : X ≤ Subgroup.normalizer (L : Set G) := by
    have h := MS93.le_normalizer_oddGen X
    rwa [← MS93.isMSPair_eq_oddGen hMSp hL hG] at h
  have key : X ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) = pCoreOf 2 L ∧
      IsMaxElemAbelian S (pCoreOf 2 L) ∧
      ∃ A : Subgroup G, A ≤ L ∧ IsMaxElemAbelian S A ∧
        (∀ B : Subgroup G, IsMaxElemAbelian S B → B = pCoreOf 2 L ∨ B = A) ∧
        Nat.card ↥(A ⊓ pCoreOf 2 L) = 2 ^ (4 * n) := by
    by_cases hn : 2 ≤ n
    · exact CFSG.Quasithin.H13.Ch4.lemmaC136_holds G X R L S n F' α' hMSp hL hG hXL hn hF' hα'
        hS hCL hN
    · have hn1 : n = 1 := by
        have := burnsideC135_one_le_n hF
        omega
      subst hn1
      exact burnsideC135_lemmaC136_one (by rw [hF']; rfl) hMSp hL hXL hα' hS hCL hN
  obtain ⟨h1, hQmax, A, hAL, hA, hAll, hcard⟩ := key
  refine ⟨h1, A, hAL, ?_, hcard⟩
  ext B
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · exact hAll B
  · rintro (rfl | rfl)
    · exact hQmax
    · exact hA

theorem burnsideC135_C_1_36_of (h134 : MS93.AS_C_1_34_corr) : C_1_36 :=
  burnsideC135_C_1_36_ofW (burnsideC135_c134W_of_corr h134)

end CFSG.ASVolI

end

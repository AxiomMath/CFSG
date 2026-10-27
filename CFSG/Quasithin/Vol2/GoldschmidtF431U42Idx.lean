module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Syl

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin U42F431
open scoped Pointwise

theorem B0_le_P1 : B0 ≤ P1 := inf_le_left

theorem B0_le_P2 : B0 ≤ P2 := inf_le_right

theorem mem_B0_iff {g : Y} : g ∈ B0 ↔ (g : P45) 0 = 0 ∧ (g : P45) '' L0S = L0S := by
  rw [B0, Subgroup.mem_inf, mem_P1_iff, mem_P2_iff]

theorem lineSet_ne_of_sameSet_false {a b : List ℕ} (h : sameSet a b = false) :
    lineSet a ≠ lineSet b := by
  intro hab
  have := sameSet_of_lineSet_eq hab
  rw [h] at this
  exact Bool.false_ne_true this

theorem p_spec :
    p1W.length = 3 ∧ (∀ kw ∈ p1W, (lnTab.getD kw.1 []).contains 0 = true ∧
      applyW kw.2 0 = 0 ∧ sameSet (imgSet (evalW kw.2) L0) (lnTab.getD kw.1 []) = true) ∧
    (List.range 27).filter (fun k => (lnTab.getD k []).contains 0) = p1W.map Prod.fst ∧
    p2W.length = 5 ∧ (∀ pw ∈ p2W, L0.contains pw.1 = true ∧ applyW pw.2 0 = pw.1 ∧
      sameSet (imgSet (evalW pw.2) L0) L0 = true) ∧ p2W.map Prod.fst = L0 := by
  have h := chkP_spec
  simp only [chkP, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, and_assoc] at h
  exact h

theorem P1_elem {kw : ℕ × List ℕ} (hkw : kw ∈ p1W) :
    ∃ g ∈ P1, g • L0S = lnS kw.1 := by
  obtain ⟨-, hap, hss⟩ := p_spec.2.1 kw hkw
  refine ⟨⟨wordP kw.2, wordP_mem _⟩, ?_, ?_⟩
  · rw [mem_P1_iff]
    apply Fin.ext
    rw [show (((⟨wordP kw.2, wordP_mem _⟩ : Y)) : P45) = wordP kw.2 from rfl, applyW_eq]
    exact hap
  · rw [smul_set_eq]
    show (wordP kw.2) '' L0S = lnS kw.1
    rw [L0S, image_lineSet (repL_wordP _) L0_lt, lineSet_eq_of_sameSet hss]
    rfl

theorem three_le_orbit :
    3 ≤ (MulAction.orbit ↥P1 L0S).ncard := by
  obtain ⟨a, b, c, habc⟩ := List.length_eq_three.1 p_spec.1
  have hfilt := p_spec.2.2.1
  rw [habc] at hfilt
  have hnd : (List.map Prod.fst [a, b, c]).Nodup := by
    rw [← hfilt]
    exact (List.nodup_range).filter _
  have hlt : ∀ kw ∈ [a, b, c], kw.1 < 27 := by
    intro kw hkw
    have : kw.1 ∈ (List.range 27).filter (fun k => (lnTab.getD k []).contains 0) := by
      rw [hfilt]; exact List.mem_map_of_mem hkw
    exact List.mem_range.1 (List.mem_of_mem_filter this)
  have hne : ∀ kw₁ ∈ [a, b, c], ∀ kw₂ ∈ [a, b, c], kw₁.1 ≠ kw₂.1 → lnS kw₁.1 ≠ lnS kw₂.1 := by
    intro kw₁ h₁ kw₂ h₂ hk
    rcases lines_spec.2.2.2.2.2 kw₁.1 (hlt _ h₁) kw₂.1 (hlt _ h₂) with h | h
    · exact absurd h hk
    · exact lineSet_ne_of_sameSet_false h
  have hmem : ∀ kw ∈ [a, b, c], lnS kw.1 ∈ MulAction.orbit ↥P1 L0S := by
    intro kw hkw
    obtain ⟨g, hg, hgS⟩ := P1_elem (kw := kw) (by rw [habc]; exact hkw)
    exact ⟨⟨g, hg⟩, hgS⟩
  have hab : a.1 ≠ b.1 := fun h => by simp [h] at hnd
  have hac : a.1 ≠ c.1 := fun h => by simp [h] at hnd
  have hbc : b.1 ≠ c.1 := fun h => by simp [h] at hnd
  have hsub : ({lnS a.1, lnS b.1, lnS c.1} : Set (Set (Fin 45))) ⊆ MulAction.orbit ↥P1 L0S := by
    intro S hS
    rcases hS with rfl | rfl | rfl
    · exact hmem a (by simp)
    · exact hmem b (by simp)
    · exact hmem c (by simp)
  have h3 : ({lnS a.1, lnS b.1, lnS c.1} : Set (Set (Fin 45))).ncard = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨_, _, _, hne a (by simp) b (by simp) hab, hne a (by simp) c (by simp) hac,
      hne b (by simp) c (by simp) hbc, rfl⟩
  rw [← h3]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

theorem stabilizer_P1 : MulAction.stabilizer ↥P1 L0S = B0.subgroupOf P1 := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, B0, Subgroup.mem_inf]
  constructor
  · intro h
    exact ⟨g.2, (MulAction.mem_stabilizer_iff).2 h⟩
  · intro h
    exact (MulAction.mem_stabilizer_iff).1 h.2

theorem three_le_relIndex : 3 ≤ B0.relIndex P1 := by
  have h := MulAction.index_stabilizer ↥P1 L0S
  rw [stabilizer_P1] at h
  show 3 ≤ (B0.subgroupOf P1).index
  rw [h]
  exact three_le_orbit

theorem card_K_ge :
    192 ≤ Nat.card ↥(T ⊔ Subgroup.zpowers c3Y) := by
  have h1 : Nat.card T ∣ Nat.card ↥(T ⊔ Subgroup.zpowers c3Y) :=
    Subgroup.card_dvd_of_le le_sup_left
  have h2 : orderOf c3Y ∣ Nat.card ↥(T ⊔ Subgroup.zpowers c3Y) :=
    Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers c3Y))
  rw [card_T] at h1
  rw [orderOf_c3] at h2
  have h3 : 64 * 3 ∣ Nat.card ↥(T ⊔ Subgroup.zpowers c3Y) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2
  exact Nat.le_of_dvd Nat.card_pos (by simpa using h3)

theorem K_le_B0 : T ⊔ Subgroup.zpowers c3Y ≤ B0 :=
  sup_le T_le_B0 ((Subgroup.zpowers_le).2 c3_mem_B0)

theorem card_B0 :
    Nat.card B0 = 192 := by
  have h1 := Subgroup.relIndex_mul_card (H := B0) (K := P1)
  rw [inf_eq_left.2 B0_le_P1, card_P1] at h1
  have h3 := three_le_relIndex
  have h4 : 192 ≤ Nat.card B0 := (card_K_ge).trans (Subgroup.card_le_of_le K_le_B0)
  nlinarith

theorem relIndex_B0_P1 :
    B0.relIndex P1 = 3 := by
  have h1 := Subgroup.relIndex_mul_card (H := B0) (K := P1)
  rw [inf_eq_left.2 B0_le_P1, card_P1, card_B0] at h1
  omega

theorem B0_le_normalizer_T :
    B0 ≤ Subgroup.normalizer (T : Set Y) := by
  have hK : T ⊔ Subgroup.zpowers c3Y ≤ Subgroup.normalizer (T : Set Y) ⊓ B0 :=
    le_inf (sup_le Subgroup.le_normalizer
      ((Subgroup.zpowers_le).2 c3_mem_normalizer)) K_le_B0
  have h1 : Nat.card B0 ≤ Nat.card ↥(Subgroup.normalizer (T : Set Y) ⊓ B0) := by
    rw [card_B0]
    exact (card_K_ge).trans (Subgroup.card_le_of_le hK)
  have h2 : Subgroup.normalizer (T : Set Y) ⊓ B0 = B0 :=
    Subgroup.eq_of_le_of_card_ge inf_le_right h1
  rw [← h2]
  exact inf_le_left

end CFSG.Quasithin.H13.F431.U42

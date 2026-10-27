module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma5Ord
public import CFSG.Quasithin.Vol2.Ch12Sec9List
public import CFSG.Quasithin.H13.L1332Inputs
public import CFSG.Quasithin.H13.LinearOrders
public import CFSG.Quasithin.Vol2.Ch11SecA02Simple

public section

namespace CFSG.Quasithin.H13

namespace L1294Q

open CFSG.Open CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def Normal3 (N : Subgroup G) : Prop :=
  ∀ M : Subgroup G, M ≤ N → (∀ n ∈ N, ∀ m ∈ M, n * m * n⁻¹ ∈ M) → 3 < Nat.card M → M = N

variable {Q : Type} [Group Q]

theorem comap_normal (ψ : Q →* G) {M : Subgroup G}
    (hM : ∀ n ∈ ψ.range, ∀ m ∈ M, n * m * n⁻¹ ∈ M) : (M.comap ψ).Normal :=
  ⟨fun x hx q => by
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hM _ ⟨q, rfl⟩ _ hx⟩

theorem normal3_of_simple [IsSimpleGroup Q] (ψ : Q →* G) : Normal3 ψ.range := by
  intro M hMN hM h3
  have := comap_normal ψ hM
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.comap ψ) with h | h
  · exfalso
    have hM' : M = ⊥ := by rw [← Subgroup.map_comap_eq_self hMN, h, Subgroup.map_bot]
    rw [hM', Subgroup.card_bot] at h3
    omega
  · rw [← Subgroup.map_comap_eq_self hMN, h, ← MonoidHom.range_eq_map]

theorem le_center_or_eq_top (hQ : CFSG.IsQuasisimple Q) (M : Subgroup Q) [M.Normal] :
    M ≤ Subgroup.center Q ∨ M = ⊤ := by
  obtain ⟨hperf, hsimple, -⟩ := hQ
  set π := QuotientGroup.mk' (Subgroup.center Q) with hπ
  have hn : (M.map π).Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.map π) with h | h
  · left
    intro x hx
    have : π x ∈ M.map π := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff x).1 this
  · right
    have hdec : ∀ x : Q, ∃ m ∈ M, m⁻¹ * x ∈ Subgroup.center Q := by
      intro x
      have : π x ∈ M.map π := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨m, hm, hmx⟩ := this
      exact ⟨m, hm, (QuotientGroup.eq).1 hmx⟩
    have key1 : ∀ a b c : Q, c ∈ Subgroup.center Q → ⁅a * c, b⁆ = ⁅a, b⁆ := by
      intro a b c hc
      have hcb : c * b = b * c := (Subgroup.mem_center_iff.1 hc b).symm
      rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
      calc a * c * b * (c⁻¹ * a⁻¹) * b⁻¹ = a * (c * b) * c⁻¹ * a⁻¹ * b⁻¹ := by group
        _ = a * (b * c) * c⁻¹ * a⁻¹ * b⁻¹ := by rw [hcb]
        _ = a * b * a⁻¹ * b⁻¹ := by group
    have key2 : ∀ a b c : Q, c ∈ Subgroup.center Q → ⁅a, b * c⁆ = ⁅a, b⁆ := by
      intro a b c hc
      have hca : c * a⁻¹ = a⁻¹ * c := (Subgroup.mem_center_iff.1 hc a⁻¹).symm
      rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
      calc a * (b * c) * a⁻¹ * (c⁻¹ * b⁻¹) = a * b * (c * a⁻¹) * c⁻¹ * b⁻¹ := by group
        _ = a * b * (a⁻¹ * c) * c⁻¹ * b⁻¹ := by rw [hca]
        _ = a * b * a⁻¹ * b⁻¹ := by group
    rw [eq_top_iff]
    calc (⊤ : Subgroup Q) = commutator Q := hperf.commutator_eq_top.symm
      _ ≤ M := by
        rw [commutator_def, Subgroup.commutator_le]
        intro x _ y _
        obtain ⟨m, hm, hmx⟩ := hdec x
        obtain ⟨m', hm', hmy⟩ := hdec y
        have hx : x = m * (m⁻¹ * x) := by group
        have hy : y = m' * (m'⁻¹ * y) := by group
        rw [hx, hy, key1 _ _ _ hmx, key2 _ _ _ hmy, commutatorElement_def]
        exact M.mul_mem (M.mul_mem (M.mul_mem hm hm') (M.inv_mem hm)) (M.inv_mem hm')

theorem normal3_of_quasisimple [Finite Q] (hQ : CFSG.IsQuasisimple Q)
    (hZ : Nat.card (Subgroup.center Q) ≤ 3) (ψ : Q →* G) : Normal3 ψ.range := by
  intro M hMN hM h3
  have := comap_normal ψ hM
  rcases le_center_or_eq_top hQ (M.comap ψ) with h | h
  · exfalso
    have hle : Nat.card M ≤ Nat.card (Subgroup.center Q) := by
      rw [← Subgroup.map_comap_eq_self hMN]
      calc Nat.card ((M.comap ψ).map ψ) ≤ Nat.card (M.comap ψ) :=
            Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
        _ ≤ Nat.card (Subgroup.center Q) := Subgroup.card_le_of_le h
    omega
  · rw [← Subgroup.map_comap_eq_self hMN, h, ← MonoidHom.range_eq_map]

theorem card_range_dvd [Finite Q] (ψ : Q →* G) : Nat.card ψ.range ∣ Nat.card Q := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
  exact Subgroup.card_quotient_dvd_card _

theorem card_range_of_simple [IsSimpleGroup Q] {ψ : Q →* G} (hne : ψ.range ≠ ⊥) :
    Nat.card ψ.range = Nat.card Q := by
  have hker : ψ.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
    · exact h
    · exfalso
      apply hne
      rw [eq_bot_iff]
      rintro _ ⟨q, rfl⟩
      exact (Subgroup.mem_bot).2 (ψ.mem_ker.1 (h ▸ Subgroup.mem_top q))
  exact (Nat.card_congr (MonoidHom.ofInjective ((MonoidHom.ker_eq_bot_iff ψ).1 hker)).toEquiv).symm

theorem list2
    (hQ : IsList1293Two Q) {ψ : Q →* G} (hne : ψ.range ≠ ⊥) :
    2661120 < Nat.card ψ.range ∧ 7 ∣ Nat.card ψ.range ∧ Normal3 ψ.range := by
  rcases hQ with h | h | h <;> obtain ⟨e⟩ := h
  · have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :=
      CFSG.Quasithin.Vol2.Ch11.SecA.isSimpleGroup_SL_zmod_two (by norm_num)
    have : IsSimpleGroup Q := e.isSimpleGroup
    rw [card_range_of_simple hne, Nat.card_congr e.toEquiv, card_sl_five_zmod_two]
    exact ⟨by norm_num, by norm_num, normal3_of_simple ψ⟩
  · have : IsSimpleGroup Q :=
      @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2 e
    rw [card_range_of_simple hne, Nat.card_congr e.toEquiv, CFSG.Sporadic.Mathieu.card_M24]
    exact ⟨by norm_num, by norm_num, normal3_of_simple ψ⟩
  · have : IsSimpleGroup Q :=
      @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J4.isSimpleGroup_J4 e
    rw [card_range_of_simple hne, Nat.card_congr e.toEquiv, CFSG.Sporadic.J4.card_J4]
    exact ⟨by norm_num, by norm_num, normal3_of_simple ψ⟩

theorem card_of_isSL27OverE49 (h : IsSL27OverE49 Q) : Nat.card Q = 16464 := by
  obtain ⟨E, -, hE, -, hEn, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)) = 336 := by
    rw [Matrix.card_SL_field, ZMod.card, Fin.prod_univ_two]
    norm_num
  have h1 := E.card_mul_index
  rw [hE, Subgroup.index, Nat.card_congr e.toEquiv, hSL] at h1
  rw [← h1]

theorem card_of_isHatA7 (h : IsHatA7 Q) : Nat.card Q = 7560 := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := h
  have h1 := (Subgroup.center Q).card_mul_index
  rw [hZ, Subgroup.index, Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at h1
  rw [← h1]
  decide

theorem list3
    (hQ : IsList1293Three Q) {ψ : Q →* G} (hne : ψ.range ≠ ⊥) :
    (Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧ Nat.card ψ.range = 20160 ∧
        Normal3 ψ.range) ∨
      ((Nat.card ψ.range = 2520 ∨ Nat.card ψ.range = 7560 ∨ 2661120 < Nat.card ψ.range) ∧
        Normal3 ψ.range) ∨
      Nat.card ψ.range ∣ 16464 := by
  rcases hQ with h | h | h | h | h | h | h | h
  · obtain ⟨e⟩ := h
    have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :=
      isSimpleGroup_sl_four_zmod_two
    have : IsSimpleGroup Q := e.isSimpleGroup
    refine Or.inl ⟨⟨e⟩, ?_, normal3_of_simple ψ⟩
    rw [card_range_of_simple hne, Nat.card_congr e.toEquiv, card_sl_four_zmod_two]
  · obtain ⟨e⟩ := h
    have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
    have : IsSimpleGroup Q := e.isSimpleGroup
    refine Or.inr (Or.inl ⟨Or.inl ?_, normal3_of_simple ψ⟩)
    rw [card_range_of_simple hne, Nat.card_congr e.toEquiv, nat_card_alternatingGroup,
      Nat.card_fin]
    decide
  ·
    have hQc := card_of_isHatA7 h
    have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQc]; norm_num)
    refine Or.inr (Or.inl ⟨?_, normal3_of_quasisimple h.1 (by rw [h.2.1]) ψ⟩)
    have hdvd := card_range_dvd ψ
    rw [hQc] at hdvd
    have hker : ψ.ker ≤ Subgroup.center Q := by
      rcases le_center_or_eq_top h.1 ψ.ker with hk | hk
      · exact hk
      · exfalso
        apply hne
        rw [eq_bot_iff]
        rintro _ ⟨q, rfl⟩
        exact (Subgroup.mem_bot).2 (ψ.mem_ker.1 (hk ▸ Subgroup.mem_top q))
    have hk := Subgroup.card_dvd_of_le hker
    rw [h.2.1] at hk
    have hk' : Nat.card ψ.ker * Nat.card ψ.range = 7560 := by
      rw [← hQc, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
      exact (Subgroup.card_mul_index ψ.ker)
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 hk with h1 | h3
    · rw [h1, one_mul] at hk'
      exact Or.inr (Or.inl hk')
    · rw [h3] at hk'
      exact Or.inl (by omega)
  · obtain ⟨e⟩ := h
    have : IsSimpleGroup Q :=
      @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2 e
    refine Or.inr (Or.inl ⟨Or.inr (Or.inr ?_), normal3_of_simple ψ⟩)
    rw [card_range_of_simple hne, Nat.card_congr e.toEquiv, L1295B.card_M23]
    norm_num
  · obtain ⟨e⟩ := h
    have : IsSimpleGroup Q :=
      @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.HS.isSimpleGroup_HS e
    refine Or.inr (Or.inl ⟨Or.inr (Or.inr ?_), normal3_of_simple ψ⟩)
    rw [card_range_of_simple hne, Nat.card_congr e.toEquiv, CFSG.Sporadic.HS.card_HS]
    norm_num
  · obtain ⟨e⟩ := h
    have : IsSimpleGroup Q :=
      @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.He.isSimpleGroup_He e
    refine Or.inr (Or.inl ⟨Or.inr (Or.inr ?_), normal3_of_simple ψ⟩)
    rw [card_range_of_simple hne, Nat.card_congr e.toEquiv, CFSG.Sporadic.He.card_He]
    norm_num
  · obtain ⟨e⟩ := h
    have : IsSimpleGroup Q :=
      @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Ru.isSimpleGroup_Ru e
    refine Or.inr (Or.inl ⟨Or.inr (Or.inr ?_), normal3_of_simple ψ⟩)
    rw [card_range_of_simple hne, Nat.card_congr e.toEquiv, CFSG.Sporadic.Ru.card_Ru]
    norm_num
  · have hQc := card_of_isSL27OverE49 h
    have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQc]; norm_num)
    refine Or.inr (Or.inr ?_)
    rw [← hQc]
    exact card_range_dvd ψ

end L1294Q

end CFSG.Quasithin.H13

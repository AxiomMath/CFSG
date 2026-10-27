module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBasic

public section

namespace CFSG.Quasithin

private theorem isPGroup_three_of_isElemAbelian {G : Type*} [Group G] {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 3 E) : IsPGroup 3 E := by
  have : IsElementaryAbelian 3 E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).2 hE
  exact IsElementaryAbelian.isPGroup 3 E

private theorem card_le_nine_of_not_dvd {G : Type*} [Group G] [Finite G]
    (hG : ¬ 3 ^ 3 ∣ Nat.card G) {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 3 E) :
    Nat.card E ≤ 3 ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (isPGroup_three_of_isElemAbelian hE)
  have hdvd : 3 ^ k ∣ Nat.card G := hk ▸ Subgroup.card_subgroup_dvd_card E
  have hk2 : k ≤ 2 := by
    by_contra h3
    exact hG ((pow_dvd_pow 3 (by omega : 3 ≤ k)).trans hdvd)
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) hk2

private theorem not_isCyclic_of_isElemAbelian_card {G : Type*} [Group G] {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 2) : ¬ IsCyclic E := by
  intro hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have h3 : g ^ 3 = 1 :=
    Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hE.2 _ g.2)
  have hdvd := orderOf_dvd_of_pow_eq_one h3
  rw [hg, hcard] at hdvd
  exact absurd hdvd (by decide)

private theorem exists_compl_of_isElemAbelian {G : Type*} [Group G] {E Z : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hZE : Z ≤ E) :
    ∃ K : Subgroup G, K ≤ E ∧ Z ⊓ K = ⊥ ∧ Z ⊔ K = E := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsElementaryAbelian 3 E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).2 hE
  obtain ⟨C, hC⟩ := IsElementaryAbelian.exists_isCompl 3 E (Z.subgroupOf E)
  have hZ : (Z.subgroupOf E).map E.subtype = Z := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hZE]
  refine ⟨C.map E.subtype, Subgroup.map_subtype_le C, ?_, ?_⟩
  · rw [← hZ, ← Subgroup.map_inf_eq _ _ _ E.subtype_injective, hC.inf_eq_bot, Subgroup.map_bot]
  · rw [← hZ, ← Subgroup.map_sup, hC.sup_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

private theorem exists_isElemAbelian_card_nine_of_not_isCyclic {X : Type*} [Group X] [Finite X]
    {R : Subgroup X} (hRcard : Nat.card R = 3 ^ 3) (hRnc : ¬ IsCyclic R) :
    ∃ A : Subgroup X, CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 R) := ⟨IsPGroup.of_card hRcard⟩
  obtain ⟨S, -, hScard, hS⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hRnc
  refine ⟨S.map R.subtype, ?_, ?_⟩
  · exact CFSG.SectionRank.isElemAbelian_map
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 S).1 hS) R.subtype
  · rw [Subgroup.card_map_of_injective R.subtype_injective, hScard]

theorem pRank_three_alt_six_seven {m : ℕ} (hm : m = 6 ∨ m = 7) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin m))) = 2 := by
  have hm6 : 6 ≤ m := by omega
  have hm8 : m ≤ 8 := by omega
  have h27 : ¬ 3 ^ 3 ∣ Nat.card (alternatingGroup (Fin m)) := fun h =>
    absurd (h.trans (CFSG.SectionRank.card_alternatingGroup_dvd (by omega) hm8)) (by decide)
  refine le_antisymm (CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE =>
    card_le_nine_of_not_dvd h27 hE) ?_
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top
    (CFSG.SectionRank.isElemAbelian_sylowThreeAlt hm6) (CFSG.SectionRank.card_sylowThreeAlt hm6)

theorem pRank_three_hatA6 {X : Type} [Group X] [Finite X]
    (h : IsHat X (alternatingGroup (Fin 6))) : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 := by
  obtain ⟨hq, hZ, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZp : IsPGroup 3 (Subgroup.center X) := IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])
  have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]; decide
  have hXcard : Nat.card X = 1080 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
    rw [Nat.card_congr e.toEquiv, hA6, hZ] at h1
    omega
  apply le_antisymm
  ·
    refine CFSG.SectionRank.pRank_le (by norm_num) fun F _ hF => ?_
    by_contra hlt
    have hF3 : IsPGroup 3 F := isPGroup_three_of_isElemAbelian hF
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hF3
    rw [hk] at hlt
    have hdvd : 3 ^ k ∣ 1080 := by
      have := Subgroup.card_subgroup_dvd_card F
      rwa [hk, hXcard] at this
    have hk3 : 3 ≤ k := by
      by_contra h3
      exact hlt (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hk3' : k ≤ 3 := by
      by_contra h4
      exact absurd ((pow_dvd_pow 3 (by omega : 4 ≤ k)).trans hdvd) (by decide)
    obtain rfl : k = 3 := le_antisymm hk3' hk3
    have hF27 : Nat.card F = 27 := hk.trans (by norm_num)
    have hFidx : ¬ 3 ∣ F.index := by
      have := Subgroup.index_mul_card (H := F)
      rw [hF27, hXcard] at this
      omega
    have hZF : Subgroup.center X ≤ F := hZp.le_sylow_of_normal (hF3.toSylow hFidx)
    obtain ⟨K, hKF, hK1, hK2⟩ := exists_compl_of_isElemAbelian hF hZF
    obtain ⟨K', hK'1, hK'2⟩ := (gaschutz hZp (hF3.toSylow hFidx)).2 ⟨K, hKF, hK1, hK2⟩
    have hK'top : K' = ⊤ :=
      CFSG.QuasithinUnique.Bridge.Over.eq_top_of_sup_center_eq_top hq.1
        ((sup_comm K' (Subgroup.center X)).trans hK'2)
    rw [hK'top, inf_top_eq] at hK'1
    rw [hK'1, Subgroup.card_bot] at hZ
    exact absurd hZ (by norm_num)
  ·
    have hQ : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ Subgroup.center X)) := by
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
      exact (pRank_three_alt_six_seven (m := 6) (Or.inl rfl)).ge
    obtain ⟨E, -, hE, hEcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank hQ
    have hRcard : Nat.card (E.comap (QuotientGroup.mk' (Subgroup.center X))) = 3 ^ 3 :=
      calc Nat.card (E.comap (QuotientGroup.mk' (Subgroup.center X)))
          = Nat.card (Subgroup.center X) * Nat.card E :=
            QuotientGroup.card_preimage_mk (Subgroup.center X) (E : Set (X ⧸ Subgroup.center X))
        _ = 3 * 3 ^ 2 := by rw [hZ, hEcard]
        _ = 3 ^ 3 := by norm_num
    have hRnc : ¬ IsCyclic (E.comap (QuotientGroup.mk' (Subgroup.center X))) := fun hcyc =>
      not_isCyclic_of_isElemAbelian_card hE hEcard
        (isCyclic_of_surjective ((QuotientGroup.mk' (Subgroup.center X)).subgroupComap E)
          (MonoidHom.subgroupComap_surjective _ _ (QuotientGroup.mk'_surjective _)))
    obtain ⟨A, hA, hAcard⟩ := exists_isElemAbelian_card_nine_of_not_isCyclic hRcard hRnc
    exact CFSG.SectionRank.le_pRank (by norm_num) le_top hA hAcard

end CFSG.Quasithin

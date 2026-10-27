module

public import CFSG.Sporadic.FischerOddCore.Fi24R2Comp
public import CFSG.Sporadic.FischerOddCore.Fi24TJComp

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local instance] CFSG.Sporadic.Fi24.rAction

open CFSG CFSG.LocalCores

abbrev fi23ToJ :
    CFSG.Sporadic.Fi23.J →* CFSG.Sporadic.Fi24.J :=
  CFSG.Sporadic.Fi24.M.subtype.comp (@MulEquiv.toMonoidHom CFSG.Sporadic.Fi23.J
    CFSG.Sporadic.Fi24.M inferInstance inferInstance CFSG.Sporadic.Fi24.fi23EquivM.symm)

theorem card_fix_tJ :
    Nat.card {k : Fin 306936 // CFSG.Sporadic.Fi24.tJ • k = k} = 3512 := by
  have hsb : CFSG.Sporadic.Fi24.fi23EquivM.symm CFSG.Sporadic.Fi24.sb =
      ⟨CFSG.Sporadic.Fi24.tJ, CFSG.Sporadic.Fi24.tJ_mem_M⟩ := by
    rw [MulEquiv.symm_apply_eq, CFSG.Sporadic.Fi24.fi23EquivM_tJ]
  have hf : fi23ToJ CFSG.Sporadic.Fi24.sb = CFSG.Sporadic.Fi24.tJ := by
    show ((CFSG.Sporadic.Fi24.fi23EquivM.symm CFSG.Sporadic.Fi24.sb : CFSG.Sporadic.Fi24.M) :
      CFSG.Sporadic.Fi24.J) = CFSG.Sporadic.Fi24.tJ
    rw [hsb]
  obtain ⟨c, hc⟩ := (isConj_iff (α := CFSG.Sporadic.Fi24.J)).1
    (MonoidHom.map_isConj fi23ToJ CFSG.Sporadic.Fi24.sb_mem_D23)
  rw [hf] at hc
  rw [← hc, card_fix_conj]
  have h1 : Nat.card {k : Fin 306936 // fi23ToJ CFSG.Sporadic.Fi23.d • k = k} =
      Nat.card {k : Fin 306936 // fi24D • k = k} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun k => by
      rw [← CFSG.Sporadic.Fi24.jR_smul]
      rfl)
  rw [h1, ← card_fixed_D24_pts]
  exact fi24Wit_facts.1 0 (by norm_num)

theorem isConj_t2_fi24R2 :
    IsConj (CFSG.Sporadic.Fi24.fi23EquivM.symm CFSG.Sporadic.Fi23.t2 : CFSG.Sporadic.Fi24.J)
      fi24R2 :=
  MonoidHom.map_isConj fi23ToJ isConj_fi23U2_fi23U3.2

theorem CTI_Fi24prime_504_fixed_point_centralizer_has_no_components
    {s : CFSG.Sporadic.Fi24.J}
    (hs : orderOf s = 2) (h504 : Nat.card {k : Fin 306936 // s • k = k} = 504) :
    (Nat.card ↥(Subgroup.centralizer ({s} : Set CFSG.Sporadic.Fi24.J)) = 160526499840 ∧
      ∃ Q : Subgroup ↥(Subgroup.centralizer ({s} : Set CFSG.Sporadic.Fi24.J)), Q.Normal ∧
        Nat.card Q = 8192 ∧ Subgroup.centralizer (Q : Set _) ≤ Q) ∧
    ∀ B : Subgroup ↥(Subgroup.centralizer ({s} : Set CFSG.Sporadic.Fi24.J)), ¬ IsComponent B := by
  have hs2 : s * s = 1 := by rw [← sq, ← hs, pow_orderOf_eq_one]
  have hs1 : s ≠ 1 := fun h => by rw [h, orderOf_one] at hs; omega
  have hconj : IsConj fi24R2 s := by
    rcases CFSG.Sporadic.Fi24.isConj_tJ_or_r2 CFSG.Fischer.polarFacts
        CFSG.Sporadic.Fi23.d1_mem_localClass CFSG.Sporadic.Fi23.involution_cover hs2 hs1 with
      h | h
    · exfalso
      obtain ⟨c, hc⟩ := isConj_iff.1 h.symm
      have := card_fix_conj c CFSG.Sporadic.Fi24.tJ
      rw [hc, h504, card_fix_tJ] at this
      omega
    · exact (h.trans isConj_t2_fi24R2).symm
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have e : ↥(Subgroup.centralizer ({fi24R2} : Set CFSG.Sporadic.Fi24.J)) ≃*
      ↥(Subgroup.centralizer ({s} : Set CFSG.Sporadic.Fi24.J)) :=
    (centralizerMulEquiv (MulAut.conj c) fi24R2).trans
      (MulEquiv.subgroupCongr (by rw [MulAut.conj_apply, hc]))
  obtain ⟨hcard, Q, hQn, hQcard, hQc⟩ := fi24R2_centralizer_structure
  obtain ⟨Q', hQ'n, hQ'card, hQ'c⟩ := @exists_selfCentralizing_card_of_mulEquiv
    ↥(Subgroup.centralizer ({s} : Set CFSG.Sporadic.Fi24.J))
    ↥(Subgroup.centralizer ({fi24R2} : Set CFSG.Sporadic.Fi24.J)) inferInstance inferInstance
    e.symm Q hQn hQc
  rw [hQcard] at hQ'card
  refine ⟨⟨by rw [← Nat.card_congr e.toEquiv]; exact hcard, Q', hQ'n, hQ'card, hQ'c⟩,
    fun B => not_isComponent_of_selfCentralizing hQ'n
      (IsPGroup.of_card (n := 13) (by rw [hQ'card]; norm_num)) hQ'c B⟩

theorem CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven
    {S : Type*} [Group S] (e : S ≃* Blueprint.NativeSporadic.Fi24prime) (s : S)
    (hs : orderOf s = 2) (B : Subgroup (Subgroup.centralizer ({s} : Set S)))
    (hB : IsComponent B) :
    Nat.card (B ⧸ Subgroup.center B) = 64561751654400 ∧
      11 ∣ Nat.card (B ⧸ Subgroup.center B) := by
  set f : S ≃* CFSG.Sporadic.Fi24.J := e.trans CFSG.Sporadic.Fi24.fi24EquivJ
  have hx2 : f s * f s = 1 := by
    rw [← map_mul, ← sq, ← hs, pow_orderOf_eq_one, map_one]
  have hx1 : f s ≠ 1 := fun h => by
    rw [MulEquiv.map_eq_one_iff] at h
    rw [h, orderOf_one] at hs
    omega
  refine @component_quotient_of_mulEquiv S CFSG.Sporadic.Fi24.J _ inferInstance f s
    (fun n => n = 64561751654400 ∧ 11 ∣ n) ?_ B hB
  intro B' hB'
  rcases CFSG.Sporadic.Fi24.isConj_tJ_or_r2 CFSG.Fischer.polarFacts
      CFSG.Sporadic.Fi23.d1_mem_localClass CFSG.Sporadic.Fi23.involution_cover hx2 hx1 with h | h
  · refine @component_quotient_of_isConj CFSG.Sporadic.Fi24.J inferInstance _ _ h.symm
      (fun n => n = 64561751654400 ∧ 11 ∣ n) (fun B'' hB'' => ?_) B' hB'
    have hc := card_quotient_center_of_component_tJ hB''
    exact ⟨hc, by rw [hc]; norm_num⟩
  · exact @component_quotient_of_isConj CFSG.Sporadic.Fi24.J inferInstance _ _
      (h.trans isConj_t2_fi24R2).symm (fun n => n = 64561751654400 ∧ 11 ∣ n)
      (fun B'' hB'' => absurd hB'' (fi24_no_component_r2 B'')) B' hB'

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial in
theorem CTI_commuting_block_Fi24prime_overgroup_exclusion
    {G : Type*} [Group G] [Finite G]
    {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) :
    ¬ Nonempty (L ⧸ center L ≃* NativeSporadic.Fi24prime) := by
  classical
  rintro ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hodd, hπKq, hcomm, hloc, -⟩ :=
    escaping_block_quotient_inherits_local_components hq heven hJ hΔ hL hML hLH
  obtain ⟨K₁, hK₁, K₂, hK₂, hne⟩ := hΔ
  have hinv : ∀ K ∈ block J, ∃ t : L, (t : G) ∈ K ∧ orderOf t = 2 := by
    intro K hK
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := centerQuotientImage L K) 2
      (even_iff_two_dvd.1 (hπKq K hK).2)
    obtain ⟨t, htK, ht2, -⟩ := exists_involution_lift_of_odd_center hodd u.2
      (by rw [Subgroup.orderOf_coe, hu])
    exact ⟨t, htK, ht2⟩
  have h11 : ∀ Ka ∈ block J, ∀ Kb ∈ block J, Ka ≠ Kb →
      11 ∣ Nat.card (centerQuotientImage L Ka ⧸ center (centerQuotientImage L Ka)) := by
    intro Ka hKa Kb hKb hab
    obtain ⟨t, htK, ht2⟩ := hinv Kb hKb
    obtain ⟨hπt, hcompK⟩ := hloc Ka hKa Kb hKb hab t htK ht2
    have hB := (isComponentOf_iff_isComponent_subgroupOf hcompK.1).1 hcompK
    have h :=
      (CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven e _ hπt _
        hB).2
    let φ := Subgroup.subgroupOfEquivOfLe hcompK.1
    rwa [(Nat.card_congr (QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)).toEquiv)] at h
  have hmul := card_quotient_center_mul_dvd (hcomm K₁ hK₁ K₂ hK₂ hne).2
    (bot_le : (⊥ : Subgroup (L ⧸ center L)) ≤ center (L ⧸ center L))
  rw [Nat.card_congr QuotientGroup.quotientBot.toEquiv, Nat.card_congr e.toEquiv,
    CFSG.Sporadic.Fi24.card_Fi24prime] at hmul
  have h121 := (Nat.mul_dvd_mul (h11 K₁ hK₁ K₂ hK₂ hne) (h11 K₂ hK₂ K₁ hK₁ hne.symm)).trans hmul
  norm_num at h121

end CFSG.Sporadic.FischerOddCore

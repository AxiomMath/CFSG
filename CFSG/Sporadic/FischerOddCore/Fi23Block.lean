module

public import CFSG.Sporadic.FischerOddCore.Fi23NoComp
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotAlternating
public import CFSG.LocalAnalysis.ComponentInitial.GroupCentralQuotient

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG CFSG.LocalCores

section Transport

theorem component_quotient_of_isConj {G : Type*} [Group G] {r x : G} (h : IsConj r x)
    {p : ℕ → Prop}
    (hr : ∀ B : Subgroup ↥(Subgroup.centralizer ({r} : Set G)), IsComponent B →
      p (Nat.card (B ⧸ Subgroup.center B)))
    (B : Subgroup ↥(Subgroup.centralizer ({x} : Set G))) (hB : IsComponent B) :
    p (Nat.card (B ⧸ Subgroup.center B)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have e1 := centralizerMulEquiv (MulAut.conj c⁻¹) x
  have e2 : ↥(Subgroup.centralizer ({MulAut.conj c⁻¹ x} : Set G)) ≃*
      ↥(Subgroup.centralizer ({r} : Set G)) :=
    MulEquiv.subgroupCongr (by
      rw [MulAut.conj_apply, ← hc, show c⁻¹ * (c * r * c⁻¹) * c⁻¹⁻¹ = r by group])
  obtain ⟨hB', hcard⟩ := component_quotient_mulEquiv (e1.trans e2) hB
  rw [hcard]
  exact hr _ hB'

theorem component_quotient_of_mulEquiv {S H : Type*} [Group S] [Group H] (f : S ≃* H) (a : S)
    {p : ℕ → Prop}
    (hH : ∀ B : Subgroup ↥(Subgroup.centralizer ({f a} : Set H)), IsComponent B →
      p (Nat.card (B ⧸ Subgroup.center B)))
    (B : Subgroup ↥(Subgroup.centralizer ({a} : Set S))) (hB : IsComponent B) :
    p (Nat.card (B ⧸ Subgroup.center B)) := by
  obtain ⟨hB', hcard⟩ := component_quotient_mulEquiv (centralizerMulEquiv f a) hB
  rw [hcard]
  exact hH _ hB'

end Transport

theorem CTI_Fi23_involution_local_components_simple_quotient_divisible_by_eleven
    {S : Type*}
    [Group S] (e : S ≃* Blueprint.NativeSporadic.Fi23) (a : S) (ha : orderOf a = 2)
    (B : Subgroup (Subgroup.centralizer ({a} : Set S))) (hB : IsComponent B) :
    11 ∣ Nat.card (B ⧸ Subgroup.center B) := by
  set f : S ≃* CFSG.Sporadic.Fi23.J := e.trans CFSG.Sporadic.Fi23.fi23EquivJ
  have hx2 : f a ^ 2 = 1 := by
    rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  have hx1 : f a ≠ 1 := fun h => by
    rw [MulEquiv.map_eq_one_iff] at h
    rw [h, orderOf_one] at ha
    omega
  refine @component_quotient_of_mulEquiv S CFSG.Sporadic.Fi23.J _ inferInstance f a
    (fun n => 11 ∣ n) ?_ B hB
  intro B' hB'
  rcases CFSG.Sporadic.Fi23.involution_cover (f a) hx2 hx1 with h | h | h
  · refine @component_quotient_of_isConj CFSG.Sporadic.Fi23.J inferInstance _ _ h
      (fun n => 11 ∣ n) (fun B'' hB'' => ?_) B' hB'
    show 11 ∣ Nat.card (B'' ⧸ Subgroup.center B'')
    rw [card_quotient_center_of_component_Cd hB'']
    norm_num
  · refine @component_quotient_of_isConj CFSG.Sporadic.Fi23.J inferInstance _ _ h
      (fun n => 11 ∣ n) (fun B'' hB'' => ?_) B' hB'
    show 11 ∣ Nat.card (B'' ⧸ Subgroup.center B'')
    rw [card_quotient_center_of_component_dd1 hB'']
    norm_num
  · exact @component_quotient_of_isConj CFSG.Sporadic.Fi23.J inferInstance _ _ h
      (fun n => 11 ∣ n) (fun B'' hB'' => absurd hB'' (fi23_no_component_t2 B'')) B' hB'

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial in
theorem CTI_commuting_block_Fi23_overgroup_exclusion
    {G : Type*} [Group G] [Finite G]
    {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) :
    ¬ Nonempty (L ⧸ center L ≃* NativeSporadic.Fi23) := by
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
      CTI_Fi23_involution_local_components_simple_quotient_divisible_by_eleven e _ hπt _ hB
    let φ := Subgroup.subgroupOfEquivOfLe hcompK.1
    rwa [(Nat.card_congr (QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)).toEquiv)] at h
  have hmul := card_quotient_center_mul_dvd (hcomm K₁ hK₁ K₂ hK₂ hne).2
    (bot_le : (⊥ : Subgroup (L ⧸ center L)) ≤ center (L ⧸ center L))
  rw [Nat.card_congr QuotientGroup.quotientBot.toEquiv, Nat.card_congr e.toEquiv,
    CFSG.Sporadic.Fi23.card_Fi23] at hmul
  have h121 := (Nat.mul_dvd_mul (h11 K₁ hK₁ K₂ hK₂ hne) (h11 K₂ hK₂ K₁ hK₁ hne.symm)).trans hmul
  norm_num at h121

end CFSG.Sporadic.FischerOddCore

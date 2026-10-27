module

public import CFSG.Sporadic.SmallOddCore.J2Local
public import CFSG.LocalAnalysis.ComponentInitial.EscapingNotAlternating
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

theorem card_primeFactors_twelve : (Nat.primeFactors 12).card ≤ 2 := by
  refine (Finset.card_le_card fun r hr => ?_).trans (Finset.card_le_two (a := 2) (b := 3))
  rw [Finset.mem_insert, Finset.mem_singleton]
  have hr' := Nat.prime_of_mem_primeFactors hr
  have hd := Nat.dvd_of_mem_primeFactors hr
  have hle := Nat.le_of_dvd (by norm_num) hd
  clear hr
  interval_cases r <;> simp_all (config := { decide := true })

theorem commuting_block_j2_overgroup_exclusion
    {G : Type*} [Group G] [Finite G]
    {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) :
    ¬ Nonempty (L ⧸ center L ≃* NativeSporadic.J2) := by
  classical
  rintro ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hodd, hπKq, hcomm, hloc, -⟩ :=
    escaping_block_quotient_inherits_local_components hq heven hJ hΔ hL hML hLH
  obtain ⟨K₁, hK₁, K₂, hK₂, hne⟩ := hΔ
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := centerQuotientImage L K₂) 2
    (even_iff_two_dvd.1 (hπKq K₂ hK₂).2)
  obtain ⟨t, htK, ht2, -⟩ := exists_involution_lift_of_odd_center hodd u.2
    (by rw [Subgroup.orderOf_coe, hu])
  obtain ⟨hπt, hcompK⟩ := hloc K₁ hK₁ K₂ hK₂ hne t htK ht2
  have h12 := cti_j2_involution_local_components_ambient_centralizer_order_twelve ⟨e⟩ hπt hcompK
  have hle : centerQuotientImage L K₂ ≤
      centralizer (centerQuotientImage L K₁ : Set (L ⧸ center L)) := by
    rw [← commutator_eq_bot_iff_le_centralizer]
    rw [commutator_comm]
    exact (hcomm K₁ hK₁ K₂ hK₂ hne).2
  have hsolv : Group.IsSolvable ↥(centralizer (centerQuotientImage L K₁ : Set (L ⧸ center L))) := by
    apply isSolvable_of_card_primeFactors_le_two
    rw [h12]
    exact card_primeFactors_twelve
  have hq2 := (hπKq K₂ hK₂).1
  rw [ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native] at hq2
  have hperf : Group.IsPerfect ↥(centerQuotientImage L K₂) := hq2.1
  have hnt : Nontrivial ↥(centerQuotientImage L K₂) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    obtain ⟨a, b, hab⟩ := hq2.2.2
    exact hab (Subsingleton.elim _ _)
  have : Group.IsSolvable ↥(centerQuotientImage L K₂) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  exact Group.IsPerfect.not_isSolvable _ this

end CFSG.Sporadic.SmallOddCore

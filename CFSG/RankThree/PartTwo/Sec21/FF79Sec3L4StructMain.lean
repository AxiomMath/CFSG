module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Struct2
import all CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21 Subgroup
open CFSG.Assembly (InCatalog)

variable {H : Type} [Group H] [Finite H] {β : MulAut H} {Z K : Subgroup H} {z₀ : H}
variable (hd : FF79APData β Z K z₀)
include hd

theorem K_le_apFix : K ≤ apFix β (layer H) := fun k hk => ⟨K_le_L hd hk, hd.K_fix k hk⟩

theorem ap_K_comp : IsComponent (K.subgroupOf (apFix β (layer H))) := by
  obtain ⟨e⟩ := hd.K_a5
  have hq : IsQuasisimple (alternatingGroup (Fin 5)) :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup alt5_nonab).1
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (e.symm.trans (Subgroup.subgroupOfEquivOfLe (K_le_apFix hd)).symm) hq, ?_⟩
  haveI : (K.subgroupOf (apFix β (layer H))).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hd.K_nor g (by simpa using g.2.2) n hn⟩
  exact Subgroup.Normal.isSubnormal inferInstance

theorem ap_others : ∀ K' : Subgroup H, K' ≤ apFix β (layer H) →
    IsComponent (K'.subgroupOf (apFix β (layer H))) → K' ≠ K → Nat.Coprime 3 (Nat.card K') := by
  intro K' hK'M hK'c hne
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcop
  have hdvd : 3 ∣ Nat.card K' := by
    by_contra h
    exact hcop ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h)
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥K') 3 hdvd
  rcases CFSG.LocalCores.distinct_components_commute (ap_K_comp hd) hK'c with h | h
  · apply hne
    have := Subgroup.subgroupOf_inj.1 h
    rwa [inf_of_le_left (K_le_apFix hd), inf_of_le_left hK'M, eq_comm] at this
  · have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
    have hcomm : ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k := by
      intro k hk k' hk'
      have hk1 : (⟨k, K_le_apFix hd hk⟩ : ↥(apFix β (layer H))) ∈
          K.subgroupOf (apFix β (layer H)) := Subgroup.mem_subgroupOf.2 hk
      have hk2 : (⟨k', hK'M hk'⟩ : ↥(apFix β (layer H))) ∈
          K'.subgroupOf (apFix β (layer H)) := Subgroup.mem_subgroupOf.2 hk'
      have := Subgroup.mem_centralizer_iff.1 (hcen hk1) _ hk2
      exact (congrArg Subtype.val this).symm
    have hu' : orderOf (u : H) = 3 := by rw [Subgroup.orderOf_coe]; exact hu
    obtain ⟨a, haK, ha3⟩ := K_order3 hd
    have huM := hK'M u.2
    refine no_fixed_pair hd (x := a) (y := (u : H)) (K_le_L hd haK) huM.1 ha3 hu'
      (hcomm a haK u u.2) (hd.K_fix a haK) (by simpa using huM.2) ?_
    intro hmem
    have huK : (u : H) ∈ K := (zpowers_le.2 haK) hmem
    have := K_central hd huK fun w hw => hcomm w hw u u.2
    rw [this, orderOf_one] at hu'
    omega

theorem ap_catalog : InCatalog ↥(layer H) := by
  haveI := L_facts_simple hd
  haveI := layer_normal_of_ap (H := H)
  have hq := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (L_nonab hd)).1
  exact hd.catalog (layer H) ⟨hq, Subgroup.Normal.isSubnormal inferInstance⟩ (L_facts_simple hd)

theorem ap_struct :
    ∃ L : Subgroup H, FF79APStruct β K L :=
  ⟨layer H,
    { layer_eq := rfl
      simple := L_facts_simple hd
      nonab := L_nonab hd
      β_mem := L_stable hd
      K_le := K_le_L hd
      absyl := ap_absyl hd
      inv3 := ap_inv3 hd
      outer := ap_outer hd
      K_comp := ap_K_comp hd
      others := ap_others hd
      catalog := ap_catalog hd
      exp3 := hd.exp3 }⟩

end CFSG.RankThree.PartTwo.Sec21.FF79

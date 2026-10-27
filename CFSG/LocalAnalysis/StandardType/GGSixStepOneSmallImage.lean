module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneSmallBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly

open scoped commutatorElement

section Images

variable {G : Type} [Group G]

theorem ggSubgroupOf_commutator {J V Y : Subgroup G} (hJ : J ≤ Y) (hV : V ≤ Y) :
    (⁅J, V⁆ : Subgroup G).subgroupOf Y = ⁅J.subgroupOf Y, V.subgroupOf Y⁆ := by
  have hJV : (⁅J, V⁆ : Subgroup G) ≤ Y := Subgroup.commutator_le.mpr fun a ha b hb =>
    commutatorElement_mem_of_mem (hJ ha) (hV hb)
  apply Subgroup.map_injective Y.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hJV, Subgroup.map_commutator,
    Subgroup.map_subgroupOf_eq_of_le hJ, Subgroup.map_subgroupOf_eq_of_le hV]

theorem ggLe_pPrimeCoreOf_of_map_eq_bot (p : ℕ) {S Y : Subgroup G} (hSY : S ≤ Y)
    (h : (S.subgroupOf Y).map (QuotientGroup.mk' (LargeEvenPPrimeCore p ↥Y)) = ⊥) :
    S ≤ LargeEvenPPrimeCoreOf p Y := by
  have h' : S.subgroupOf Y ≤ LargeEvenPPrimeCore p ↥Y := by
    have := (Subgroup.map_eq_bot_iff _).mp h
    rwa [QuotientGroup.ker_mk'] at this
  intro s hs
  exact ⟨⟨s, hSY hs⟩, h' (Subgroup.mem_subgroupOf.mpr hs), rfl⟩

theorem ggMap_le_normalizer_map (p : ℕ) {J V Y : Subgroup G}
    (hJV : J ≤ Subgroup.normalizer (V : Set G)) :
    (J.subgroupOf Y).map (QuotientGroup.mk' (LargeEvenPPrimeCore p ↥Y)) ≤
      Subgroup.normalizer
        (((V.subgroupOf Y).map (QuotientGroup.mk' (LargeEvenPPrimeCore p ↥Y)) :
          Subgroup (↥Y ⧸ LargeEvenPPrimeCore p ↥Y)) : Set (↥Y ⧸ LargeEvenPPrimeCore p ↥Y)) := by
  refine le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map _)
  intro j hj
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.mp (hJV (Subgroup.mem_subgroupOf.mp hj)) h

theorem ggIsSubnormal_map_quotient (p : ℕ) {J C Y : Subgroup G} (hJC : IsSubnormal J C) :
    IsSubnormal ((J.subgroupOf Y).map (QuotientGroup.mk' (LargeEvenPPrimeCore p ↥Y)))
      ((C.subgroupOf Y).map (QuotientGroup.mk' (LargeEvenPPrimeCore p ↥Y))) := by
  have h1 := (CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_iff_open J C).1 hJC
  have h2 := CFSG.ComponentClassification.LBalance.subnormal_subgroupOf h1 Y
  have h3 := CFSG.ComponentClassification.Components.chain_map
    (QuotientGroup.mk' (LargeEvenPPrimeCore p ↥Y)) h2
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isSubnormal_iff_open _ _).2 h3

end Images

section Main

variable {G : Type} [Group G] [Finite G]

theorem ggCommutator_le_pPrimeCoreOf {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {Y A J V : Subgroup G} {x : G} (hA : LargeEvenPComponent p Y A) (hJA : J ≤ A)
    (hJ : IsComponentOf J (Y ⊓ Subgroup.centralizer {x})) (hpJ : p ∣ Nat.card J)
    (hxA : x ∈ Subgroup.normalizer (A : Set G)) (hxp : x ^ p = 1)
    (hxc : ⁅A, Subgroup.zpowers x⁆ ≤ LargeEvenPPrimeCoreOf p A)
    (hVY : V ≤ Y) (hJV : J ≤ Subgroup.normalizer (V : Set G)) (hV : IsPGroup q V) :
    ⁅J, V⁆ ≤ LargeEvenPPrimeCoreOf p Y := by
  set π := QuotientGroup.mk' (LargeEvenPPrimeCore p ↥Y) with hπ
  have hAY : A ≤ Y := hA.1
  have hJY : J ≤ Y := hJ.1.trans inf_le_left
  have hA₀Y : LargeEvenPPrimeCoreOf p A ≤ LargeEvenPPrimeCoreOf p Y :=
    ggPPrimeCoreOf_le_of_isSubnormal hA.2.1
  have hĀ : IsComponentOf ((A.subgroupOf Y).map π) ⊤ := hA.2.2.1
  have hCA : ((A ⊓ Subgroup.centralizer {x}).subgroupOf Y).map π = (A.subgroupOf Y).map π := by
    refine le_antisymm (Subgroup.map_mono (Subgroup.subgroupOf_mono Y inf_le_left)) ?_
    rintro _ ⟨⟨a, haY⟩, ha, rfl⟩
    have ha' : a ∈ A := ha
    obtain ⟨c, hc, hca⟩ := ggExists_centralizer_mul (Subgroup.map_subtype_le _)
      (ggNormalizer_le_normalizer_pPrimeCoreOf p A hxA) hxp
      ((Nat.Prime.coprime_iff_not_dvd Fact.out).mp (ggPPrimeCoreOf_coprime A)) hxc ha'
    refine ⟨⟨c, hAY (Subgroup.mem_inf.mp hc).1⟩, Subgroup.mem_subgroupOf.mpr hc, ?_⟩
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨w, hw, hwe⟩ := hA₀Y hca
    have : (⟨c, hAY (Subgroup.mem_inf.mp hc).1⟩ : ↥Y)⁻¹ * ⟨a, haY⟩ = w :=
      Subtype.ext (by simpa using hwe.symm)
    rw [this]
    exact hw
  have hJC : IsSubnormal J (A ⊓ Subgroup.centralizer {x}) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hJ
      (le_inf hJA (hJ.1.trans inf_le_right)) (inf_le_inf_right _ hAY)).2.1
  have hJCi := ggIsSubnormal_map_quotient p (Y := Y) hJC
  rw [hCA] at hJCi
  have hJtop : IsSubnormal ((J.subgroupOf Y).map π) ⊤ :=
    CFSG.LocalAnalysis.ComponentInitial.assembly_isSubnormal_trans hJCi hĀ.2.1
  have hJĀ : (J.subgroupOf Y).map π ≤ (A.subgroupOf Y).map π :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono Y hJA)
  have hJJ : ⁅J, J⁆ = J := commutator_self_eq_of_isQuasisimple hJ.2.2
  have himgJJ : ⁅(J.subgroupOf Y).map π, (J.subgroupOf Y).map π⁆ = (J.subgroupOf Y).map π := by
    rw [← Subgroup.map_commutator, ← ggSubgroupOf_commutator hJY hJY, hJJ]
  have heq : (J.subgroupOf Y).map π = (A.subgroupOf Y).map π := by
    rcases isComponentOf_le_or_commutator_eq_bot hĀ hJtop with h | h
    · exact le_antisymm hJĀ h
    · exfalso
      have hbot : (J.subgroupOf Y).map π = ⊥ := by
        rw [← himgJJ, eq_bot_iff, ← h]
        exact Subgroup.commutator_mono hJĀ le_rfl
      have hJW := ggLe_pPrimeCoreOf_of_map_eq_bot p hJY hbot
      exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp
        ((ggPPrimeCoreOf_coprime Y).coprime_dvd_right (Subgroup.card_dvd_of_le hJW)) hpJ
  have hJcomp : IsComponentOf ((J.subgroupOf Y).map π) ⊤ := heq ▸ hĀ
  have hVq : IsPGroup q ↥((V.subgroupOf Y).map π) :=
    (hV.of_equiv (Subgroup.subgroupOfEquivOfLe hVY).symm).map π
  have hc := ggCommutator_eq_bot_of_isComponentOf hJcomp le_top (ggMap_le_normalizer_map p hJV)
    hVq
  rw [← Subgroup.map_commutator, ← ggSubgroupOf_commutator hJY hVY] at hc
  exact ggLe_pPrimeCoreOf_of_map_eq_bot p (Subgroup.commutator_le.mpr fun a ha b hb =>
    commutatorElement_mem_of_mem (hJY ha) (hVY hb)) hc

end Main

end CFSG.StandardType

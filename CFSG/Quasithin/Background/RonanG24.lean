module

public import CFSG.Quasithin.H13.VolIG248

public section

namespace CFSG.Quasithin.RonanG24

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem tildeOf_commutator {V₁ U K : Subgroup G} (hU : U ≤ Subgroup.normalizer (V₁ : Set G))
    (hK : K ≤ Subgroup.normalizer (V₁ : Set G)) :
    tildeOf V₁ ⁅U, K⁆ = ⁅tildeOf V₁ U, tildeOf V₁ K⁆ := by
  have hc : ⁅U, K⁆.subgroupOf (Subgroup.normalizer (V₁ : Set G)) =
      ⁅U.subgroupOf (Subgroup.normalizer (V₁ : Set G)),
        K.subgroupOf (Subgroup.normalizer (V₁ : Set G))⁆ := by
    apply Subgroup.map_injective (Subgroup.normalizer (V₁ : Set G)).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hU,
      Subgroup.map_subgroupOf_eq_of_le hK,
      Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le.2 fun u hu k hk =>
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hU hu) (hK hk))
          (Subgroup.inv_mem _ (hU hu))) (Subgroup.inv_mem _ (hK hk)))]
  unfold tildeOf secImg
  rw [hc, Subgroup.map_commutator]

theorem commutator_sup_eq_of_tildeOf {V₁ U K : Subgroup G}
    (hU : U ≤ Subgroup.normalizer (V₁ : Set G)) (hK : K ≤ Subgroup.normalizer (V₁ : Set G))
    (hKU : K ≤ Subgroup.normalizer (U : Set G)) (hV₁U : V₁ ≤ U)
    (h : ⁅tildeOf V₁ U, tildeOf V₁ K⁆ = tildeOf V₁ U) : ⁅U, K⁆ ⊔ V₁ = U := by
  refine le_antisymm (sup_le ?_ hV₁U) fun u hu => ?_
  · rw [Subgroup.commutator_le]
    intro u hu k hk
    have hk' : k * u⁻¹ * k⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 (hKU hk) _).1 (U.inv_mem hu)
    have e : ⁅u, k⁆ = u * (k * u⁻¹ * k⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact U.mul_mem hu hk'
  · have h1 : tmk V₁ ⟨u, hU hu⟩ ∈ tildeOf V₁ (⁅U, K⁆ ⊔ V₁) := by
      have h0 : tmk V₁ ⟨u, hU hu⟩ ∈ tildeOf V₁ U := secMk_mem_secImg hu
      rw [← h, ← tildeOf_commutator hU hK] at h0
      exact secImg_mono le_sup_left h0
    exact (secMk_mem_secImg_iff le_sup_right).1 h1

theorem isQ8Sq_subgroups {U : Subgroup G} (h : IsQ8Sq ↥U) :
    Nat.card U = 32 ∧ ∃ A B : Subgroup G, A ≤ U ∧ B ≤ U ∧ A ⊔ B = U ∧ ⁅A, B⁆ = ⊥ ∧
      Nonempty (↥A ≃* QuaternionGroup 2) ∧ Nonempty (↥B ≃* QuaternionGroup 2) := by
  obtain ⟨hcard, A, B, ⟨hAB, hsup⟩, ⟨eA⟩, ⟨eB⟩⟩ := h
  refine ⟨hcard, A.map U.subtype, B.map U.subtype, Subgroup.map_subtype_le A,
    Subgroup.map_subtype_le B, ?_, ?_,
    ⟨(A.equivMapOfInjective U.subtype U.subtype_injective).symm.trans eA⟩,
    ⟨(B.equivMapOfInjective U.subtype U.subtype_injective).symm.trans eB⟩⟩
  · rw [← Subgroup.map_sup, hsup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  · rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 (hAB ha) b hb)

end Generic

section Eight

variable {G : Type} [Group G] [Finite G]

theorem G24_eight {V V₁ L T H : Subgroup G} (hyp : AlmostSpecialA5Hyp V V₁ L T H) {g : G}
    (hg : g ∈ L) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G))
    (hc : ⁅tildeOf V₁ (conjClosure V H), tildeOf V₁ (lOne L V₁)⁆ = tildeOf V₁ (conjClosure V H))
    (hO2 : pCoreOf 2 (lOne L V₁) ≤ pCoreOf 2 H) :
    conjClosure V H ⊔ rconj (conjClosure V H) g = L ∧ (IsShort2 L ∧ IsAltType L 5) ∧
      pCoreOf 2 (conjClosure V H ⊔ rconj (conjClosure V H) g) = conjClosure V₁ L ∧
      conjClosure V H = pCoreOf 2 (lOne L V₁) ∧
      (Nat.card (conjClosure V H) = 32 ∧ ∃ A B : Subgroup G, A ≤ conjClosure V H ∧
        B ≤ conjClosure V H ∧ A ⊔ B = conjClosure V H ∧ ⁅A, B⁆ = ⊥ ∧
        Nonempty (↥A ≃* QuaternionGroup 2) ∧ Nonempty (↥B ≃* QuaternionGroup 2)) := by
  have hLH : lOne L V₁ ≤ H := le_sup_left.trans hyp.base.lOne_sup_le
  have hcomm : ⁅conjClosure V H, lOne L V₁⁆ ⊔ V₁ = conjClosure V H :=
    commutator_sup_eq_of_tildeOf hyp.base.conjClosure_le_N (hLH.trans hyp.base.H_le)
      (hLH.trans (le_normalizer_conjClosure V H)) (hyp.base.le_V.trans (le_conjClosure V H)) hc
  obtain ⟨hI, hs, ha, hS, hU, hQ⟩ := H13.VolI.stmtG248Core hyp.toCore hcomm hO2 hg hgN
  refine ⟨hI, ⟨hs, ha⟩, ?_, hU, isQ8Sq_subgroups hQ⟩
  rw [hI]
  exact hS

end Eight

end CFSG.Quasithin.RonanG24

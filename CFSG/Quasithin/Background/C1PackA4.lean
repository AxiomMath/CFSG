module

public import CFSG.Quasithin.Background.C1GNSolvAlt
public import CFSG.Quasithin.EmptyFaithful.S14110AuxCommute

public section

namespace CFSG.Quasithin.C1Pack

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pCoreOf_subgroupOf_self (L : Subgroup G) :
    (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := by
  exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _

omit [Finite G] in
theorem isAltType_three_of_card_three {L : Subgroup G} (hL : IsShort2 L)
    (h3 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3) : IsAltType L 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic (↥L ⧸ CFSG.pCore 2 ↥L) := isCyclic_of_prime_card (p := 3) h3
  have hcyc' : IsCyclic (alternatingGroup (Fin 3)) :=
    isCyclic_of_prime_card (p := 3) C1GN.alt3_card
  let e : ↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 3) :=
    mulEquivOfCyclicCardEq (h3.trans C1GN.alt3_card.symm)
  let φ : ↥L →* alternatingGroup (Fin 3) := e.toMonoidHom.comp (QuotientGroup.mk' _)
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = CFSG.pCore 2 ↥L := by
    ext x
    simp only [MonoidHom.mem_ker, φ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  exact C1GN.isAltType_three_of_isAltQuotient (C := pCoreOf 2 L) hL
    ⟨φ, hφs, by rw [pCoreOf_subgroupOf_self]; exact hker⟩

theorem commutator_eq_bot_of_card_three {H B₁ B₂ : Subgroup G} (hH : CharTwo H)
    (hB₁ : IsBlock2 H B₁) (h₁ : Nat.card (↥B₁ ⧸ CFSG.pCore 2 ↥B₁) = 3)
    (hB₂ : IsBlock2 H B₂) (h₂ : Nat.card (↥B₂ ⧸ CFSG.pCore 2 ↥B₂) = 3) (hne : B₁ ≠ B₂) :
    ⁅B₁, B₂⁆ = ⊥ := by
  obtain ⟨c, hc⟩ := S14110.A4Data.of_isShort2 hB₁.1 (isAltType_three_of_card_three hB₁.1 h₁)
  obtain ⟨c', hc'⟩ := S14110.A4Data.of_isShort2 hB₂.1 (isAltType_three_of_card_three hB₂.1 h₂)
  rcases S14110.commute_or_eq_of_isSubnormal hH hB₁.2.1 hB₂.2.1 hB₁.2.2 hB₂.2.2 hc hc' with
    h | h
  · exact absurd h hne
  · rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (h x hx y hy).symm

end CFSG.Quasithin.C1Pack

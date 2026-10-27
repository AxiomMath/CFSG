module

public import CFSG.Sporadic.Schreier.TitsAutD
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SuzukiOuterOdd
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeModel
public import CFSG.Sporadic.Schreier.TitsOuter

public noncomputable section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_model_field_outer_group_and_inner_involutions)

theorem mem_inner_of_sq_eq_one_of_odd {G : Type*} [Group G] (hodd : Odd (Nat.card (Outer G)))
    {α : MulAut G} (hα : α ^ 2 = 1) : α ∈ inner G := by
  have h2 : orderOf (QuotientGroup.mk α : Outer G) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one])
  have hcard : orderOf (QuotientGroup.mk α : Outer G) ∣ Nat.card (Outer G) :=
    orderOf_dvd_natCard _
  have h1 : orderOf (QuotientGroup.mk α : Outer G) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.2 hodd) h2 hcard
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem titsD_mem_inner_of_sq_eq_one
    {α : MulAut titsD} (hα : α ^ 2 = 1) : α ∈ inner titsD := by
  obtain ⟨a, rfl⟩ := titsConj_surjective α
  have ha : (a : Equiv.Perm (Fin 1755)) ^ 2 = 1 := by
    have : a ^ 2 = 1 := titsConj_injective (by rw [map_pow, hα, map_one])
    exact congrArg Subtype.val this
  have haD : (a : Equiv.Perm (Fin 1755)) ∈ titsD := by
    by_cases h1 : (a : Equiv.Perm (Fin 1755)) = 1
    · rw [h1]
      exact one_mem _
    · exact titsA_involution_mem_D a.2 (orderOf_eq_prime ha h1)
  rw [← map_titsConj_titsD]
  exact ⟨a, haD, rfl⟩

theorem mem_inner_of_congr {G H : Type*} [Group G] [Group H] (e : G ≃* H) {α : MulAut G}
    (h : MulAut.congr e α ∈ inner H) : α ∈ inner G := by
  rw [← inner_map_congr e] at h
  obtain ⟨β, hβ, hβα⟩ := h
  rw [MulEquiv.coe_toMonoidHom] at hβα
  rwa [← (MulAut.congr e).injective hβα]

theorem CLS_Suzuki_large_Ree_Tits_involutions_inner
    (L : Type) [Group L] (f : ℕ)
    (h : CFSG.Blueprint.SuzukiModel L 2 f ∨ CFSG.Blueprint.ReeTitsModel L .twistedF4 2 f ∨
      CFSG.Blueprint.ReeTitsModel L .Tits 2 1) :
    ∀ α : MulAut L, α ^ 2 = 1 → α ∈ inner L := by
  intro α hα
  rcases h with h | h | h
  · obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := h
    have hodd := CFSG.ProperTwoGeneratedCore.HighRankPair.odd_card_outer_suzukiGroup ha
      (hK.trans (by rw [hf]))
    exact mem_inner_of_sq_eq_one_of_odd
      (by rwa [Nat.card_congr (equivalence e).toEquiv]) hα
  · exact (large_Ree_model_field_outer_group_and_inner_involutions L 2 f h).2.2.2.2.2.1 α hα
  · obtain ⟨e⟩ := titsModelEquiv L 2 1 h
    exact mem_inner_of_congr e (titsD_mem_inner_of_sq_eq_one (by rw [← map_pow, hα, map_one]))

end CFSG.Sporadic.Schreier.Tits

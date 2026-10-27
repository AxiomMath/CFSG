module

public import CFSG.Quasithin.Vol2.Ch4Sec3C57Lin
public import CFSG.Quasithin.Vol2.Ch4Sec3C57A5c

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace C57

variable {G : Type} [Group G] [Finite G]

theorem Setup.lemmaC57 {H M₀ R K : Subgroup G} (h : Setup H M₀ R K) :
    (M₀ ⊓ Subgroup.normalizer (K : Set G)).relIndex M₀ = 2 := by
  rcases h.block.2 with hlin | h3 | h5
  · exact h.relIndex_eq_two_of_lin (Or.inl hlin)
  · exact h.relIndex_eq_two_of_lin (Or.inr h3)
  · exact h.relIndex_eq_two_of_alt5 h5

theorem oTwoUpper_sup_eq_of_short {L T : Subgroup G} (hL : IsShort2 L) (hT : IsPGroup 2 T)
    (hTN : T ≤ Subgroup.normalizer (L : Set G)) : oTwoUpper (L ⊔ T) = L := by
  refine le_antisymm (oTwoUpper_le_of_pow_mem fun _ hx => C1.exists_pow_mem_of_mem_sup hT hTN hx)
    ((?_ : L ≤ oTwoUpper L).trans (oTwoUpper_mono le_sup_left))
  have hKL : oTwoUpper L ≤ L := oTwoUpper_le L
  have hn : ((oTwoUpper L).subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).mpr (le_normalizer_oTwoUpper L)
  have hp : IsPGroup 2 (↥L ⧸ (oTwoUpper L).subgroupOf L) := by
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper L l.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hk
  have htop := hL.1 _ hp
  intro l hl
  have : (⟨l, hl⟩ : ↥L) ∈ (oTwoUpper L).subgroupOf L := by rw [htop]; trivial
  exact Subgroup.mem_subgroupOf.mp this

end C57

end CFSG.Quasithin.H13.Ch4

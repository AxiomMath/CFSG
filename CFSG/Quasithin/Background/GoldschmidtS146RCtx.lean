module

public import CFSG.Quasithin.EmptyFaithful.S146B0

public section

namespace CFSG.Quasithin.GoldS146R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

structure Ctx146 {G : Type} [Group G] [Finite G] (T M K : Subgroup G) : Prop where
  setting : Setting146 G T M
  htm : IsHTM T M (K ⊔ T)
  comp : K ∈ cComp (K ⊔ T)
  norm : T ≤ Subgroup.normalizer (K : Set G)
  simple : IsSimpleGroup (KBar K)
  borel : K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ≤ M

section Ctx

variable {G : Type} [Group G] [Finite G] {T M K : Subgroup G}

theorem Ctx146.le_M (c : Ctx146 T M K) : T ≤ M := c.setting.hyp.m_max.1.2

theorem Ctx146.sylow (c : Ctx146 T M K) : IsSylowTwoOf T (K ⊔ T) :=
  isSylowTwoOf_of_quasithinIsSylowTwo c.setting.hyp.sylow le_sup_right

theorem Ctx146.sylow_inf (c : Ctx146 T M K) : IsSylowTwoOf (T ⊓ K) K :=
  A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp c.comp) c.sylow

theorem Ctx146.pCore_le (c : Ctx146 T M K) : pCoreOf 2 K ≤ T ⊓ K :=
  pCoreOf_two_le_of_isSylowTwoOf c.sylow_inf

theorem Ctx146.le_H (_c : Ctx146 T M K) : K ≤ K ⊔ T := le_sup_left

end Ctx

section Hstar

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem exists_hstar_below {H : Subgroup G} (hH : InH T H) (hHM : ¬ H ≤ M) :
    ∃ H₂ : Subgroup G, IsHStar T M H₂ ∧ H₂ ≤ H := by
  have hne : {Y : Subgroup G | InH T Y ∧ ¬ Y ≤ M ∧ Y ≤ H}.Nonempty := ⟨H, hH, hHM, le_rfl⟩
  obtain ⟨a, ⟨ha1, ha2, ha3⟩, hmin⟩ := WellFounded.has_min wellFounded_lt _ hne
  refine ⟨a, ⟨ha1, ha2, fun Y hY hYa hYM => ?_⟩, ha3⟩
  by_contra hne'
  exact hmin Y ⟨hY, hYM, hYa.trans ha3⟩ (lt_of_le_of_ne hYa hne')

end Hstar

end CFSG.Quasithin.GoldS146R

module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111Idx
public import CFSG.Quasithin.Background.F6Solvable

public section

namespace CFSG.Quasithin

namespace Y15111

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem nonempty_perm_equiv_of_relIndex_three {T K : Subgroup G} (hT : IsPGroup 2 T) (hTK : T ≤ K)
    (hidx : T.relIndex K = 3) (hn : ¬ K ≤ Subgroup.normalizer (T : Set G)) :
    Nonempty (↥K ⧸ CFSG.Open.pCore 2 ↥K ≃* Equiv.Perm (Fin 3)) :=
  nonempty_perm_equiv_of_index_three (hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTK).symm) hidx
    fun hnorm => hn ((Subgroup.normal_subgroupOf_iff_le_normalizer hTK).mp hnorm)

theorem isGoldschmidtTripleIn_of_index_three {T P1 H : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hTP : T ≤ P1) (hTH : T ≤ H) (hPH : P1 ⊓ H = T) (hP1 : T.relIndex P1 = 3)
    (hH : T.relIndex H = 3) (hnP : ¬ P1 ≤ Subgroup.normalizer (T : Set G))
    (hnH : ¬ H ≤ Subgroup.normalizer (T : Set G)) : F6.IsGoldschmidtTripleIn (P1 ⊔ H) P1 H := by
  refine ⟨rfl, nonempty_perm_equiv_of_relIndex_three hT.1 hTP hP1 hnP,
    nonempty_perm_equiv_of_relIndex_three hT.1 hTH hH hnH, ?_⟩
  rw [hPH]
  refine ⟨hTP.trans le_sup_left, hT.1, fun h2 => hT.2 ?_⟩
  exact h2.trans (Subgroup.relIndex_dvd_index_of_le (hTP.trans le_sup_left))

end Y15111

end CFSG.Quasithin

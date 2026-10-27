module

public import CFSG.Quasithin.EmptyFaithful.SBd7Ms

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S15223

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_of_relIndex_two {S T : Subgroup G} (hST : S ≤ T) (h : S.relIndex T = 2) :
    T ≤ Subgroup.normalizer (S : Set G) := by
  have hn : (S.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two h
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hST).mp hn

theorem pCoreOf_sup_le {K S I : Subgroup G} (hS : IsSylowTwoOf S I) (hKI : K ≤ I) :
    pCoreOf 2 (K ⊔ S) ≤ S :=
  pCoreOf_two_le_of_isSylowTwoOf
    (SBd7.isSylowTwoOf_of_le_of_le' hS le_sup_right (sup_le hKI hS.1))

omit [Finite G] in
theorem le_normalizer_pCoreOf_sup {K S T H : Subgroup G} (hH : H = K ⊔ T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hTS : T ≤ Subgroup.normalizer (S : Set G)) :
    H ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ S) : Set G) := by
  have hK : K ≤ Subgroup.normalizer ((K ⊔ S : Subgroup G) : Set G) :=
    le_sup_left.trans Subgroup.le_normalizer
  have hT : T ≤ Subgroup.normalizer ((K ⊔ S : Subgroup G) : Set G) :=
    fun t ht => Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hTK ht, hTS ht⟩
  rw [hH]
  exact (sup_le hK hT).trans (normalizer_le_normalizer_pCoreOf 2 _)

theorem normalizer_le_of_normal {H Mc C : Subgroup G} (hU : IsUniqueM H Mc) (hC2 : IsPGroup 2 C)
    (hC0 : C ≠ ⊥) (hHC : H ≤ Subgroup.normalizer (C : Set G)) :
    Subgroup.normalizer (C : Set G) ≤ Mc := by
  refine le_of_isUniqueM hU ⟨hHC, fun h => hC0 ?_⟩
  rw [eq_bot_iff]
  exact (le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hC2).trans h.le

end S15223

end CFSG.Quasithin

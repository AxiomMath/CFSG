module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight62GammaAll

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup

theorem map_conj_eq_self_of_mem_of_normal
    {G : Type} [Group G] {L M : Subgroup G} (hLMle : L ≤ M)
    (hLM : (L.subgroupOf M).Normal) {t : G} (ht : t ∈ M) :
    L.map (MulAut.conj t).toMonoidHom = L :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hLMle).mp hLM ht)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

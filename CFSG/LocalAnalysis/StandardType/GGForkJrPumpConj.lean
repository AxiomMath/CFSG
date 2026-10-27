module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGen

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Internal

variable {G : Type} [Group G] [Finite G]

theorem ggRealization_conj {p : ℕ} (hp : p.Prime) {Bs : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) {r : MulAut ↥Bs} {Jr : Subgroup G}
    (hr : GGIsReflection p r) (hind : r ∈ ggInduced Jr Bs)
    (hJC : Jr ≤ Subgroup.centralizer (ggFixG Bs r : Set G))
    (hpc : IsPComponent p (Jr.subgroupOf (Subgroup.centralizer (ggFixG Bs r : Set G)))) :
    GGIsReflection p (ggConjAut Bs hg * r * (ggConjAut Bs hg)⁻¹) ∧
      ggConjAut Bs hg * r * (ggConjAut Bs hg)⁻¹ ∈
        ggInduced (Jr.map (MulAut.conj g).toMonoidHom) Bs ∧
      Jr.map (MulAut.conj g).toMonoidHom ≤
        Subgroup.centralizer (ggFixG Bs (ggConjAut Bs hg * r * (ggConjAut Bs hg)⁻¹) : Set G) ∧
      IsPComponent p ((Jr.map (MulAut.conj g).toMonoidHom).subgroupOf
        (Subgroup.centralizer (ggFixG Bs (ggConjAut Bs hg * r * (ggConjAut Bs hg)⁻¹) : Set G))) := by
  refine ⟨hr.conj' (ggConjAut Bs hg), mem_ggInduced_map_conj hg hind, ?_, ?_⟩
  · rw [ggFixG_conj hg, centralizer_map_conj]
    exact Subgroup.map_mono hJC
  · rw [ggFixG_conj hg, centralizer_map_conj]
    exact (CFSG.ComponentClassification.Burgoyne.isPComponent_subgroupOf_map_iff p hp
      (MulAut.conj g).injective).mp hpc

end Internal

end CFSG.StandardType

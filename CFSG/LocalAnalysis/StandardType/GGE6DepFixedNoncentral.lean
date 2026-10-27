module

public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer

public section

namespace CFSG.StandardType.GGE6Dep

open CFSG CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem normalizes_of_fixed_noncentral {C Lc : Subgroup G} (hLc : IsComponentOf Lc C) {y : G}
    (hy : y ∈ Subgroup.normalizer (C : Set G)) {s : G} (hs : s ∈ Lc)
    (hns : ∃ l ∈ Lc, l * s ≠ s * l) (hsy : y * s * y⁻¹ = s) :
    y ∈ Subgroup.normalizer (Lc : Set G) := by
  have h1 : IsComponentOf (Lc.map (MulAut.conj y).toMonoidHom) C := by
    have h := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hLc y
    rwa [map_conj_eq_of_mem_normalizer hy] at h
  rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute h1 hLc with h | h
  · exact mem_normalizer_iff_map_conj.mpr h
  · exfalso
    have hle : Lc.map (MulAut.conj y).toMonoidHom ≤ Subgroup.centralizer (Lc : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
    have hsmem : s ∈ Lc.map (MulAut.conj y).toMonoidHom :=
      ⟨s, hs, by change MulAut.conj y s = s; rw [MulAut.conj_apply]; exact hsy⟩
    obtain ⟨l, hl, hls⟩ := hns
    exact hls (Subgroup.mem_centralizer_iff.1 (hle hsmem) l hl)

end CFSG.StandardType.GGE6Dep

end

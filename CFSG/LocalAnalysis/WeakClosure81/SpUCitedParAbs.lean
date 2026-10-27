module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

theorem spUCited_le_sylow_of_normal {G : Type} [Group G] [Finite G] {U P : Subgroup G}
    (hU : ∃ T : Sylow 2 G, (T : Subgroup G) = U) (hUP : U ≤ P) {N : Subgroup G} (hNP : N ≤ P)
    (hN : (N.subgroupOf P).Normal) (hN2 : IsPGroup 2 N) : N ≤ U := by
  obtain ⟨T, hT⟩ := hU
  have hnorm : P ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).mp hN
  have hNU : U ≤ Subgroup.normalizer (N : Set G) := hUP.trans hnorm
  have hT2 : IsPGroup 2 U := hT ▸ T.isPGroup'
  have h2sup : IsPGroup 2 (N ⊔ U : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hN2 hT2 hNU
  have hEq : N ⊔ U = (T : Subgroup G) :=
    T.is_maximal' h2sup (by rw [hT]; exact le_sup_right)
  exact (le_sup_left : N ≤ N ⊔ U).trans (hEq.trans_le hT.le)

theorem spUCited_le_inf_normalizer_of_normal {G : Type} [Group G] [Finite G] {U R P : Subgroup G}
    (hU : ∃ T : Sylow 2 G, (T : Subgroup G) = U) (hUR : U ≤ Subgroup.normalizer (R : Set G))
    (hUP : U ≤ P) {n : G} (hn : n ∈ P) {N : Subgroup G} (hNP : N ≤ P)
    (hN : (N.subgroupOf P).Normal) (hN2 : IsPGroup 2 N) :
    N ≤ U ⊓ Subgroup.normalizer ((R.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G) := by
  have hNU : N ≤ U := spUCited_le_sylow_of_normal hU hUP hNP hN hN2
  have hnorm : P ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).mp hN
  have hNmap : N ≤ U.map (MulAut.conj n).toMonoidHom := by
    intro x hx
    have hxN : n⁻¹ * x * n ∈ N := by
      have h := (Subgroup.mem_normalizer_iff.mp (hnorm (P.inv_mem hn)) x).mp hx
      simpa using h
    exact Subgroup.mem_map.mpr ⟨n⁻¹ * x * n, hNU hxN, by
      show MulAut.conj n (n⁻¹ * x * n) = x
      rw [MulAut.conj_apply]
      group⟩
  have hUR' : U.map (MulAut.conj n).toMonoidHom ≤
      Subgroup.normalizer ((R.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G) := by
    rw [← Subgroup.map_normalizer_eq_of_bijective R
      (f := (MulAut.conj n).toMonoidHom) (MulAut.conj n).bijective]
    exact Subgroup.map_mono hUR
  exact le_inf hNU (hNmap.trans hUR')

end CFSG.LocalAnalysis.WeakClosure81

end

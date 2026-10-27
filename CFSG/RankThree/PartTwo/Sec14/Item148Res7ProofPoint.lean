module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.GLS.Basic
public import CFSG.RankThree.PartTwo.Sec14.Std

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Res7Point

variable {G : Type} [Group G] [Finite G]

theorem normalizer_zpowers_le148 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {b : G}
    (hbΩ : Subgroup.zpowers b ∈ omegaA A) {Lb : Subgroup G} (hLb : Lb ∈ lA A b)
    (h3 : 3 ∣ Nat.card Lb) :
    Subgroup.normalizer (Subgroup.zpowers b : Set G) ≤ Subgroup.normalizer (Lb : Set G) := by
  have huniq := (h.chosen136.2 b hbΩ Lb hLb).2
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hmem := map_mem_thetaComponentsAt (MulAut.conj g) hLb.1
  have hgb : g * b * g⁻¹ ∈ Subgroup.zpowers b :=
    (Subgroup.mem_normalizer_iff.mp hg b).mp (Subgroup.mem_zpowers b)
  have hzp : Subgroup.zpowers (g * b * g⁻¹) = Subgroup.zpowers b := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgb) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers]
    exact ((MulAut.conj g).orderOf_eq b).ge
  have hθb : thetaComponentsAt 3 (g * b * g⁻¹) = thetaComponentsAt 3 b := by
    rw [thetaComponentsAt_eq_thetaComponentsIn, thetaComponentsAt_eq_thetaComponentsIn,
      centralizer_singleton_eq_of_zpowers_eq hzp]
  have hmem' : Lb.map (MulAut.conj g).toMonoidHom ∈ thetaComponentsAt 3 b := by
    rw [← hθb]
    exact hmem
  exact huniq _ hmem'
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]; exact h3)

end Res7Point

end CFSG.RankThree.PartTwo.Sec14

module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanThetaJ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6
public import CFSG.GroupTheory.NormalizerConjFixedPoints

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}

theorem centralizer_le_of_mem_zSub_wPT (c : Ctx82E3 D) {P : Subgroup G} {x : G}
    (hcardZ : Nat.card (zSub P c.L) = 3)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (hord : orderOf x = 3) (hxZ : x ∈ zSub P c.L) :
    Subgroup.centralizer ({x} : Set G) ≤ D.M := by
  have hzp : Subgroup.zpowers x ≤ zSub P c.L := Subgroup.zpowers_le.mpr hxZ
  have hcardzp : Nat.card ↥(Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, hord]
  have hEq : Subgroup.zpowers x = zSub P c.L :=
    Subgroup.eq_of_le_of_card_ge hzp (by rw [hcardzp, hcardZ])
  have hCZ : Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer (zSub P c.L : Set G) := by
    rw [← hEq]
    intro y hy
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    have hyx : y * x * y⁻¹ = x := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp hy
      calc y * x * y⁻¹ = (x * y) * y⁻¹ := by rw [h]
        _ = x := by group
    show Subgroup.zpowers (y * x * y⁻¹) = Subgroup.zpowers x
    rw [hyx]
  exact hCZ.trans hNZ

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

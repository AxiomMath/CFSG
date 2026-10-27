module

public import CFSG.GroupTheory.CentralizerSup
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}

theorem zSub_le_centralizer (P L : Subgroup G) :
    zSub P L ≤ Subgroup.centralizer ((P ⊓ L : Subgroup G) : Set G) :=
  inf_le_right

theorem zpowers_eq_zSub_of_mem (c : Ctx82E3 D) {P : Subgroup G}
    (hZcard : Nat.card (zSub P c.L) = 3)
    {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian 3 A) (hZA : zSub P c.L ≤ A)
    {x : G} (hx : x ∈ zSub P c.L) (hx1 : x ≠ 1) :
    Subgroup.zpowers x = zSub P c.L := by
  have hx3 : x ^ 3 = 1 := hA.2 x (hZA hx)
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hzle : Subgroup.zpowers x ≤ zSub P c.L := Subgroup.zpowers_le.mpr hx
  have hxcard : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hord]
  exact Subgroup.eq_of_le_of_card_ge hzle (by rw [hZcard, hxcard])

theorem centralizer_le_normalizer_zSub (c : Ctx82E3 D) {P : Subgroup G}
    (hZcard : Nat.card (zSub P c.L) = 3)
    {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian 3 A) (hZA : zSub P c.L ≤ A)
    {x : G} (hx : x ∈ zSub P c.L) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) := by
  have hz : Subgroup.centralizer ({x} : Set G) =
      Subgroup.centralizer ((zSub P c.L : Subgroup G) : Set G) := by
    rw [← CFSG.centralizer_zpowers_eq_centralizer_singleton x,
      zpowers_eq_zSub_of_mem c hZcard hA hZA hx hx1]
  rw [hz]
  exact Subgroup.centralizer_le_normalizer ((zSub P c.L : Subgroup G) : Set G)

theorem centralizer_le_M_of_mem_zSub (c : Ctx82E3 D) {P : Subgroup G}
    (hZcard : Nat.card (zSub P c.L) = 3)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian 3 A) (hZA : zSub P c.L ≤ A)
    {x : G} (hx : x ∈ zSub P c.L) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) ≤ D.M :=
  (centralizer_le_normalizer_zSub c hZcard hA hZA hx hx1).trans hNZ

theorem le_centralizer_of_le_inf (c : Ctx82E3 D)
    {P A : Subgroup G} (hAPL : A ≤ P ⊓ c.L)
    {x : G} (hx : x ∈ zSub P c.L) : A ≤ Subgroup.centralizer ({x} : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp (zSub_le_centralizer P c.L hx) a (hAPL ha)

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

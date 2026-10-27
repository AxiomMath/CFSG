module

public import CFSG.Blueprint.SourceReeTitsTransport
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Parrott.FixDim

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]

theorem autFixedSubgroup_eq_evenSource (h : Tim79a.ParrottHyp z) (x : ↥(H z)) :
    CFSG.autFixedSubgroup (conjV h x) =
      CFSG.Blueprint.EvenSource.autFixedSubgroup (conjV h x) := by
  ext v
  rw [CFSG.mem_autFixedSubgroup, CFSG.Blueprint.EvenSource.mem_autFixedSubgroup]

theorem conjV_conj_eq (h : Tim79a.ParrottHyp z) (g x : ↥(H z)) :
    conjV h (g * x * g⁻¹) = (MulAut.conj (conjV h g)) (conjV h x) := by
  rw [map_mul, map_mul, map_inv, MulAut.conj_apply]

theorem autFixedSubgroup_conj (h : Tim79a.ParrottHyp z) (g x : ↥(H z)) :
    (CFSG.autFixedSubgroup (conjV h x)).map
        (conjV h g : QuotientV.V z →* QuotientV.V z) =
      CFSG.autFixedSubgroup (conjV h (g * x * g⁻¹)) := by
  rw [autFixedSubgroup_eq_evenSource h x, autFixedSubgroup_eq_evenSource h (g * x * g⁻¹)]
  have h := CFSG.Blueprint.EvenSource.map_autFixedSubgroup_of_conj
    (A := QuotientV.V z) (C := QuotientV.V z)
    (conjV h g) (conjV h x) (conjV h (g * x * g⁻¹)) ?_
  · exact h
  · intro a
    rw [conjV_conj_eq, MulAut.conj_apply]
    simp

theorem fixDimV_conj (h : Tim79a.ParrottHyp z) {x y g : ↥(H z)}
    (hxy : g * x * g⁻¹ = y) :
    fixDimV h y = fixDimV h x := by
  subst hxy
  have hmap := autFixedSubgroup_conj (h := h) g x
  have hcard : Nat.card ↥(CFSG.autFixedSubgroup (conjV h x)) =
      Nat.card ↥(CFSG.autFixedSubgroup (conjV h (g * x * g⁻¹))) := by
    rw [← hmap]
    exact (Subgroup.card_map_of_injective (f := (conjV h g : QuotientV.V z →* QuotientV.V z))
      (conjV h g).injective).symm
  rw [card_fix h x, card_fix h (g * x * g⁻¹)] at hcard
  exact (Nat.pow_right_injective (by norm_num : 2 ≤ 2) hcard).symm

end CFSG.RankThree.GF2n.Parrott

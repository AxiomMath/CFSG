module

public import CFSG.RankThree.GF2n.Stroth80.Sec5Vt
public import CFSG.RankThree.GF2n.Stroth80.Sec7Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec4Model
public import CFSG.RankThree.GF2n.Stroth80.Sec7Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem isCentrePre_le_H0 (hc : Ctx M Q Z B) {n : ℕ} {t : G} (_hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    Z0 ≤ H0 M Z :=
  (IsCentrePre.le hZ0).trans (hc.Rt_le_H0 t)

theorem isElemAbelian_bar_Z0 [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) (hZc : Sec7CentreStatement) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    Assembly.IsElemAbelian 2 (bar M Q Z0) := by
  have hZL : Z0 ≤ LB M Q B := fun z hz =>
    ((hZc G M Q Z B hc n t hs Z0 hZ0 z).mp hz).1
  refine hc.isElemAbelian_bar_LB.mono ?_
  exact Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
    (Subgroup.subgroupOf_mono M hZL)

theorem card_bar_Z0 [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) (hZc : Sec7ZCardStatement) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    Nat.card ↥(bar M Q Z0) = Nat.card Z := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  have hnorm : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, r * y * r⁻¹ ∈ Q := fun r hr y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hr)) y).mp hy
  have hQZ0 : Q ≤ Z0 := IsCentrePre.Q_le hZ0 hQR hnorm
  have hZ0M : Z0 ≤ M := (IsCentrePre.le hZ0).trans (hc.Rt_le_M t)
  have hcard := bar_card_mul_card_of_le (M := M) (S := Z0) hQZ0 hZ0M
  have hZ0card := hZc G M Q Z B hc n t hs Z0 hZ0
  rw [hZ0card, Nat.mul_comm (Nat.card Q) (Nat.card Z)] at hcard
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hcard

theorem four_le_card_bar_Z0 [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) (hZc : Sec7ZCardStatement) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    4 ≤ Nat.card ↥(bar M Q Z0) := by
  rw [card_bar_Z0 hc hs hZc hZ0]
  exact hc.hyp.q4

end CFSG.RankThree.GF2n.Stroth80

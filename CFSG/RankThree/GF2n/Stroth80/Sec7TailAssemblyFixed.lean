module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailHypSub
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailInv717

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem invAbelian_of_irred (hc : Ctx M Q Z B) {t : G} {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hirr : IsIrredModule (Rt M (LB M Q B) t) (hc.CN t) Z0) : InvAbelian hc t Z0 := by
  intro A hZA hAN hRA hAne x hx y hy
  rcases hirr.2.2.2 A hZA hAN hRA with h | h
  · rw [h] at hx hy
    exact hZ0.comm_mem hx (hZ0.le hy)
  · exact absurd h hAne

theorem invAbelian_of_inv717 (hInv : Sec717InvStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) (hp3 : OmegaPlusNat hc t 3) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) : InvAbelian hc t Z0 := by
  intro A hZA hAN hRA hAne x hx y hy
  rcases hInv G M Q Z B hc n t hs hp3 Z0 hZ0 A hZA hAN hRA with h | h | hL
  · rw [h] at hx hy
    exact hZ0.comm_mem hx (hZ0.le hy)
  · exact absurd h hAne
  · exact hL.2.2.2.2.1 x hx y hy

end CFSG.RankThree.GF2n.Stroth80

module

public import CFSG.Quasithin.Vol2.GoldschmidtF48RigFar
public import CFSG.Quasithin.Recognition.F4Thirteen

public section

namespace CFSG.Quasithin.H13.F48Rig

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

universe u

theorem f1_eq_f2 {α : RankTwoAmalgam.{u}} {Y : Type} [Group Y] (c : α.Completion Y)
    (x : α.G12) : f1 (c := c) (α.α1 x) = f2 (c := c) (α.α2 x) :=
  Subtype.ext ((c.comm1 x).trans (c.comm2 x).symm)

variable {S : LieSetting.{u, 0}} {Y : Type} [Group Y] [Finite Y]

@[expose] noncomputable def vEq (hS : S.Facts45L) (β : S.α.Completion Y) (hβ : β.IsFaithful)
    (hs : β.IsSmall S.m) : Vs β (decide (Odd S.m)) ≃ Vs S.ι (decide (Odd S.m)) :=
  vEquiv β S.ι hβ S.hι _ (hS.facts46 β hβ) (hS.facts46 S.ι S.hι)
    (fun _ hz => dist_lv_le_sType β ((hS.facts46 β hβ).diam_le hs) hz)
    (fun _ hz => dist_lv_le_sType S.ι hS.poly.diam_le hz)

variable (hS : S.Facts45L) (β : S.α.Completion Y) (hβ : β.IsFaithful) (hs : β.IsSmall S.m)

theorem vEq_f2 (a : S.α.G2) (z : Vs β (decide (Odd S.m))) :
    vEq hS β hβ hs (f2 (c := β) a • z) = f2 (c := S.ι) a • vEq hS β hβ hs z :=
  vEquiv_f2 β S.ι hβ S.hι _ _ _ _ _ a z

theorem vEq_B1 {a : S.α.G1} (ha : a ∈ S.α.α1.range) (z : Vs β (decide (Odd S.m))) :
    vEq hS β hβ hs (f1 (c := β) a • z) = f1 (c := S.ι) a • vEq hS β hβ hs z := by
  obtain ⟨x, rfl⟩ := ha
  rw [f1_eq_f2 β x, f1_eq_f2 S.ι x]
  exact vEq_f2 hS β hβ hs _ z

theorem vEq_f1_near (a : S.α.G1) (z : Vs β (decide (Odd S.m))) (hz : NearV S.m β z.1) :
    vEq hS β hβ hs (f1 (c := β) a • z) = f1 (c := S.ι) a • vEq hS β hβ hs z :=
  vEquiv_f1 β S.ι hβ S.hι _ _ _ _ _ (by have := S.hm; omega) a z hz

theorem vEq_near (z : Vs β (decide (Odd S.m))) :
    NearV S.m S.ι (vEq hS β hβ hs z).1 ↔ NearV S.m β z.1 :=
  vEquiv_near β S.ι hβ S.hι _ _ _ _ _ (by have := S.hm; omega) z

include hS hβ hs in
theorem far_iff_not_near (z : Vs β (decide (Odd S.m))) :
    β.graph.dist β.xv z.1 = S.m ↔ ¬ NearV S.m β z.1 :=
  (not_near_iff β (by have := S.hm; omega) ((hS.facts46 β hβ).diam_le hs) z.2).symm

include hS in
theorem far_iff_not_near_iota (z : Vs S.ι (decide (Odd S.m))) :
    S.ι.graph.dist S.ι.xv z.1 = S.m ↔ ¬ NearV S.m S.ι z.1 :=
  (not_near_iff S.ι (by have := S.hm; omega) hS.poly.diam_le z.2).symm

theorem vEq_far_iff (z : Vs β (decide (Odd S.m))) :
    S.ι.graph.dist S.ι.xv (vEq hS β hβ hs z).1 = S.m ↔ β.graph.dist β.xv z.1 = S.m := by
  rw [far_iff_not_near hS β hβ hs, far_iff_not_near_iota hS, not_congr (vEq_near hS β hβ hs z)]

end CFSG.Quasithin.H13.F48Rig

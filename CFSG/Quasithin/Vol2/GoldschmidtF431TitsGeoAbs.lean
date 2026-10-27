module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoBridgeL
public import CFSG.Quasithin.Recognition.F4Main
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoFacts46

public section

namespace CFSG.Quasithin.TitsGeo

open CFSG.Open CFSG.Quasithin.F7 CFSG.Quasithin.RankTwoAmalgam.Completion

universe u w w'

variable {α : RankTwoAmalgam.{u}} {Y : Type w} [Group Y] {Yb : Type w'} [Group Yb]

structure TitsModel (ι : α.Completion Yb) (k : ℕ) : Prop where
  faithful : ι.IsFaithful
  thick1 : 2 ≤ α.qOne
  thick2 : 2 ≤ α.qTwo
  hk : 1 ≤ k
  even : Even k
  transX : ι.PathTrans ι.xv (k + 2)
  transL : ι.PathTrans ι.lv (k + 1)
  noFixX : NoFixEnd ι (k + 2) ι.xv
  pairX : TransPair ι (k + 2) ι.xv
  pairL : TransPair ι (k + 2) ι.lv

namespace TitsModel

variable {ι : α.Completion Yb} {k : ℕ} (M : TitsModel ι k)

include M

theorem titsHyp {c : α.Completion Y} (hc : c.IsFaithful) : TitsHyp c k where
  faithful := hc
  thick1 := M.thick1
  thick2 := M.thick2
  hk := M.hk
  even := M.even
  transPt a ha := by
    obtain ⟨g, hg⟩ := exists_smul_eq_baseVert c a
    rw [ha] at hg
    rw [← hg]
    exact (pathTrans_xv_transfer c hc ι M.faithful _ M.transX).smul g
  transLn a ha := by
    obtain ⟨g, hg⟩ := exists_smul_eq_baseVert c a
    rw [ha] at hg
    rw [← hg]
    exact (pathTrans_lv_transfer c hc ι M.faithful _ M.transL).smul g
  noFix a ha := by
    obtain ⟨g, hg⟩ := exists_smul_eq_baseVert c a
    rw [ha] at hg
    rw [← hg]
    exact noFixEnd_smul (noFixEnd_transfer_x hc M.faithful (by omega) M.noFixX) g
  pair a := by
    obtain ⟨g, hg⟩ := exists_smul_eq_baseVert c a
    rw [← hg]
    cases hv : CosetGeom.vtype a
    · exact transPair_smul (transPair_transfer_x hc M.faithful (by omega) M.pairX) g
    · exact transPair_smul (transPair_transfer_l hc M.faithful (by omega) M.pairL) g

theorem facts46 [Finite Y] {c : α.Completion Y} (hc : c.IsFaithful) : c.Facts46 (k + 2) :=
  (M.titsHyp hc).facts46

end TitsModel

end CFSG.Quasithin.TitsGeo

namespace CFSG.Quasithin.LieSetting

open CFSG.Quasithin.TitsGeo

universe u w w'

theorem lemma_F424_titsModel (S : LieSetting.{u, w}) {k : ℕ} (hm : S.m = k + 2)
    (M : TitsModel S.ι k) (hpoly : IsGenPolygon S.ι.graph S.m)
    {Y : Type w'} [Group Y] [Finite Y] (β : S.α.Completion Y) (hβ : β.IsFaithful)
    (hle : Nat.card Y ≤ Nat.card S.Yb) (h48 : β.IsSmall S.m → S.F48Concl β) :
    Nat.card Y = Nat.card S.Yb ∧
      ∃ (Ġ : Type w') (_ : Group Ġ), S.IsExtension Ġ ∧ Nonempty (Y ≃* Ġ) := by
  have hev : Even S.m := by
    rw [hm]
    exact M.even.add (by decide)
  have Fι : S.ι.Facts46 S.m := by
    rw [hm]
    exact M.facts46 S.hι
  have Fβ : β.Facts46 S.m := by
    rw [hm]
    exact M.facts46 hβ
  exact lemma_F424_even hev hpoly Fι β Fβ hle h48

end CFSG.Quasithin.LieSetting

module

public import CFSG.RankThree.GF2n.Tim81.Cited.Sec6
public import CFSG.Timmesfeld.Bridge.OddRootNoSz
import CFSG.Timmesfeld.Bridge.OddRootPair
import CFSG.Timmesfeld.Bridge.OddRootL2Assembly
import CFSG.Timmesfeld.Bridge.OddRootSzMainFinal
import CFSG.RankThree.GF2n.Tim81.Sec2.SL2Sec5
public import CFSG.RankThree.GF2n.Tim77Prop24TwoL2

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG.Timmesfeld CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld.Bridge.OddRoot

theorem oddTranspRootL2_of
    (hM : SzMainStmt) : OddTranspRootL2 := by
  intro K _ _ D hS hO _ hsq hconn d hd x hx hdx
  let h : CFSG.Timmesfeld.Bridge.OddRoot.Hyp K D :=
    { setup := hS, o2 := hO, sq := hsq, conn := hconn }
  have hall : ∀ d ∈ D, ∀ x ∈ D, ¬ Commute d x → PSL2Pair D d x := by
    intro d hd x hx hdx
    exact psl2Pair_of_not_sqOut h hd hx hdx
      (noSzBelow_of hM (Nat.card K + 1) K D (Nat.lt_succ_self _) h d hd x hx hdx)
  obtain ⟨n, hn, hcard, φ, hφd, hφx⟩ := exists_SL2_of_allPSL2 h hall hd hx hdx
  have hn0 : n ≠ 0 := by omega
  refine ⟨GaloisField 2 n, inferInstance, inferInstance, inferInstance, φ, ?_, ?_, ?_⟩
  · change Nat.card (GaloisField 2 n) = Nat.card (rootGroup D d)
    rw [GaloisField.card 2 n hn0]
    exact hcard.symm
  · change ((rootGroup D d).subgroupOf (rootGroup D d ⊔ rootGroup D x)).map φ.toMonoidHom
      = utri (GaloisField 2 n)
    rw [hφd, CFSG.RankThree.GF2n.Tim77.utri_eq_upperUnipotent]
  · change ((rootGroup D x).subgroupOf (rootGroup D d ⊔ rootGroup D x)).map φ.toMonoidHom
      = ltri (GaloisField 2 n)
    rw [hφx, CFSG.RankThree.GF2n.Tim81.Sec2.ltri_eq_lowerUnipotent]

theorem oddTranspRootL2 :
    OddTranspRootL2 :=
  oddTranspRootL2_of szMainStmt

end CFSG.RankThree.GF2n.Tim81

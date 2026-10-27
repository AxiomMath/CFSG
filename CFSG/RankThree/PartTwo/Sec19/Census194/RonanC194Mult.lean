module

public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194

open CFSG.RankThree.PerfectCover

theorem card_center_dvd_hopf {Y X : Type} [Group Y] [Finite Y] [Group X]
    (hY : CFSG.IsQuasisimple Y) (e : Y ⧸ Subgroup.center Y ≃* X) :
    Nat.card (Subgroup.center Y) ∣ Nat.card (CFSG.Open.griessHopfMultiplier X) := by
  let q := centralQuotientMap e
  have hq : Function.Surjective q := centralQuotientMap_surjective e
  have hk : q.ker = Subgroup.center Y := centralQuotientMap_ker e
  have hkc : q.ker ≤ Subgroup.center Y := hk.le
  have : Group.IsPerfect Y := hY.1
  have : Finite X := finite_of_surjective_monoidHom q hq
  have : Group.IsPerfect X := isPerfect_of_quasisimple_quotient hY e
  have : Finite (hopfMultiplier X) := finite_hopfMultiplier (inferInstance : Group.IsPerfect X)
  let ψ : CFSG.Open.griessHopfMultiplier X →* q.ker :=
    (hopfMultiplierToKer q hq hkc).comp (hopfMultiplierEquivGriess X).toMonoidHom
  have hψ : Function.Surjective ψ :=
    (hopfMultiplierToKer_surjective q hq hkc).comp (hopfMultiplierEquivGriess X).surjective
  have h := Subgroup.card_dvd_of_surjective (f := ψ) hψ
  rwa [hk] at h

theorem card_center_dvd_of_row {Y X G : Type} [Group Y] [Finite Y] [Group X] [Group G]
    (hY : CFSG.IsQuasisimple Y) (e : Y ⧸ Subgroup.center Y ≃* X)
    (hrow : Nonempty (CFSG.Open.griessHopfMultiplier X ≃* G)) {a : ℕ}
    (hG : Nat.card G = a) : Nat.card (Subgroup.center Y) ∣ a := by
  obtain ⟨ε⟩ := hrow
  have h := card_center_dvd_hopf hY e
  rwa [Nat.card_congr ε.toEquiv, hG] at h

end CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194

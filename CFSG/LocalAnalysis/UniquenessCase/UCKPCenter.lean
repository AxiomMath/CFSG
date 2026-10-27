module

public import CFSG.LocalAnalysis.UniquenessCase.UCKU3
public import CFSG.Open.GriessAllModelsStatement
import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup

theorem card_griessHopfMultiplier_psu3 (hG : CFSG.Open.GriessAllModelsStatement)
    {Y : Type} [Group Y] {n : ℕ} (hY : CFSG.Blueprint.LieModel Y .PSU 3 2 n) :
    Nat.card (griessHopfMultiplier Y) = Nat.gcd 3 (2 ^ n + 1) := by
  have hcl : CFSG.Open.StatedClassicalModel Y .PSU 3 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel hY (by decide)
  have hmodel : CFSG.Models.LieModel Y .PSU 3 2 n := ⟨hcl.1, Or.inl hcl⟩
  obtain ⟨-, ⟨g⟩⟩ := hG Y .PSU 3 2 n hmodel
  rw [Nat.card_congr g.toEquiv, Nat.card_prod]
  unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
  simp only [Nat.card_prod, Nat.card_zmod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _)]
  simp [CFSG.Blueprint.Multiplier.genericOrders, CFSG.Blueprint.Multiplier.exceptionalOrders]

theorem u3Center_of_griess (hG : CFSG.Open.GriessAllModelsStatement) : U3Center := by
  intro X _ _ n hX
  obtain ⟨hq, hU⟩ := hX
  haveI : Group.IsPerfect X := Group.isPerfect_def.2 hq.1
  let e : (X ⧸ center X) ≃* (X ⧸ center X) := MulEquiv.refl _
  let q := CFSG.RankThree.PerfectCover.centralQuotientMap e
  have hqs : Function.Surjective q := CFSG.RankThree.PerfectCover.centralQuotientMap_surjective e
  have hk : q.ker = center X := CFSG.RankThree.PerfectCover.centralQuotientMap_ker e
  let ψ : griessHopfMultiplier (X ⧸ center X) →* q.ker :=
    (CFSG.RankThree.PerfectCover.hopfMultiplierToKer q hqs hk.le).comp
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess (X ⧸ center X)).toMonoidHom
  have hψ : Function.Surjective ψ :=
    (CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective q hqs hk.le).comp
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess (X ⧸ center X)).surjective
  have hdvd : Nat.card q.ker ∣ Nat.card (griessHopfMultiplier (X ⧸ center X)) :=
    Subgroup.card_dvd_of_surjective hψ
  rw [hk, card_griessHopfMultiplier_psu3 hG hU] at hdvd
  exact hdvd.trans (Nat.gcd_dvd_left 3 (2 ^ n + 1))

end CFSG.LocalAnalysis.UniquenessCase.UCK

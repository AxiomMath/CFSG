module

public import CFSG.LocalAnalysis.StandardType.GGSporKBSevenOrd
public import CFSG.LocalAnalysis.StandardType.GGSporKLamOrders
public import CFSG.LocalAnalysis.StandardType.GGSporKOrdersB
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Defs
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Rows

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open

theorem bSevenOrd_of_rows
    {K : Type} [Group K] [Finite K] (N : ℕ) (hK : Nat.card K ∣ N)
    (hrows : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → labOrd lab ∣ N → Ord7Row lab) :
    BSevenOrd K := by
  intro L hLs hmark
  obtain ⟨lab, hlab, hmodel, hcard⟩ := largeEvenMarking_card_labOrd hmark
  have hc : Subgroup.center ↥L = ⊥ := by
    rcases hLs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h | h
    · exact h
    · exfalso
      have hbot : commutator ↥L = ⊥ := by
        rw [commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro g _
        exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top x)) g
      have htop : commutator ↥L = ⊤ := hmark.1
      haveI := hLs.toNontrivial
      rw [hbot] at htop
      exact bot_ne_top htop
  have e : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have hmodelL : MarkedModel lab ↥L := MarkedModel.of_mulEquiv e hmodel
  have hcardL : Nat.card ↥L = labOrd lab := by rw [← hcard]; exact (Nat.card_congr e.toEquiv).symm
  have hdvd : labOrd lab ∣ N := by
    rw [← hcardL]
    exact (Subgroup.card_subgroup_dvd_card L).trans hK
  exact hrows lab hlab hdvd ↥L hLs hmodelL

theorem bSevenOrd_B [Finite (TauCeti.CFSGIndex.sporadic .B).Group] :
    BSevenOrd (TauCeti.CFSGIndex.sporadic .B).Group :=
  bSevenOrd_of_rows 4154781481226426191177580544000000 (by rw [ggSporK_card_sporadicB]) fun _ hlab hd => ord7Row_of_dvd hlab hd

end CFSG.StandardType.SporadicShape

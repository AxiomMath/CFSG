module

public import CFSG.RankThree.PartOne.F106.ConvTwoAdic
public import CFSG.RankThree.PartOne.F106.ConvOddFamilies
public import CFSG.RankThree.PartOne.N143.Inspect613Even
public import CFSG.ClassicalInvolution.Orders.Classical
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
public import CFSG.Adapters.TauCetiExceptional.B1Exceptional

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.N143 CFSG.RankThree.PartOne.S12K
open CFSG.RankThree.PartOne.Census3 (ThmThreeItem1 ThmThreeItem2 ThmThreeItem4)

open TauCeti (PrimePower)


theorem odd_three_le_card (q : PrimePower) (hq2 : q.p ≠ 2) :
    Odd (q.p ^ q.exponent) ∧ 3 ≤ q.p ^ q.exponent := by
  have hp := q.prime_p
  have hodd : Odd q.p := hp.odd_of_ne_two hq2
  refine ⟨hodd.pow, ?_⟩
  have h3 : 3 ≤ q.p := by
    have := hp.two_le
    have : q.p ≠ 2 := hq2
    omega
  exact h3.trans (Nat.le_self_pow q.exponent_pos.ne' q.p)

section Certs


theorem false_of_odd_item {X : Type} [Group X] {N : ℕ} (hN : 20 ≤ N)
    (hdvd : 2 ^ N ∣ Nat.card X) (hsize : Nat.card X ^ 4 ≤ (2 ^ N) ^ 11)
    (h : ThmThreeItem1 X ∨ ThmThreeItem2 X ∨ ThmThreeItem4 X) : False := by
  rcases h with ⟨q, hq2, -, hv, ⟨e⟩⟩ | ⟨q, hq2, -, h2⟩ | ⟨q, hq2, -, h4⟩
  · obtain ⟨hodd, h3⟩ := odd_three_le_card q hq2
    have hm := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    have hc := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hq2 hm).1 rfl
    rw [hc] at hdvd hsize
    exact false_ordA_one hodd h3 hN hdvd hsize
  · obtain ⟨hodd, h3⟩ := odd_three_le_card q hq2
    rcases h2 with ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩
    · have hm := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      have hc := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hq2 hm).1 rfl
      rw [hc] at hdvd hsize
      exact false_ordA_two hodd h3 hN hdvd hsize
    · have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      have hc := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hq2 hm).2.1 rfl
      rw [hc] at hdvd hsize
      exact false_ordTwistedA_two hodd h3 hN hdvd hsize
  · obtain ⟨hodd, h3⟩ := odd_three_le_card q hq2
    rcases h4 with ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩ | ⟨hv, ⟨e⟩⟩
    · have hm := CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.untwistedBridge_G2 q hv hq2 e
      have hc := CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_G2 hm
      rw [hc] at hdvd hsize
      exact false_ordG2 hodd h3 hN hdvd hsize
    · have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
      have hc := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hq2 hm).2.2.1 rfl
      rw [hc] at hdvd hsize
      exact false_ordBC_two hodd h3 hN hdvd hsize
    · have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
      have hc := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hq2 hm).2.1 rfl
      rw [hc] at hdvd hsize
      exact false_ordTwistedA_three hodd h3 hN hdvd hsize
    · have hm := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      have hc := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hq2 hm).1 rfl
      rw [hc] at hdvd hsize
      exact false_ordA_three hodd h3 hN hdvd hsize

theorem smallEvenParams_of_odd_item {X : Type} [Group X] {t : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible t n 2 f) (hcard : Nat.card X = charTwoOrder t n f)
    (h : ThmThreeItem1 X ∨ ThmThreeItem2 X ∨ ThmThreeItem4 X) : SmallEvenParams t n f := by
  by_contra hns
  obtain ⟨N, r, -, hc, h20, hb, -⟩ := twoAdic_of_nonSmall hadm hns
  rw [← hcard] at hc hb
  exact false_of_odd_item h20 (hc ▸ Dvd.intro r rfl) hb h

end Certs

end CFSG.RankThree.PartOne.F106

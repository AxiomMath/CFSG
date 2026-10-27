module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148CRowTools
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148C

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance (OPrimeCoreTrivialAt
  OPrimeCoreTrivialAt.of_mulEquiv)

theorem rowSOf148_spor_of_oPrime {s : TauCeti.SporadicName}
    (hb : Nonempty (Blueprint.NativeSporadic.Carrier s ≃* Spor s))
    (hout : Finite (Blueprint.NativeSporadic.Carrier s) →
      ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier s)))
    (h : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier s) → OPrimeCoreTrivialAt 3 S) :
    RowSOf148 (Spor s) :=
  rowSOf148_spor hb fun S _ _ hs hna ⟨e⟩ =>
    rowS148_of_pPrimeCore_eq_bot (RonanK429H.center_eq_bot_of_simple_nonab hna)
      (RonanK429H.not_three_dvd_outer_of_mulEquiv e (hout (Finite.of_equiv S e.toEquiv)))
      (h S hs ⟨e⟩)

theorem rowSOf148_j3 :
    RowSOf148 (Spor .J3) :=
  rowSOf148_spor_of_oPrime CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
    (fun hfin => by
      haveI := hfin
      exact RonanK429H.not_three_dvd_outer_of_le_two card_outer_J3)
    fun S _ _ _ ⟨e⟩ => by
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
      exact CFSG.HardMathSupport.Timmesfeld.SporadicBalance.oPrimeCoreTrivialAt_J3 S ⟨e.trans b⟩

theorem rowSOf148_mcl :
    RowSOf148 (Spor .McL) :=
  rowSOf148_spor_of_oPrime CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
    (fun hfin => by
      haveI := hfin
      exact RonanK429H.not_three_dvd_outer_of_le_two card_outer_McL)
    fun _ _ _ _ ⟨e⟩ => OPrimeCoreTrivialAt.of_mulEquiv e
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.oPrimeCoreTrivialAt_McL

theorem rowSOf148_on :
    RowSOf148 (Spor .ONan) :=
  rowSOf148_spor_of_oPrime CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv (fun _ => inputs47Core_outON)
    fun S _ _ hs he => by
      haveI := hs
      exact CFSG.HardMathSupport.Timmesfeld.SporadicBalance.sporadicOPrimeHolds_ONan_three S he

theorem rowSOf148_suz :
    RowSOf148 (Spor .Suz) :=
  rowSOf148_spor_of_oPrime CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
    (fun _ => by
      rw [CFSG.Sporadic.SuzOddCore.outer_carrier_suz.1]
      norm_num)
    fun _ _ _ _ ⟨e⟩ => OPrimeCoreTrivialAt.of_mulEquiv (e.trans CFSG.Sporadic.SuzOddCore.suzEquivM)
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.oPrimeCoreTrivialAt_suzM

theorem rowSOf148_co3 :
    RowSOf148 (Spor .Co3) :=
  rowSOf148_spor_of_oPrime CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv
    (fun _ => by
      rw [show Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Co3)) = 1 from
        CFSG.RankThree.PartOne.CTUC_Co3_all_automorphisms_inner.{0}.2.2.2.1]
      norm_num)
    fun _ _ _ _ ⟨e⟩ => OPrimeCoreTrivialAt.of_mulEquiv
      (e.trans CFSG.Sporadic.Schreier.Co3.co3PermEquiv)
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T.oPrimeCoreTrivialAt_co3P

theorem rowSOf148_hn :
    RowSOf148 (Spor .HN) :=
  rowSOf148_spor_of_oPrime CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
    (fun _ => by
      rw [CFSG.RankThree.PartOne.SPOR.card_outer_HN]
      norm_num)
    fun S _ _ hs he => by
      haveI := hs
      exact CFSG.HardMathSupport.Timmesfeld.SporadicBalance.sporadicOPrimeHolds_HN_three_of_witness
        CFSG.HardMathSupport.Timmesfeld.SporadicBalance.hnThreeWitness_of_certificate S he

theorem rowSOf148_th :
    RowSOf148 (Spor .Th) :=
  rowSOf148_spor_of_oPrime CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
    (fun _ => by
      rw [show Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Th)) = 1 from
        CFSG.RankThree.PartOne.SPOR.card_outer_Th_native]
      norm_num)
    fun S _ _ hs he => by
      haveI := hs
      exact CFSG.HardMathSupport.Timmesfeld.SporadicBalance.sporadicOPrimeHolds_Th_three_of_residual
        CFSG.HardMathSupport.Timmesfeld.SporadicBalance.thThreeResidual_holds S he

end CFSG.RankThree.PartTwo.Sec4.Ronan148C

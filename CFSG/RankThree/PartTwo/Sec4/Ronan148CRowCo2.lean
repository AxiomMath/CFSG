module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148CRowTools
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo2Cent
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo2U42

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148C

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 RonanK429H
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

open CFSG.GH74.GLS (pPrimeCoreOf)

open Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co2Cert
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T
  CFSG.HardMathSupport.Dickson.I271.Co2Cent CFSG.HardMathSupport.Dickson.I271.U42Presentation
  CFSG.HardMathSupport.Dickson.I271

section Certs


theorem pPrimeCoreOf_co2 (x : Equiv.Perm (Fin 2300)) (hx : x ∈ co2P) (hxo : orderOf x = 3) :
    pPrimeCoreOf 3 (centralizer ({x} : Set (Equiv.Perm (Fin 2300))) ⊓ co2P) = ⊥ := by
  obtain ⟨k, hk, c, hc, e, he, rfl⟩ := co2_exists_conj_classes hx hxo
  rcases hc with rfl | rfl
  · obtain ⟨h3, -, -, hcard, hle, hnorm, hcent⟩ := co2CaseA_spec
    exact pPrimeCoreOf_centralizer_conj hk h3 he (pPrimeCoreOf_eq_bot_of_selfCentralizing hle hnorm
      (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)) hcent)
  · obtain ⟨h3, -, -, hcard, hLC, hLn, hcent, hrels⟩ := co2CaseB_spec
    obtain ⟨eL⟩ := nonempty_mulEquiv_QP45_of_rels uvGen hrels hcard
    haveI : IsSimpleGroup Lsub := isSimpleGroup_of_equiv_QP45 eL
    exact pPrimeCoreOf_centralizer_conj hk h3 he
      (pPrimeCoreOf_eq_bot_of_simpleNormal hLC hLn (by rw [hcard]; norm_num) hcent)


theorem rowS148_co2 :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .Co2) → RowS148 S := by
  intro S _ _ _ hna ⟨e⟩
  have hout : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Co2)) := by
    rw [RankThree.PartOne.SPOR.card_outer_Co2]
    norm_num
  exact rowS148_of_subgroupModel (e.trans co2PermEquiv) (RonanK429H.center_eq_bot_of_simple_nonab hna)
    (not_three_dvd_outer_of_mulEquiv e hout) pPrimeCoreOf_co2

theorem rowSOf148_co2 :
    RowSOf148 (Spor .Co2) :=
  rowSOf148_spor CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv rowS148_co2

end Certs

end CFSG.RankThree.PartTwo.Sec4.Ronan148C

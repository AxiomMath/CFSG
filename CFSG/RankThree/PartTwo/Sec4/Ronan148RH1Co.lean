module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Crit
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Co3Shape
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo2Cent
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo2U42

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open Subgroup

section Co2

open CFSG.Sporadic.Co2Cert CFSG.HardMathSupport.Dickson.I271


theorem good427_co2 (x : Equiv.Perm (Fin 2300)) (hx : x ∈ co2P) (hxo : orderOf x = 3) :
    Good427 (centralizer ({x} : Set (Equiv.Perm (Fin 2300))) ⊓ co2P) := by
  obtain ⟨k, hk, c, hc, e, he, rfl⟩ := co2_exists_conj_classes hx hxo
  rcases hc with rfl | rfl
  · obtain ⟨h3, -, -, hcard, hle, hnorm, hcent⟩ := co2CaseA_spec
    exact Good427.conj hk h3 he (good427_of_selfCentralizing' hle hnorm
      (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)) hcent)
  · obtain ⟨h3, -, -, hcard, hLC, hLn, hcent, hrels⟩ := co2CaseB_spec
    obtain ⟨eL⟩ := nonempty_mulEquiv_QP45_of_rels uvGen hrels hcard
    haveI : IsSimpleGroup Lsub := isSimpleGroup_of_equiv_QP45 eL
    exact Good427.conj hk h3 he (good427_of_simpleNormal' hLC hLn
      (nonabelian_of_equiv_QP45 eL) (by rw [hcard]; norm_num) hcent)


theorem noCfgS427_co2 :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .Co2) → NoCfgS427 S ∧ NoONS427 S := by
  intro S _ _ _ hna ⟨e⟩
  have hout : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Co2)) := by
    rw [RankThree.PartOne.SPOR.card_outer_Co2]
    norm_num
  refine ⟨noCfgS427_of_subgroupModel (e.trans co2PermEquiv) (RonanK429H.center_eq_bot_of_simple_nonab hna)
    (not_three_dvd_outer_of_mulEquiv e hout) good427_co2, noONS427_of_card ?_⟩
  rw [Nat.card_congr e.toEquiv]
  show ¬ (19 * 31 * 343) ∣ Nat.card Blueprint.NativeSporadic.Co2
  rw [CFSG.Sporadic.Co2.card_Co2]
  norm_num

end Co2

section Co3

open CFSG.Sporadic.Schreier.Co3 CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T CFSG.RankThree.PartOne


theorem good427_co3 (x : Equiv.Perm (Fin 276)) (hx : x ∈ co3P) (hxo : orderOf x = 3) :
    Good427 (centralizer ({x} : Set (Equiv.Perm (Fin 276))) ⊓ co3P) := by
  obtain ⟨k, hk, c, hc, e, he, rfl⟩ := exists_conj_classes hx hxo
  rcases hc with rfl | rfl | rfl
  · obtain ⟨h3, -, -, hcard, hle, hnorm, hcent⟩ := caseA_spec
    exact Good427.conj hk h3 he (good427_of_selfCentralizing' hle hnorm
      (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)) hcent)
  · obtain ⟨h3, -, -, hcard, hle, hnorm, hcent⟩ := caseB_spec
    exact Good427.conj hk h3 he (good427_of_selfCentralizing' hle hnorm
      (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)) hcent)
  · obtain ⟨⟨hCeq, hcard⟩, -⟩ := caseC_spec
    refine Good427.conj hk yPerm_pow he (good427_of_not_five_dvd ?_)
    rw [← hCeq, hcard]
    norm_num


theorem noCfgS427_co3 :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .Co3) → NoCfgS427 S ∧ NoONS427 S := by
  intro S _ _ _ hna ⟨e⟩
  have hout : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Co3)) := by
    rw [show Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Co3)) = 1 from
      CTUC_Co3_all_automorphisms_inner.{0}.2.2.2.1]
    norm_num
  refine ⟨noCfgS427_of_subgroupModel (e.trans co3PermEquiv) (RonanK429H.center_eq_bot_of_simple_nonab hna)
    (not_three_dvd_outer_of_mulEquiv e hout) good427_co3, noONS427_of_card ?_⟩
  rw [Nat.card_congr e.toEquiv]
  show ¬ (19 * 31 * 343) ∣ Nat.card Blueprint.NativeSporadic.Co3
  rw [CFSG.Sporadic.Co3.card_Co3]
  norm_num

end Co3

section Rows



section Co2Row


theorem rowOf427_co2
    : RowOf427 (Spor .Co2) :=
  rowOf427_spor (s := .Co2) CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv noCfgS427_co2

end Co2Row

section Co3Row


theorem rowOf427_co3
    : RowOf427 (Spor .Co3) :=
  rowOf427_spor (s := .Co3) CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv noCfgS427_co3

end Co3Row

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end

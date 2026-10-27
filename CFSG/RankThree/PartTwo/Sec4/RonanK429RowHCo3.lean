module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp2
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Co3Shape

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

open Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.Sporadic.Schreier.Co3
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T
  CFSG.HardMathSupport.Dickson.I271.Co3Cent CFSG.HardMathSupport.Dickson.I271

section Certs


theorem good429_co3 (x : Equiv.Perm (Fin 276)) (hx : x ∈ co3P) (hxo : orderOf x = 3) :
    Good429 (centralizer ({x} : Set (Equiv.Perm (Fin 276))) ⊓ co3P) := by
  obtain ⟨k, hk, c, hc, e, he, rfl⟩ := exists_conj_classes hx hxo
  rcases hc with rfl | rfl | rfl
  · obtain ⟨h3, -, -, hcard, hle, hnorm, hcent⟩ := caseA_spec
    exact Good429.conj hk h3 he (good429_of_selfCentralizing' hle hnorm
      (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)) hcent)
  · obtain ⟨h3, -, -, hcard, hle, hnorm, hcent⟩ := caseB_spec
    exact Good429.conj hk h3 he (good429_of_selfCentralizing' hle hnorm
      (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)) hcent)
  · obtain ⟨⟨hCeq, hcard⟩, -⟩ := caseC_spec
    refine Good429.conj hk yPerm_pow he (good429_of_card (M := 4536) (B := 17) ?_ (by norm_num) (by decide))
    rw [← hCeq]
    exact hcard


theorem noCfgS429_co3 :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .Co3) → NoCfgS429 S := by
  intro S _ _ _ hna ⟨e⟩
  have hout : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Co3)) := by
    rw [show Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Co3)) = 1 from
      CTUC_Co3_all_automorphisms_inner.{0}.2.2.2.1]
    norm_num
  exact noCfgS429_of_subgroupModel (e.trans co3PermEquiv) (center_eq_bot_of_simple_nonab hna)
    (not_three_dvd_outer_of_mulEquiv e hout) good429_co3

theorem rowSOf429_co3 :
    RowSOf429 (Spor .Co3) :=
  rowSOf429_spor CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv noCfgS429_co3

end Certs

end CFSG.RankThree.PartTwo.Sec4.RonanK429H

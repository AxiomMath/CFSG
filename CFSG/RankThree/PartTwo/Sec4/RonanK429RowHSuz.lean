module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp2
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzB

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Monster.B.Fischer
  CFSG.Monster.B.Mathieu CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
  CFSG.HardMathSupport.Dickson.I271
open CFSG.Sporadic.SuzOddCore (suzM suzEquivM)


section Certs


theorem good429_suz_A :
    Good429 (centralizer ({fuseXA} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) := by
  rw [← aSub_eq]
  obtain ⟨hq, hZ, -⟩ := aSub_quasisimple
  have hZ3 : IsPGroup 3 (Subgroup.center ↥aSub) := by
    rw [hZ]
    have hord : orderOf (⟨fuseXA, aX_mem⟩ : ↥aSub) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime fuseXA_pow fuseXA_ne_one
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord, pow_one]
  exact good429_of_isQuasisimple (B := 214) (isQuasisimple_of_open hq) hZ3
    (by rw [card_aSub]; norm_num) (by rw [card_aSub]; decide)

theorem good429_suz (x : Equiv.Perm (Fin 1782)) (hx : x ∈ suzM) (hxo : orderOf x = 3) :
    Good429 (centralizer ({x} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) := by
  obtain ⟨k, hk, c, hc, e, he, rfl⟩ := suz_exists_conj_classes hx hxo
  rcases hc with rfl | rfl | rfl
  · exact Good429.conj hk fuseXA_pow he good429_suz_A
  · obtain ⟨hcard, -, hle, hnorm, hcent⟩ := TabSuzB.caseB_spec
    exact Good429.conj hk fuseXB_pow he (good429_of_selfCentralizing' hle hnorm
      (IsPGroup.of_card (n := 6) (by rw [hcard]; norm_num)) hcent)
  · obtain ⟨hCeq, hcard⟩ := Cy_eq
    refine Good429.conj hk yPerm_pow he
      (good429_of_card (M := 3240) (B := 15) ?_ (by norm_num) (by decide))
    rw [← hCeq]
    exact hcard


theorem noCfgS429_suz :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .Suz) → NoCfgS429 S := by
  intro S _ _ _ hna ⟨e⟩
  have hout : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Suz)) := by
    rw [CFSG.Sporadic.SuzOddCore.outer_carrier_suz.1]
    norm_num
  exact noCfgS429_of_subgroupModel (e.trans suzEquivM) (center_eq_bot_of_simple_nonab hna)
    (not_three_dvd_outer_of_mulEquiv e hout) good429_suz

theorem rowSOf429_suz :
    RowSOf429 (Spor .Suz) :=
  rowSOf429_spor CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv noCfgS429_suz

end Certs

end CFSG.RankThree.PartTwo.Sec4.RonanK429H

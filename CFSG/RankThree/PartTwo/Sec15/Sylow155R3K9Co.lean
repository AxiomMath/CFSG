module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3K9CritJ2
import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCo2
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Co3
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp
public import CFSG.Sporadic.Co2Cert.Faithful
public import CFSG.Sporadic.Schreier.Co3Faithful

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG.RankThree.PartTwo.Sec4 (Spor)
open CFSG.RankThree.PartTwo.Sec4.RonanK429H
  (center_eq_bot_of_simple_nonab not_three_dvd_outer_of_mulEquiv)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open Subgroup

theorem not_dvd_card_centralizer_of_no_order25 {G : Type*} [Group G] [Finite G] {P : Subgroup G}
    {s : G}
    (h : ∀ E : Subgroup G, E ≤ P → Nat.card E = 25 → (∀ e ∈ E, e * s = s * e) → False) :
    ¬ 25 ∣ Nat.card ↥(centralizer ({s} : Set G) ⊓ P) := by
  intro hd
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set C : Subgroup G := centralizer ({s} : Set G) ⊓ P with hC
  obtain ⟨E, hE⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥C) 5 (n := 2) (by simpa using hd)
  refine h (E.map C.subtype) ?_ ?_ ?_
  · rintro _ ⟨e, -, rfl⟩
    exact (Subgroup.mem_inf.1 e.2).2
  · rw [Subgroup.card_map_of_injective C.subtype_injective, hE]
    norm_num
  · rintro _ ⟨e, -, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 e.2).1

section Co2

open CFSG.Sporadic.Co2Cert (co2P co2PermEquiv)


theorem goodJ2_co2 (x : Equiv.Perm (Fin 2300)) (hx : x ∈ co2P) (hxo : orderOf x = 3) :
    GoodJ2 (centralizer ({x} : Set (Equiv.Perm (Fin 2300))) ⊓ co2P) :=
  goodJ2_of_not_dvd_twentyFive
    (CFSG.HardMathSupport.Solomon.Coordinator.Co2Spor.not_dvd_card_centralizer hx hxo)


theorem noCfgJ2_co2 :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .Co2) → NoCfgJ2 S := by
  intro S _ _ _ hna ⟨e⟩
  have hout : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Co2)) := by
    rw [CFSG.RankThree.PartOne.SPOR.card_outer_Co2]
    norm_num
  exact noCfgJ2_of_subgroupModel (e.trans co2PermEquiv)
    (center_eq_bot_of_simple_nonab hna) (not_three_dvd_outer_of_mulEquiv e hout) goodJ2_co2


theorem rowOfK9_co2 : RowOfK9 (Spor .Co2) :=
  rowOfK9_spor (s := .Co2) CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv noCfgJ2_co2

end Co2

section Co3

open CFSG.Sporadic.Schreier.Co3 (co3P co3PermEquiv)


theorem goodJ2_co3 (x : Equiv.Perm (Fin 276)) (hx : x ∈ co3P) (hxo : orderOf x = 3) :
    GoodJ2 (centralizer ({x} : Set (Equiv.Perm (Fin 276))) ⊓ co3P) :=
  goodJ2_of_not_dvd_twentyFive
    (not_dvd_card_centralizer_of_no_order25 fun E hEP hE hcomm =>
      CFSG.HardMathSupport.Solomon.Coordinator.YS08.Co3Copy.no_order25_centralized hx hxo hEP hE
        hcomm)


theorem noCfgJ2_co3 :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .Co3) → NoCfgJ2 S := by
  intro S _ _ _ hna ⟨e⟩
  have hout : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Co3)) := by
    rw [show Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Co3)) = 1 from
      CFSG.RankThree.PartOne.CTUC_Co3_all_automorphisms_inner.{0}.2.2.2.1]
    norm_num
  exact noCfgJ2_of_subgroupModel (e.trans co3PermEquiv)
    (center_eq_bot_of_simple_nonab hna) (not_three_dvd_outer_of_mulEquiv e hout) goodJ2_co3


theorem rowOfK9_co3 : RowOfK9 (Spor .Co3) :=
  rowOfK9_spor (s := .Co3) CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv noCfgJ2_co3

end Co3

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3

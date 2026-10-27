module

public import CFSG.RankThree.PartTwo.Sec14.Sylow1411X
public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
import CFSG.RankThree.PartTwo.Sec14.Item1413Res7ProofXPt
import CFSG.RankThree.PartTwo.Sec12.Item128Bar
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res5ProofNonsolv

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan143Q

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open scoped commutatorElement

open Proof1413Res5 Proof1413Res7 Sylow1411X in
theorem claim1411NonsolvXPointOutR_of_item143Q
    (h131 : Item131)
    (h142All : Item142AllS14) (h143 : Ronan148Q.Item143QS14) (hbot : Item145BotS14)
    (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) : Claim1411NonsolvXPointOutR := by
  intro G _ _ A c L hR hloc Y hYΔ hY hs h3 hBc hIH S hS T hT hDST hbig hres a haA ha1 haS haT
    hpt hout
  have hSt := hR.toSec14Std
  have hD13 := hSt.toSec13Data
  have hYa := hres a haA ha1 haS haT
  by_cases ha : Subgroup.zpowers a ∈ omegaA A
  ·
    have hAa : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hD13.commute hx haA)
    obtain ⟨La, hLa₀⟩ := Sec12.exists_mem_lA422 h422 h45 hD13.toPartTwoStanding
      hD13.mem_partTwoF hD13.card_eq ha
    have hLa := Sec12.mem_lA_of_mem_lA422 hAa hLa₀
    obtain ⟨hPGL, r, hr, l, hl, hrl⟩ := hout ha La hLa
    have h' : Sec14Std G A a La := Proof1413.sec14Std_at hSt ha hLa
    rcases (h'.chosen136.2 a ha La hLa).1 with ⟨⟨φ⟩⟩ | hL3 | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · exact ((isEmpty_j2_of_transOn h142All hR hloc ha hLa).false φ).elim
    ·
      obtain ⟨p, e, hp, he, hiso⟩ := hL3
      by_cases hp2 : p = 2
      · subst hp2
        have hD := h'.toSec13Data
        obtain ⟨haL, h9, hAa', hQ⟩ :=
          Proof1413Res6.l3_point_facts h131 hD ⟨2, e, hp, he, hiso⟩ hPGL
        obtain ⟨hEe, hE9, htr⟩ := Proof1413Res6.hess_of_l3_point hD haL h9 hAa' hQ
        have hL2 : ∀ V : Subgroup G, IsPGroup 2 V → V ≤ La →
            A ≤ Subgroup.normalizer (V : Set G) →
              V ≤ inSubgroup (aschbacherSolvableCore 3) La :=
          fun V hV2 hVL hAV => le_theta_of_two he hiso hEe hE9 htr hV2 hVL hAV
        obtain ⟨hZq, -⟩ := theta_sup_xA_mem_scriptQ h142All h'
        have hZYq : (inSubgroup (aschbacherSolvableCore 3) La ⊔ xA A) ⊓ Y ∈ scriptQ A (lB A) :=
          mem_scriptQ_of_le hZq inf_le_left (le_normalizer_inf hZq.1.2.2 hY.2)
        have hle : ∀ U ∈ scriptQPiStar A (lB A) Y (piOf 2),
            U ≤ (inSubgroup (aschbacherSolvableCore 3) La ⊔ xA A) ⊓ Y := fun U hU =>
          le_inf (le_theta_sup_xA h142All hbot h' hAa' hL2
            (isPGroup_of_mem_scriptQPi Nat.prime_two hU.prop) (hU.prop.1.2.trans hYa)
            hU.prop.1.1.1.2.2) hU.prop.1.2
        exact isConjIn_of_le_mem_scriptQ h'.isE27 (hbot G A a La h') hZYq inf_le_right hS hT
          (hle S hS) (hle T hT)
      · have hp3 : 3 < p := by
          have h2 := (Fact.out : p.Prime).two_le
          have h3' := Proof1413Res6.ne_three_of_isoLThreePi he hiso
          omega
        exact absurd (hloc a ha) (not_transOn_of_l3 h131 h142All h' hPGL he hp3 hiso)
    · exact (hrl (cent_of_a7 h131 h' φ r hr l hl)).elim
    · exact (hrl (cent_of_m22 h131 h' φ r hr l hl)).elim
    · exact (hrl (cent_of_m12 h131 h' φ r hr l hl)).elim
  ·
    obtain ⟨Q, hQ⟩ := maxInvariantPiSubgroups_nonempty
      (delta A (lB A) (Subgroup.centralizer ({a} : Set G))) A (piCompl 3)
    rcases ((h143 G A c L hSt) a haA ha1 ha Q hQ).2 with heq | ⟨b, d, Lb, hb, hLb, hJ, -⟩
    · exact absurd heq (hpt.resolve_left ha)
    · exact ((isEmpty_j2_of_transOn h142All hR hloc hb hLb).false hJ.some).elim

theorem claim1411NonsolvXR_of_sylow_item143Q
    (h131 : Item131)
    (h142All : Item142AllS14) (h143 : Ronan148Q.Item143QS14) (h146 : Item146S14)
    (hbot : Item145BotS14) (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) : Claim1411NonsolvXR :=
  claim1411NonsolvXR_of_out h131 h142All h146 hbot
    (claim1411NonsolvXPointOutR_of_item143Q h131 h142All h143 hbot h422 h45)

end CFSG.RankThree.PartTwo.Sec14.Ronan143Q

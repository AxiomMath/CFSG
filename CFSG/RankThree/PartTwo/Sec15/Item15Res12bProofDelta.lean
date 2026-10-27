module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res12bProofDefs
public import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofQ
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
public import CFSG.RankThree.PartTwo.Sec15.Item1518Res2ProofDelta
public import CFSG.RankThree.PartTwo.Sec17.RouteForms

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

open Proof15Res11 Proof1518R2

theorem step1523DeltaY4R_of_res12b
    (h142 : Concl142S14)
    (h134 : Item134) (h48 : Sec4.Item4_8) : Step1523DeltaY4R := by
  intro G _ _ A c L h _ hJ Y hY _ d D _ _
  refine sup_eq_delta_of_mem_scriptQ D.mem_x.2.2.1
    (inf_centralizer_mem_scriptQ1523 h (h142 G A c L h.toSec14Std) hY.prop.1.1.2 D.mem_d ?_)
  intro B hB hdB hΩB
  exfalso
  have hD := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  have hd3 : Nat.card (Subgroup.zpowers d) = 3 :=
    Sec13.card_zpowers_of_pow_three (hA.1.2 d D.mem_d) D.ne_d
  have hB9 : Nat.card B = 9 := by
    have h27 := hA.2
    have hB2 := hB.2
    omega
  have hlt : Subgroup.zpowers d < B := lt_of_le_of_ne (Subgroup.zpowers_le.mpr hdB) fun heq => by
    have := congrArg (fun K : Subgroup G => Nat.card K) heq
    simp only [hd3, hB9] at this
    omega
  obtain ⟨b, hbB, hbd⟩ := IsConcreteLE.exists_of_lt hlt
  exact hΩB _ (omega_of_onType h134 h48 h hJ D.mem_d D.ne_d D.central_d D.type_k b (hB.1 hbB) hbd)
    (Subgroup.zpowers_le.mpr hbB)

end CFSG.RankThree.PartTwo.Sec15

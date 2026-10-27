module

public import CFSG.RankThree.PartTwo.Sec21.Item2110Res2ProofNormal
public import CFSG.RankThree.PartTwo.Sec21.Item2113Res3ProofRank
public import CFSG.RankThree.PartTwo.Sec21.Item2113Res3ProofU4KFinal
public import CFSG.RankThree.PartTwo.Sec21.Item218Res2ProofAssembly

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2110Res2Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint
open Subgroup

section Final

theorem item218Final_of_W (h211 : Item211) (h45 : Sec4.Item4_5)
    (hTGHJ : Item2112TwoGroupHJ) (hNF : Item2112NoFusion) : Item218Final := by
  have hch : Item2113Choice := Item2113Res2Proof.item2113Choice_of h211 h45
    (Item2113Res3Proof.item2113ChoiceHJ_of h211 h45) Item2113Res3Proof.kf2113ExcCentral_holds
  have hReal : KF2112HJReal := Item2113Res2Proof.kf2112HJReal_of Sec4.Sporadic.rank3II_4_15
  intro G _ _ A E U c L U₀ b K hpair hL hU₀ hU₀L hpair' hK hb hbc hWc hWb
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hpairs' := mem_lThreeStarPairs_iff.mp hpair'.mem_pair
  have hAe := hpair.mem_S.1.1
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hbA : b ∈ A := hpair.mem_E.2 hpairs'.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hb1 : b ≠ 1 := hpairs'.2.1
  have hcb : c ∉ zpowers b := not_mem_zpowers_symm (hAe.2 b hbA) hc1 hbc
  obtain ⟨d, hdA, hd1, hdcen, t, htL, ht, htd⟩ := hch G A E U c L hpair hL
  obtain ⟨d', hd'A, hd'1, hd'cen, t', ht'K, ht', ht'd⟩ := hch G A E U₀ b K hpair' hK
  have hDL := Item2113Proof.closure_eq_of_normalizer_le h211 hpair hL hdA hd1 hdcen htL ht htd
    hbA hb1 hbc hWb
  have hDK := Item2113Proof.closure_eq_of_normalizer_le h211 hpair' hK hd'A hd'1 hd'cen ht'K ht'
    ht'd hcA hc1 hcb hWc
  have hDD : closure ({c, d} : Set G) = closure ({b, d'} : Set G) := by
    rw [hDL, hDK, Set.pair_comm]
  have hcard : ∀ x : G, x ∈ A → x ≠ 1 → Nat.card (zpowers x) = 3 := fun x hx hx1 => by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [Nat.card_zpowers, orderOf_eq_prime (hAe.2 x hx) hx1]
  rcases hj_or_dData_W h211 h45 hpair hL hdA hd1 hdcen with hJ | ⟨ℓ, ⟨-, hℓA⟩, hD⟩
  ·
    obtain ⟨ℓ, -, hD⟩ := Item2113Res2Proof.exists_dData h211 h45 hReal hpair hL hdA hd1 hdcen
    have hTG' := hTGHJ G A E U c L hpair hL hJ d hdA hd1 hdcen
    obtain ⟨hNF₁, hNF₂⟩ := noFusion_zpowers hNF hpair hL hdA hd1 hdcen hD
    obtain ⟨ℓ', -, hD'⟩ :=
      Item2113Res2Proof.exists_dData h211 h45 hReal hpair' hK hd'A hd'1 hd'cen
    have hℓ'N := Item2113Res2Proof.mem_normalizer_of_inv hD'.ℓc hD'.ℓd
    have hℓ'D : ℓ' ∈ normalizer (closure ({c, d} : Set G) : Set G) := hDD ▸ hℓ'N.1
    have hℓ'c : ℓ' ∈ normalizer ((zpowers c : Subgroup G) : Set G) :=
      Item2113Res2Proof.mem_normalizer_zpowers (hD.conj_mem_of_noFusion
        (fun y hy hyd => hD.conj_mem_of_twoGroup hTG' hy hyd) hNF₁ hNF₂ hℓ'D)
    have hle : zpowers c ≤ closure ({b, d'} : Set G) := by
      rw [hDK, zpowers_le]
      exact subset_closure (Set.mem_insert_of_mem b rfl)
    rcases hD'.eq_of_normalizes hle (hcard c hcA hc1) hℓ'c with h | h
    · exact hcb (h ▸ mem_zpowers c)
    · exact hNF G A E U c L E U₀ b K hpair hL hpair' hK c hcA hc1
        (Item2113Proof.isCentral218_of_zpowers_eq hd'cen h) 1 (by group)
  ·
    have hle : zpowers b ≤ closure ({c, d} : Set G) := by
      rw [hDL, zpowers_le]
      exact subset_closure (Set.mem_insert_of_mem c rfl)
    rcases hD.eq_of_normalizes hle (hcard b hbA hb1) (hWb hℓA) with h | h
    · exact hbc (h ▸ mem_zpowers b)
    · exact hNF G A E U₀ b K E U c L hpair' hK hpair hL b hbA hb1
        (Item2113Proof.isCentral218_of_zpowers_eq hdcen h) 1 (by group)

theorem item218_of_two (h211 : Item211) (h213 : Item213) (h214 : Item214)
    (h215 : Item215) (h217 : Item217) (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (hL3 : Item2115LThree) (h2 : Item2110Two) (hTGHJ : Item2112TwoGroupHJ) (h219 : Item219)
    (h2101 : Item2110One) : Item218 :=
  have hNF := Item2113Res2Proof.item2112NoFusion_of h219 h2101
    (Item2113Res3Proof.item2112Rank_of h211 h45)
  item218_of_normal_final h211 h213 h214 h215 h217 h45 h66 hL3
    (item218Normal_of_two h211 h45 h2 hTGHJ hNF) (item218Final_of_W h211 h45 hTGHJ hNF)

theorem item2115_of_two (h211 : Item211) (h213 : Item213) (h214 : Item214)
    (h215 : Item215) (h217 : Item217) (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (hL3 : Item2115LThree) (hU4S : Item2115U4Signalizer) (h2 : Item2110Two)
    (hTGHJ : Item2112TwoGroupHJ) (h219 : Item219) (h2101 : Item2110One) : Item2115 :=
  item2115_of h211 h213 h214 h215 h217
    (item218_of_two h211 h213 h214 h215 h217 h45 h66 hL3 h2 hTGHJ h219 h2101) h45 h66 hL3
    (Item2113Proof.item2115U4_of h211 (Item2113Res2Proof.item2115U4Ten_of
      (Item2113Res3Proof.item2115U4Fusion_of_item45 h45)
      (Item2113Res3Proof.item2115U4Local_of hU4S)))

end Final

end CFSG.RankThree.PartTwo.Sec21.Item2110Res2Proof

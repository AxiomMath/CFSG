
module

public import CFSG.Sporadic.Schreier.RuLocalFactsBase

public import CFSG.Sporadic.Schreier.RuChainSpec
public import CFSG.Sporadic.Schreier.RuCertData
public import CFSG.Sporadic.Schreier.RuCheckLocal
public import CFSG.Sporadic.Schreier.RuCheckChains
public import CFSG.Sporadic.Schreier.RuReps

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem ruChainC_valid :
    ValidSchreier ruChainC := ruChain_valid ruChainC_check.1

theorem ruChainN_valid :
    ValidSchreier ruChainN := ruChain_valid ruChainN_check.1

theorem ruChainJoin_valid :
    ValidSchreier ruChainJoin := ruChain_valid ruChainJoin_check.1

theorem ruChainCFaithful_valid : ValidSchreier ruChainCFaithful :=
  ruChain_valid ruChainCFaithful_check.1

theorem ruChainCQuotient80_valid :
    ValidSchreier ruChainCQuotient80 :=
  ruChain_valid ruChainCQuotient80_check.1

theorem ruChainS_valid :
    ValidSchreier ruChainS := ruChain_valid ruChainS_check.1

theorem ruChainK_valid :
    ValidSchreier ruChainK := ruChain_valid ruChainK_check.1

theorem ruChainJ_valid :
    ValidSchreier ruChainJ := ruChain_valid ruChainJ_check.1

theorem ruChainR_valid :
    ValidSchreier ruChainR := ruChain_valid ruChainR_check.1

theorem ruChainC_original :
    ruChainC.original.toList = [ruC0, ruC1] := by
  have h := ruChainC_check.1
  rw [show ruChainC.original.toList = (List.range 2).map fun i => permOfArr 4060
    (ruField4060 1)[i]! from ofArrays_original_toList, show List.range 2 = [0, 1] from rfl,
    List.map_cons, List.map_cons, List.map_nil,
    permOfArr_eq_of_eqA (ruChain_strong_inv h (by decide)) rep_ruC0 ruGens_check.1,
    permOfArr_eq_of_eqA (ruChain_strong_inv h (by decide)) rep_ruC1 ruGens_check.2.1]

theorem ruChainN_original :
    ruChainN.original.toList = [ruNs0, ruNs1] := by
  have h := ruChainN_check.1
  rw [show ruChainN.original.toList = (List.range 2).map fun i => permOfArr 4060
    (ruField4060 2)[i]! from ofArrays_original_toList, show List.range 2 = [0, 1] from rfl,
    List.map_cons, List.map_cons, List.map_nil,
    permOfArr_eq_of_eqA (ruChain_strong_inv h (by decide)) rep_ruNs0 ruGens_check.2.2.1,
    permOfArr_eq_of_eqA (ruChain_strong_inv h (by decide)) rep_ruNs1 ruGens_check.2.2.2.1]

theorem ruChainJoin_original :
    ruChainJoin.original.toList = [ruC0, ruC1, ruNs0, ruNs1] := by
  have h := ruChainJoin_check.1
  obtain ⟨-, -, -, -, g1, g2, g3, g4, -⟩ := ruGens_check
  rw [show ruChainJoin.original.toList = (List.range 4).map fun i => permOfArr 4060
    (ruField4060 3)[i]! from ofArrays_original_toList, show List.range 4 = [0, 1, 2, 3] from rfl,
    List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_nil,
    permOfArr_eq_of_eqA (ruChain_strong_inv h (by decide)) rep_ruC0 g1,
    permOfArr_eq_of_eqA (ruChain_strong_inv h (by decide)) rep_ruC1 g2,
    permOfArr_eq_of_eqA (ruChain_strong_inv h (by decide)) rep_ruNs0 g3,
    permOfArr_eq_of_eqA (ruChain_strong_inv h (by decide)) rep_ruNs1 g4]

theorem ruChainC_sub :
    ruChainC.originalSubgroup = ruC := by
  rw [RawSchreierDatum.originalSubgroup, ruChainC_original, setOf_mem_pair]
  rfl

theorem ruChainN_sub :
    ruChainN.originalSubgroup = ruN := by
  rw [RawSchreierDatum.originalSubgroup, ruChainN_original, setOf_mem_pair]
  rfl

theorem ruChainJoin_sub :
    ruChainJoin.originalSubgroup = ruC ⊔ ruN := by
  rw [RawSchreierDatum.originalSubgroup, ruChainJoin_original]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (Set.mem_insert _ _))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_insert _ _))
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  · refine sup_le (closure_pair_le ?_ ?_) (closure_pair_le ?_ ?_) <;>
      exact Subgroup.subset_closure (by simp)

theorem card_ruC :
    Nat.card ruC = 245760 := by
  have h : Nat.card ruChainC.originalSubgroup = _ := ruChain_card ruChainC_check.1
  rw [ruChainC_check.2.1, ruChainC_sub] at h
  exact h

theorem card_ruN :
    Nat.card ruN = 344064 := by
  have h : Nat.card ruChainN.originalSubgroup = _ := ruChain_card ruChainN_check.1
  rw [ruChainN_check.2, ruChainN_sub] at h
  exact h

theorem mem_ruC_of_sift
    {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g)
    (h : ruSift 4060 (ruField4060 1) ruCBase t = true) : g ∈ ruC := by
  rw [← ruChainC_sub]
  exact ((ruChain_sift ruChainC_check.1 ht).1 h : g ∈ ruChainC.originalSubgroup)

theorem ruP_eq_sup :
    ruP = ruC ⊔ ruN := by
  apply le_antisymm
  · rw [ruP, ← ruChainJoin_sub]
    apply closure_pair_le
    · exact ((ruChain_sift ruChainJoin_check.1 rep_ruA0).1 ruChainJoin_check.2.2.1 :
        ruA0 ∈ ruChainJoin.originalSubgroup)
    · exact ((ruChain_sift ruChainJoin_check.1 rep_ruA1).1 ruChainJoin_check.2.2.2 :
        ruA1 ∈ ruChainJoin.originalSubgroup)
  · exact sup_le ruC_le ruN_le

theorem card_ruP :
    Nat.card ruP = 145926144000 := by
  have h : Nat.card ruChainJoin.originalSubgroup = _ := ruChain_card ruChainJoin_check.1
  rw [ruChainJoin_check.2.1, ruChainJoin_sub, ← ruP_eq_sup] at h
  exact h

end CFSG.Sporadic.RuSchreier

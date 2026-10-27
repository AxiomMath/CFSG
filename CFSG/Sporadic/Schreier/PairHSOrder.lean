module

public import CFSG.Sporadic.Schreier.PairHSFaithful
public import CFSG.Sporadic.Schreier.PairHSCheck

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairNative

theorem hsChainArrays :
    ChainArrays hsChain (hsStrongArrs.extract 0 2) hsStrongArrs PairHS.baseArr hsWords :=
  chainArrays_ofArrays fun j hj =>
    (hsCertOK_parts.2.2.1 j (by simpa [hsStrongArrs] using hj)).2

theorem hsChain_valid :
    ValidSchreier hsChain ∧ ∀ i : Fin hsChain.baseCount,
    hsChain.orbitSize i = ((rawLevels 3850 hsStrongArrs PairHS.baseArr)[(i : ℕ)]!).pts.size :=
  validSchreier_of_chainOK hsChainArrays (by norm_num) PairHS.chain_check.1

theorem hsChain_baseCount : hsChain.baseCount = 4 := rfl

theorem hsChain_orbitSizes :
    (List.finRange hsChain.baseCount).map hsChain.orbitSize = [3850, 960, 6, 2] := by
  rw [← PairHS.chain_check.2, rawOrbitSizes]
  apply List.ext_getElem
  · rw [List.length_map, List.length_finRange, List.length_map, Array.length_toList, rawLevels,
      Array.size_ofFn]
    rfl
  · intro k h1 h2
    have hk : k < (rawLevels 3850 hsStrongArrs PairHS.baseArr).size := by simpa using h2
    simp only [List.getElem_map, List.getElem_finRange, Array.getElem_toList]
    rw [hsChain_valid.2]
    show ((rawLevels 3850 hsStrongArrs PairHS.baseArr)[k]!).pts.size = _
    rw [getElem!_pos _ k hk]

theorem hsChain_orbitSize
    (i : Fin hsChain.baseCount) :
    hsChain.orbitSize i = [3850, 960, 6, 2][(i : ℕ)]! := by
  rw [← hsChain_orbitSizes, getElem!_pos _ (i : ℕ) (by simp)]
  simp

theorem card_hsP :
    Nat.card hsP = 44352000 := by
  have h := (RawSchreierDatum.schreier_chain_order hsChain hsChain_valid.1).2.2.1
  rw [hsP_eq_original, h]
  simp only [← RawSchreierDatum.orbitSize_eq_card, hsChain_orbitSize]
  rfl

theorem hsP_orbit_zero :
    MulAction.orbit hsP (0 : Fin 3850) = Set.univ := by
  rw [hsP_eq_original]
  have h0 : (0 : ℕ) < hsChain.baseCount := by decide
  have horb := RawSchreierDatum.orbitPoints_eq_orbit hsChain ⟨0, h0⟩
  rw [RawSchreierDatum.levelSubgroup_zero_eq_original hsChain hsChain_valid.1] at horb
  have hcard : Nat.card (hsChain.orbitPoints ⟨0, h0⟩) = 3850 := by
    rw [← RawSchreierDatum.orbitSize_eq_card, hsChain_orbitSize]
    rfl
  rw [horb, show hsChain.base.get ⟨0, h0⟩ = 0 from rfl] at hcard
  refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, ← Nat.card_coe_set_eq, hcard]

theorem hsP_transitive :
    MulAction.IsPretransitive hsP (Fin 3850) := by
  refine ⟨fun x y => ?_⟩
  have hx : x ∈ MulAction.orbit hsP (0 : Fin 3850) := by rw [hsP_orbit_zero]; trivial
  have hy : y ∈ MulAction.orbit hsP (0 : Fin 3850) := by rw [hsP_orbit_zero]; trivial
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨h, rfl⟩ := hy
  exact ⟨h * g⁻¹, by rw [mul_smul, inv_smul_smul]⟩

theorem card_hsP_stabilizer :
    Nat.card (MulAction.stabilizer hsP (0 : Fin 3850)) = 11520 := by
  have h1 := MulAction.index_stabilizer hsP (0 : Fin 3850)
  have h2 := (MulAction.stabilizer hsP (0 : Fin 3850)).card_mul_index
  rw [h1, hsP_orbit_zero, Set.ncard_univ, Nat.card_fin, card_hsP] at h2
  have h3 : Nat.card (MulAction.stabilizer hsP (0 : Fin 3850)) * 3850 = 11520 * 3850 := by
    rw [h2]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h3

theorem hsGen_mem_P (k : ℕ) (hk : k < 2) : hsGen k ∈ hsP := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem hsGen_mem (k : ℕ) (hk : k < 2) : hsGen k ∈ hsChain.originalSubgroup :=
  hsP_eq_original ▸ hsGen_mem_P k hk

theorem hs_baseFaithful :
    BaseFaithful hsChain.originalSubgroup PairHS.bs := by
  have h := baseFaithful_of_valid hsChain_valid.1
  rwa [hsChain_base] at h

theorem hs_bs_lt : ∀ b ∈ PairHS.bs, b < 3850 := by
  decide

theorem repW_hswA : RepW 3850 PairHS.wA (hsGen 0) :=
  RepW.single (rep_hsGen (by norm_num))

theorem repW_hswB : RepW 3850 PairHS.wB (hsGen 1) :=
  RepW.single (rep_hsGen (by norm_num))

theorem hs_word_orders :
    orderOf (hsGen 0) = 2 ∧ orderOf (hsGen 1) = 5 ∧ orderOf (hsGen 0 * hsGen 1) = 11 ∧
      orderOf (hsGen 0 * hsGen 1 * (hsGen 0)⁻¹ * (hsGen 1)⁻¹) = 5 := by
  obtain ⟨h1, h2, h3, h4⟩ := PairHS.word_orders
  have ha := hsGen_mem 0 (by norm_num)
  have hb := hsGen_mem 1 (by norm_num)
  have o1 := (ordB_iff hs_baseFaithful hs_bs_lt repW_hswA ha (by norm_num)).1 h1
  have o2 := (ordB_iff hs_baseFaithful hs_bs_lt repW_hswB hb (by norm_num)).1 h2
  have o3 := (ordB_iff hs_baseFaithful hs_bs_lt (repW_patW repW_hswA repW_hswB [false, true])
    (patProd_mem _ ha hb _) (by norm_num)).1 h3
  have o4 := (ordB_iff hs_baseFaithful hs_bs_lt (repW_patW repW_hswA repW_hswB PairHS.commPat)
    (patProd_mem _ ha hb _) (by norm_num)).1 h4
  have hrel : PatRel [([false, true], 11), ([false, true, false] ++ List.replicate (5 - 1) true,
      5)] (hsGen 0) (hsGen 1) := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact o3
    · exact o4
  obtain ⟨o3', o4'⟩ := (patRel_comm_iff o1 o2 (by norm_num) 11 5).1 hrel
  exact ⟨o1, o2, o3', o4'⟩

theorem card_hs :
    Nat.card Blueprint.NativeSporadic.HS = 44352000 := by
  rw [Nat.card_congr hsPermEquiv.toEquiv, card_hsP]

theorem orderOf_hsSeed
    (u : Blueprint.NativeSporadic.HS) :
    orderOf u = orderOf (hsPermEquiv u : Equiv.Perm (Fin 3850)) := by
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]

theorem FAM_HS_order :
    ValidSchreier hsChain ∧ hsChain.base.toList.map Fin.val = [0, 1, 2, 3] ∧
      (List.finRange hsChain.baseCount).map hsChain.orbitSize = [3850, 960, 6, 2] ∧
      Nat.card hsP = 44352000 ∧ MulAction.IsPretransitive hsP (Fin 3850) ∧
      Nat.card (MulAction.stabilizer hsP (0 : Fin 3850)) = 11520 ∧
      orderOf (hsGen 0) = 2 ∧ orderOf (hsGen 1) = 5 ∧ orderOf (hsGen 0 * hsGen 1) = 11 ∧
      Nat.card Blueprint.NativeSporadic.HS = 44352000 ∧
      orderOf hsSeedA = 2 ∧ orderOf hsSeedB = 5 ∧ orderOf (hsSeedA * hsSeedB) = 11 := by
  obtain ⟨o1, o2, o3, -⟩ := hs_word_orders
  refine ⟨hsChain_valid.1, hsChain_base, hsChain_orbitSizes, card_hsP, hsP_transitive,
    card_hsP_stabilizer, o1, o2, o3, card_hs, ?_, ?_, ?_⟩
  · rw [orderOf_hsSeed, hsPermEquiv_seedA, o1]
  · rw [orderOf_hsSeed, hsPermEquiv_seedB, o2]
  · rw [orderOf_hsSeed, map_mul, Subgroup.coe_mul, hsPermEquiv_seedA, hsPermEquiv_seedB, o3]

end CFSG.Sporadic.Schreier

module

public import CFSG.Sporadic.Schreier.PairMcLFaithful
public import CFSG.Sporadic.Schreier.PairMcLCheck

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairNative

theorem mclChainArrays :
    ChainArrays mclChain (mclStrongArrs.extract 0 2) mclStrongArrs PairMcL.baseArr mclWords :=
  chainArrays_ofArrays fun j hj =>
    (mclCertOK_parts.2.2.1 j (by simpa [mclStrongArrs] using hj)).2

theorem mclChain_valid :
    ValidSchreier mclChain ∧ ∀ i : Fin mclChain.baseCount,
    mclChain.orbitSize i = ((rawLevels 275 mclStrongArrs PairMcL.baseArr)[(i : ℕ)]!).pts.size :=
  validSchreier_of_chainOK mclChainArrays (by norm_num) PairMcL.chain_check.1

theorem mclChain_baseCount : mclChain.baseCount = 5 := rfl

theorem mclChain_orbitSizes :
    (List.finRange mclChain.baseCount).map mclChain.orbitSize = [275, 112, 81, 45, 8] := by
  rw [← PairMcL.chain_check.2, rawOrbitSizes]
  apply List.ext_getElem
  · rw [List.length_map, List.length_finRange, List.length_map, Array.length_toList, rawLevels,
      Array.size_ofFn]
    rfl
  · intro k h1 h2
    have hk : k < (rawLevels 275 mclStrongArrs PairMcL.baseArr).size := by simpa using h2
    simp only [List.getElem_map, List.getElem_finRange, Array.getElem_toList]
    rw [mclChain_valid.2]
    show ((rawLevels 275 mclStrongArrs PairMcL.baseArr)[k]!).pts.size = _
    rw [getElem!_pos _ k hk]

theorem mclChain_orbitSize
    (i : Fin mclChain.baseCount) :
    mclChain.orbitSize i = [275, 112, 81, 45, 8][(i : ℕ)]! := by
  rw [← mclChain_orbitSizes, getElem!_pos _ (i : ℕ) (by simp)]
  simp

theorem card_mclP :
    Nat.card mclP = 898128000 := by
  have h := (RawSchreierDatum.schreier_chain_order mclChain mclChain_valid.1).2.2.1
  rw [mclP_eq_original, h]
  simp only [← RawSchreierDatum.orbitSize_eq_card, mclChain_orbitSize]
  rfl

theorem mclP_orbit_zero :
    MulAction.orbit mclP (0 : Fin 275) = Set.univ := by
  rw [mclP_eq_original]
  have h0 : (0 : ℕ) < mclChain.baseCount := by decide
  have horb := RawSchreierDatum.orbitPoints_eq_orbit mclChain ⟨0, h0⟩
  rw [RawSchreierDatum.levelSubgroup_zero_eq_original mclChain mclChain_valid.1] at horb
  have hcard : Nat.card (mclChain.orbitPoints ⟨0, h0⟩) = 275 := by
    rw [← RawSchreierDatum.orbitSize_eq_card, mclChain_orbitSize]
    rfl
  rw [horb, show mclChain.base.get ⟨0, h0⟩ = 0 from rfl] at hcard
  refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, ← Nat.card_coe_set_eq, hcard]

theorem mclP_transitive :
    MulAction.IsPretransitive mclP (Fin 275) := by
  refine ⟨fun x y => ?_⟩
  have hx : x ∈ MulAction.orbit mclP (0 : Fin 275) := by rw [mclP_orbit_zero]; trivial
  have hy : y ∈ MulAction.orbit mclP (0 : Fin 275) := by rw [mclP_orbit_zero]; trivial
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨h, rfl⟩ := hy
  exact ⟨h * g⁻¹, by rw [mul_smul, inv_smul_smul]⟩

theorem card_mclP_stabilizer :
    Nat.card (MulAction.stabilizer mclP (0 : Fin 275)) = 3265920 := by
  have h1 := MulAction.index_stabilizer mclP (0 : Fin 275)
  have h2 := (MulAction.stabilizer mclP (0 : Fin 275)).card_mul_index
  rw [h1, mclP_orbit_zero, Set.ncard_univ, Nat.card_fin, card_mclP] at h2
  have h3 : Nat.card (MulAction.stabilizer mclP (0 : Fin 275)) * 275 = 3265920 * 275 := by
    rw [h2]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h3

theorem mclGen_mem_P (k : ℕ) (hk : k < 2) : mclGen k ∈ mclP := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem mclGen_mem (k : ℕ) (hk : k < 2) : mclGen k ∈ mclChain.originalSubgroup :=
  mclP_eq_original ▸ mclGen_mem_P k hk

theorem mcl_baseFaithful :
    BaseFaithful mclChain.originalSubgroup PairMcL.bs := by
  have h := baseFaithful_of_valid mclChain_valid.1
  rwa [mclChain_base] at h

theorem mcl_bs_lt : ∀ b ∈ PairMcL.bs, b < 275 := by
  decide

theorem repW_mclwA : RepW 275 PairMcL.wA (mclGen 0) :=
  RepW.single (rep_mclGen (by norm_num))

theorem repW_mclwB : RepW 275 PairMcL.wB (mclGen 1) :=
  RepW.single (rep_mclGen (by norm_num))

theorem mcl_word_orders :
    orderOf (mclGen 0) = 2 ∧ orderOf (mclGen 1) = 5 ∧ orderOf (mclGen 0 * mclGen 1) = 11 ∧
      orderOf (mclGen 0 * mclGen 1 * (mclGen 0)⁻¹ * (mclGen 1)⁻¹) = 5 := by
  obtain ⟨h1, h2, h3, h4⟩ := PairMcL.word_orders
  have ha := mclGen_mem 0 (by norm_num)
  have hb := mclGen_mem 1 (by norm_num)
  have o1 := (ordB_iff mcl_baseFaithful mcl_bs_lt repW_mclwA ha (by norm_num)).1 h1
  have o2 := (ordB_iff mcl_baseFaithful mcl_bs_lt repW_mclwB hb (by norm_num)).1 h2
  have o3 := (ordB_iff mcl_baseFaithful mcl_bs_lt (repW_patW repW_mclwA repW_mclwB [false, true])
    (patProd_mem _ ha hb _) (by norm_num)).1 h3
  have o4 := (ordB_iff mcl_baseFaithful mcl_bs_lt (repW_patW repW_mclwA repW_mclwB PairMcL.commPat)
    (patProd_mem _ ha hb _) (by norm_num)).1 h4
  have hrel : PatRel [([false, true], 11), ([false, true, false] ++ List.replicate (5 - 1) true,
      5)] (mclGen 0) (mclGen 1) := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact o3
    · exact o4
  obtain ⟨o3', o4'⟩ := (patRel_comm_iff o1 o2 (by norm_num) 11 5).1 hrel
  exact ⟨o1, o2, o3', o4'⟩

theorem card_mcl :
    Nat.card Blueprint.NativeSporadic.McL = 898128000 := by
  rw [Nat.card_congr mclPermEquiv.toEquiv, card_mclP]

theorem orderOf_mclSeed
    (u : Blueprint.NativeSporadic.McL) :
    orderOf u = orderOf (mclPermEquiv u : Equiv.Perm (Fin 275)) := by
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]

theorem FAM_McL_order :
    ValidSchreier mclChain ∧ mclChain.base.toList.map Fin.val = [0, 1, 2, 3, 4] ∧
      (List.finRange mclChain.baseCount).map mclChain.orbitSize = [275, 112, 81, 45, 8] ∧
      Nat.card mclP = 898128000 ∧ MulAction.IsPretransitive mclP (Fin 275) ∧
      Nat.card (MulAction.stabilizer mclP (0 : Fin 275)) = 3265920 ∧
      orderOf (mclGen 0) = 2 ∧ orderOf (mclGen 1) = 5 ∧ orderOf (mclGen 0 * mclGen 1) = 11 ∧
      Nat.card Blueprint.NativeSporadic.McL = 898128000 ∧
      orderOf mclSeedA = 2 ∧ orderOf mclSeedB = 5 ∧ orderOf (mclSeedA * mclSeedB) = 11 := by
  obtain ⟨o1, o2, o3, -⟩ := mcl_word_orders
  refine ⟨mclChain_valid.1, mclChain_base, mclChain_orbitSizes, card_mclP, mclP_transitive,
    card_mclP_stabilizer, o1, o2, o3, card_mcl, ?_, ?_, ?_⟩
  · rw [orderOf_mclSeed, mclPermEquiv_seedA, o1]
  · rw [orderOf_mclSeed, mclPermEquiv_seedB, o2]
  · rw [orderOf_mclSeed, map_mul, Subgroup.coe_mul, mclPermEquiv_seedA, mclPermEquiv_seedB, o3]

end CFSG.Sporadic.Schreier

module

public import CFSG.Sporadic.Schreier.PairJ3Faithful
public import CFSG.Sporadic.Schreier.PairJ3Check

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairNative

theorem j3ChainArrays :
    ChainArrays j3Chain (j3StrongArrs.extract 0 2) j3StrongArrs PairJ3.baseArr j3Words :=
  chainArrays_ofArrays fun j hj =>
    (j3CertOK_parts.2.2.2.2.1 j (by simpa [j3StrongArrs] using hj)).2

theorem j3Chain_valid :
    ValidSchreier j3Chain ∧ ∀ i : Fin j3Chain.baseCount,
    j3Chain.orbitSize i = ((rawLevels 6156 j3StrongArrs PairJ3.baseArr)[(i : ℕ)]!).pts.size :=
  validSchreier_of_chainOK j3ChainArrays (by norm_num) PairJ3.chain_check.1

theorem j3Chain_baseCount : j3Chain.baseCount = 4 := rfl

theorem j3Chain_orbitSizes :
    (List.finRange j3Chain.baseCount).map j3Chain.orbitSize = [6156, 1360, 2, 3] := by
  rw [← PairJ3.chain_check.2, rawOrbitSizes]
  apply List.ext_getElem
  · rw [List.length_map, List.length_finRange, List.length_map, Array.length_toList, rawLevels,
      Array.size_ofFn]
    rfl
  · intro k h1 h2
    have hk : k < (rawLevels 6156 j3StrongArrs PairJ3.baseArr).size := by simpa using h2
    simp only [List.getElem_map, List.getElem_finRange, Array.getElem_toList]
    rw [j3Chain_valid.2]
    show ((rawLevels 6156 j3StrongArrs PairJ3.baseArr)[k]!).pts.size = _
    rw [getElem!_pos _ k hk]

theorem j3Chain_orbitSize
    (i : Fin j3Chain.baseCount) :
    j3Chain.orbitSize i = [6156, 1360, 2, 3][(i : ℕ)]! := by
  rw [← j3Chain_orbitSizes, getElem!_pos _ (i : ℕ) (by simp)]
  simp

theorem card_j3P :
    Nat.card j3P = 50232960 := by
  have h := (RawSchreierDatum.schreier_chain_order j3Chain j3Chain_valid.1).2.2.1
  rw [j3P_eq_original, h]
  simp only [← RawSchreierDatum.orbitSize_eq_card, j3Chain_orbitSize]
  rfl

theorem j3P_orbit_zero :
    MulAction.orbit j3P (0 : Fin 6156) = Set.univ := by
  rw [j3P_eq_original]
  have h0 : (0 : ℕ) < j3Chain.baseCount := by decide
  have horb := RawSchreierDatum.orbitPoints_eq_orbit j3Chain ⟨0, h0⟩
  rw [RawSchreierDatum.levelSubgroup_zero_eq_original j3Chain j3Chain_valid.1] at horb
  have hcard : Nat.card (j3Chain.orbitPoints ⟨0, h0⟩) = 6156 := by
    rw [← RawSchreierDatum.orbitSize_eq_card, j3Chain_orbitSize]
    rfl
  rw [horb, show j3Chain.base.get ⟨0, h0⟩ = 0 from rfl] at hcard
  refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin, ← Nat.card_coe_set_eq, hcard]

theorem j3P_transitive :
    MulAction.IsPretransitive j3P (Fin 6156) := by
  refine ⟨fun x y => ?_⟩
  have hx : x ∈ MulAction.orbit j3P (0 : Fin 6156) := by rw [j3P_orbit_zero]; trivial
  have hy : y ∈ MulAction.orbit j3P (0 : Fin 6156) := by rw [j3P_orbit_zero]; trivial
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨h, rfl⟩ := hy
  exact ⟨h * g⁻¹, by rw [mul_smul, inv_smul_smul]⟩

theorem card_j3P_stabilizer :
    Nat.card (MulAction.stabilizer j3P (0 : Fin 6156)) = 8160 := by
  have h1 := MulAction.index_stabilizer j3P (0 : Fin 6156)
  have h2 := (MulAction.stabilizer j3P (0 : Fin 6156)).card_mul_index
  rw [h1, j3P_orbit_zero, Set.ncard_univ, Nat.card_fin, card_j3P] at h2
  have h3 : Nat.card (MulAction.stabilizer j3P (0 : Fin 6156)) * 6156 = 8160 * 6156 := by
    rw [h2]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h3

theorem j3Gen_mem_P (k : ℕ) (hk : k < 2) : j3Gen k ∈ j3P := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem j3Gen_mem (k : ℕ) (hk : k < 2) : j3Gen k ∈ j3Chain.originalSubgroup :=
  j3P_eq_original ▸ j3Gen_mem_P k hk

theorem j3_baseFaithful :
    BaseFaithful j3Chain.originalSubgroup PairJ3.bs := by
  have h := baseFaithful_of_valid j3Chain_valid.1
  rwa [j3Chain_base] at h

theorem j3_bs_lt : ∀ b ∈ PairJ3.bs, b < 6156 := by
  decide

theorem repW_j3wA : RepW 6156 PairJ3.wA (j3Gen 0) :=
  RepW.single (rep_j3Gen (by norm_num))

theorem repW_j3wB : RepW 6156 PairJ3.wB (j3Gen 1) :=
  RepW.single (rep_j3Gen (by norm_num))

theorem j3_word_orders :
    orderOf (j3Gen 0) = 2 ∧ orderOf (j3Gen 1) = 3 ∧ orderOf (j3Gen 0 * j3Gen 1) = 19 ∧
      orderOf (j3Gen 0 * j3Gen 1 * (j3Gen 0)⁻¹ * (j3Gen 1)⁻¹) = 9 := by
  obtain ⟨h1, h2, h3, h4⟩ := PairJ3.word_orders
  have ha := j3Gen_mem 0 (by norm_num)
  have hb := j3Gen_mem 1 (by norm_num)
  have o1 := (ordB_iff j3_baseFaithful j3_bs_lt repW_j3wA ha (by norm_num)).1 h1
  have o2 := (ordB_iff j3_baseFaithful j3_bs_lt repW_j3wB hb (by norm_num)).1 h2
  have o3 := (ordB_iff j3_baseFaithful j3_bs_lt (repW_patW repW_j3wA repW_j3wB [false, true])
    (patProd_mem _ ha hb _) (by norm_num)).1 h3
  have o4 := (ordB_iff j3_baseFaithful j3_bs_lt (repW_patW repW_j3wA repW_j3wB PairJ3.commPat)
    (patProd_mem _ ha hb _) (by norm_num)).1 h4
  have hrel : PatRel [([false, true], 19), ([false, true, false] ++ List.replicate (3 - 1) true,
      9)] (j3Gen 0) (j3Gen 1) := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact o3
    · exact o4
  obtain ⟨o3', o4'⟩ := (patRel_comm_iff o1 o2 (by norm_num) 19 9).1 hrel
  exact ⟨o1, o2, o3', o4'⟩

theorem card_j3 :
    Nat.card Blueprint.NativeSporadic.J3 = 50232960 := by
  rw [Nat.card_congr j3PermEquiv.toEquiv, card_j3P]

theorem orderOf_j3Seed
    (u : Blueprint.NativeSporadic.J3) :
    orderOf u = orderOf (j3PermEquiv u : Equiv.Perm (Fin 6156)) := by
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]

theorem FAM_J3_order :
    ValidSchreier j3Chain ∧ j3Chain.base.toList.map Fin.val = [0, 1, 3, 2] ∧
      (List.finRange j3Chain.baseCount).map j3Chain.orbitSize = [6156, 1360, 2, 3] ∧
      Nat.card j3P = 50232960 ∧ MulAction.IsPretransitive j3P (Fin 6156) ∧
      Nat.card (MulAction.stabilizer j3P (0 : Fin 6156)) = 8160 ∧
      orderOf (j3Gen 0) = 2 ∧ orderOf (j3Gen 1) = 3 ∧ orderOf (j3Gen 0 * j3Gen 1) = 19 ∧
      Nat.card Blueprint.NativeSporadic.J3 = 50232960 ∧
      orderOf j3SeedA = 2 ∧ orderOf j3SeedB = 3 ∧ orderOf (j3SeedA * j3SeedB) = 19 := by
  obtain ⟨o1, o2, o3, -⟩ := j3_word_orders
  refine ⟨j3Chain_valid.1, j3Chain_base, j3Chain_orbitSizes, card_j3P, j3P_transitive,
    card_j3P_stabilizer, o1, o2, o3, card_j3, ?_, ?_, ?_⟩
  · rw [orderOf_j3Seed, j3PermEquiv_seedA, o1]
  · rw [orderOf_j3Seed, j3PermEquiv_seedB, o2]
  · rw [orderOf_j3Seed, map_mul, Subgroup.coe_mul, j3PermEquiv_seedA, j3PermEquiv_seedB, o3]

end CFSG.Sporadic.Schreier

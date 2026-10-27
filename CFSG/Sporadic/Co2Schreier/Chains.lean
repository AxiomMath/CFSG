
module

public import CFSG.Sporadic.Co2Schreier.ChainsBase

public import CFSG.Sporadic.Co2Schreier.ChainCheck
public import CFSG.Sporadic.Co2Schreier.Tuples
public import CFSG.Sporadic.Co2Cert.Order
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Co2Schreier.ChainCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Co2Schreier.TextCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Text
public import CFSG.Sporadic.Co2Cert.CheckInputs
public import CFSG.Sporadic.Co2Cert.OrderCheckInputs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert

theorem wordFacts : WordFacts := by
  have h := words_check
  simp only [wordsCheck, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', allLt_iff,
    and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34⟩

theorem repTuple_a :
    RepTuple 2300 aArrs aSeeds := by
  refine ⟨wordFacts.sizeA, fun h hh => ?_⟩
  have hh2 : h < 2 := hh
  have ea : aArrs = co2OrigArrs := rfl
  have e0 : aSeeds.getD 0 1 = co2Gen 0 := List.getD_cons_zero
  have e1 : aSeeds.getD 1 1 = co2Gen 1 := List.getD_cons_succ.trans List.getD_cons_zero
  rw [ea]
  interval_cases h
  · rw [e0]
    exact rep_co2Gen (by norm_num)
  · rw [e1]
    exact rep_co2Gen (by norm_num)

theorem repTuple_cInit :
    RepTuple 2300 cInitArrs cInitTuple :=
  repTuple_a.mapWords wordFacts.invA localShape.cInit_letters

theorem repTuple_d :
    RepTuple 2300 dArrs dTuple :=
  repTuple_a.mapWords wordFacts.invA localShape.dWords_letters

theorem repTuple_dStar :
    RepTuple 2300 dStarArrs dStarTuple :=
  repTuple_d.extend (by rw [dTuple_length]; exact localShape.dDeriv_letters) wordFacts.invDStar

theorem repTuple_r :
    RepTuple 2300 rArrs rTuple :=
  repTuple_dStar.mapWords wordFacts.invDStar (by rw [dStarTuple_length]; exact
    localShape.rWords_letters)

theorem rep_z0 :
    Rep 2300 z0Arr locZ0 :=
  repTuple_cInit.word wordFacts.invCInit (by rw [cInitTuple_length]; exact localShape.z0_letters)

theorem rep_t :
    Rep 2300 tArr locT :=
  repTuple_d.word wordFacts.invD (by rw [dTuple_length]; exact localShape.t_letters)

theorem rep_z :
    Rep 2300 zArr locZ :=
  repTuple_r.word wordFacts.invR (by rw [rTuple_length]; exact localShape.z_letters)

theorem rep_w :
    Rep 2300 wArr locW :=
  repTuple_a.word wordFacts.invA localShape.w_letters

theorem rep_x :
    Rep 2300 xArr locX :=
  rep_compA (rep_compA rep_w rep_z0) (rep_inv_of_isInvA rep_w wordFacts.invW)

theorem rep_h :
    Rep 2300 hArr locH :=
  rep_compA (rep_powArr (rep_compA rep_x rep_z) _) (rep_powArr (rep_compA rep_z0 rep_x) _)

theorem repTuple_c :
    RepTuple 2300 cArrs cTuple :=
  repTuple_cInit.conj rep_h wordFacts.invH

theorem repTuple_cStar :
    RepTuple 2300 cStarArrs cStarTuple :=
  repTuple_c.extend (by rw [cTuple_length]; exact localShape.cDeriv_letters) wordFacts.invCStar

theorem repTuple_q :
    RepTuple 2300 qArrs qTuple :=
  repTuple_cStar.mapWords wordFacts.invCStar (by rw [cStarTuple_length]; exact
    localShape.qWords_letters)

theorem repTuple_s :
    RepTuple 2300 sArrs sTuple := by
  refine repTuple_q.append (repTuple_cStar.mapWords wordFacts.invCStar ?_)
  rw [cStarTuple_length]
  exact localShape.sWords_letters

theorem chainC_valid :
    ValidSchreier chainC :=
  (validSchreier_of_chainOK chainC_arrays (by norm_num) chainC_check.1).1

theorem chainD_valid :
    ValidSchreier chainD :=
  (validSchreier_of_chainOK chainD_arrays (by norm_num) chainD_check.1).1

theorem chainS_valid :
    ValidSchreier chainS :=
  (validSchreier_of_chainOK chainS_arrays (by norm_num) chainS_check.1).1

theorem chainJoin_valid :
    ValidSchreier chainJoin :=
  (validSchreier_of_chainOK chainJoin_arrays (by norm_num) chainJoin_check.1).1

theorem chainC_original :
    chainC.originalSubgroup = locC := by
  rw [locC]
  exact originalSubgroup_rawOfArrays_of_eqA repTuple_c
    (by rw [localShape.chainC.origArrs_size, cTuple_length])
    (fun k hk => (rep_permOfArr (localShape.chainC.orig_inv
      (by rwa [localShape.chainC.origArrs_size] at hk))).1)
    (fun k hk => wordFacts.eqC k (by rwa [localShape.chainC.origArrs_size] at hk))

theorem chainD_original :
    chainD.originalSubgroup = locD := by
  rw [locD]
  exact originalSubgroup_rawOfArrays_of_eqA repTuple_d
    (by rw [localShape.chainD.origArrs_size, dTuple_length])
    (fun k hk => (rep_permOfArr (localShape.chainD.orig_inv
      (by rwa [localShape.chainD.origArrs_size] at hk))).1)
    (fun k hk => wordFacts.eqD k (by rwa [localShape.chainD.origArrs_size] at hk))

theorem chainS_original :
    chainS.originalSubgroup = locS := by
  rw [locS]
  exact originalSubgroup_rawOfArrays_of_eqA repTuple_s
    (by rw [localShape.chainS.origArrs_size, sTuple_length])
    (fun k hk => (rep_permOfArr (localShape.chainS.orig_inv
      (by rwa [localShape.chainS.origArrs_size] at hk))).1)
    (fun k hk => wordFacts.eqS k (by rwa [localShape.chainS.origArrs_size] at hk))

theorem chainJoin_original :
    chainJoin.originalSubgroup = locC ⊔ locD := by
  rw [locC, locD, ← Subgroup.closure_union]
  have h := originalSubgroup_rawOfArrays_of_eqA (repTuple_c.append repTuple_d)
    (by rw [localShape.chainJoin.origArrs_size, List.length_append, cTuple_length, dTuple_length])
    (fun k hk => (rep_permOfArr (localShape.chainJoin.orig_inv
      (by rwa [localShape.chainJoin.origArrs_size] at hk))).1)
    (fun k hk => wordFacts.eqJoin k (by rwa [localShape.chainJoin.origArrs_size] at hk))
    (S := localRec.chains.join.strongArrs) (base := localRec.chains.join.baseArr)
    (W := localRec.chains.join.wordArrs) (hn := by norm_num)
    (hle := chainJoin_le)
    (hlt := baseArr_lt_of_shape localShape.chainJoin (by decide))
    (hnd := baseArr_nodup_of_shape localShape.chainJoin (by decide))
  refine h.trans ?_
  congr 1
  ext g
  simp [List.mem_append]

theorem card_locC :
    Nat.card locC = 743178240 := by
  rw [← chainC_original, card_originalSubgroup_of_chainOK chainC_arrays (by norm_num)
    chainC_check.1]
  change (recordOrbits 2300 localRec.chains.C).prod = _
  rw [chainC_check.2]
  rfl

theorem card_locD :
    Nat.card locD = 41287680 := by
  rw [← chainD_original, card_originalSubgroup_of_chainOK chainD_arrays (by norm_num)
    chainD_check.1]
  change (recordOrbits 2300 localRec.chains.D).prod = _
  rw [chainD_check.2]
  rfl

theorem card_locS :
    Nat.card locS = 262144 := by
  rw [← chainS_original, card_originalSubgroup_of_chainOK chainS_arrays (by norm_num)
    chainS_check.1]
  change (recordOrbits 2300 localRec.chains.S).prod = _
  rw [chainS_check.2]
  rfl

theorem card_locC_sup_locD :
    Nat.card ↥(locC ⊔ locD) = 42305421312000 := by
  rw [← chainJoin_original, card_originalSubgroup_of_chainOK chainJoin_arrays (by norm_num)
    chainJoin_check.1]
  change (recordOrbits 2300 localRec.chains.join).prod = _
  rw [chainJoin_check.2]
  rfl

theorem locC_sup_locD :
    locC ⊔ locD = co2P :=
  Subgroup.eq_of_le_of_card_ge (sup_le locC_le_P locD_le_P)
    (by rw [card_co2P, card_locC_sup_locD])

theorem card_locS_subgroupOf :
    Nat.card (locS.subgroupOf co2P) = 262144 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe locS_le_P).toEquiv, card_locS]

theorem isPGroup_locS_subgroupOf :
    IsPGroup 2 (locS.subgroupOf co2P) :=
  IsPGroup.of_card (n := 18) (by rw [card_locS_subgroupOf]; norm_num)

theorem index_locS_subgroupOf :
    (locS.subgroupOf co2P).index = 161382375 := by
  have h := (locS.subgroupOf co2P).index_mul_card
  rw [card_locS_subgroupOf, card_co2P] at h
  have h' : (locS.subgroupOf co2P).index * 262144 = 161382375 * 262144 := by rw [h]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

@[expose] def locSylow :
    Sylow 2 co2P :=
  isPGroup_locS_subgroupOf.toSylow (by rw [index_locS_subgroupOf]; decide)

theorem coe_locSylow :
    (locSylow : Subgroup co2P) = locS.subgroupOf co2P := rfl

theorem mem_locS_of_sift
    {t : Array ℕ} {g : Equiv.Perm (Fin 2300)} (hg : Rep 2300 t g)
    (h : siftA 2300 levelsS localRec.chains.S.baseArr 0 t = true) : g ∈ locS := by
  rw [← chainS_original]
  exact (siftA_iff_mem_originalSubgroup chainS_arrays (by norm_num) chainS_check.1 hg).1 h

theorem locQ_le_S :
    locQ ≤ locS := by
  rw [locQ, Subgroup.closure_le]
  intro g hg
  obtain ⟨k, hk, rfl⟩ := (mem_iff_exists_getD (d := 1)).1 hg
  exact mem_locS_of_sift (repTuple_q.rep hk) (wordFacts.siftQ k (qTuple_length ▸ hk))

theorem locR_le_S :
    locR ≤ locS := by
  rw [locR, Subgroup.closure_le]
  intro g hg
  obtain ⟨k, hk, rfl⟩ := (mem_iff_exists_getD (d := 1)).1 hg
  exact mem_locS_of_sift (repTuple_r.rep hk) (wordFacts.siftR k (rTuple_length ▸ hk))

theorem locZ_mem_S :
    locZ ∈ locS := mem_locS_of_sift rep_z wordFacts.siftZ

theorem locT_mem_S :
    locT ∈ locS := mem_locS_of_sift rep_t wordFacts.siftT

theorem locZ_sq :
    locZ ^ 2 = 1 := by
  rw [pow_two]
  exact eq_of_eqA (rep_compA rep_z rep_z) rep_idA wordFacts.zSq

theorem locT_sq :
    locT ^ 2 = 1 := by
  rw [pow_two]
  exact eq_of_eqA (rep_compA rep_t rep_t) rep_idA wordFacts.tSq

theorem locZ_ne_one :
    locZ ≠ 1 := by
  intro h
  have := wordFacts.zNe
  rw [(eqA_iff rep_z rep_idA).2 h] at this
  exact Bool.noConfusion this

theorem locT_ne_one :
    locT ≠ 1 := by
  intro h
  have := wordFacts.tNe
  rw [(eqA_iff rep_t rep_idA).2 h] at this
  exact Bool.noConfusion this

theorem locC_le_centralizer :
    locC ≤ Subgroup.centralizer {locZ} := by
  rw [locC, Subgroup.closure_le]
  intro g hg
  obtain ⟨k, hk, rfl⟩ := (mem_iff_exists_getD (d := 1)).1 hg
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exact (commA_iff (repTuple_c.rep hk) rep_z).1 (wordFacts.commZ k (cTuple_length ▸ hk))

theorem locD_le_centralizer :
    locD ≤ Subgroup.centralizer {locT} := by
  rw [locD, Subgroup.closure_le]
  intro g hg
  obtain ⟨k, hk, rfl⟩ := (mem_iff_exists_getD (d := 1)).1 hg
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exact (commA_iff (repTuple_d.rep hk) rep_t).1 (wordFacts.commT k (dTuple_length ▸ hk))

theorem AT_Co2_local_chain_orders :
    ValidSchreier chainC ∧ ValidSchreier chainD ∧ ValidSchreier chainS ∧
    ValidSchreier chainJoin ∧
    chainC.originalSubgroup = locC ∧ chainD.originalSubgroup = locD ∧
    chainS.originalSubgroup = locS ∧ chainJoin.originalSubgroup = locC ⊔ locD ∧
    Nat.card locC = 743178240 ∧ Nat.card locD = 41287680 ∧ Nat.card locS = 262144 ∧
    Nat.card ↥(locC ⊔ locD) = 42305421312000 ∧ locC ⊔ locD = co2P ∧ locS ≤ co2P ∧
    (∃ T : Sylow 2 co2P, (T : Subgroup co2P) = locS.subgroupOf co2P) ∧
    locQ ≤ locS ∧ locR ≤ locS ∧ locZ ∈ locS ∧ locT ∈ locS ∧ locZ ^ 2 = 1 ∧ locT ^ 2 = 1 ∧
    locZ ≠ 1 ∧ locT ≠ 1 ∧ locC ≤ co2P ⊓ Subgroup.centralizer {locZ} ∧
    locD ≤ co2P ⊓ Subgroup.centralizer {locT} :=
  ⟨chainC_valid, chainD_valid, chainS_valid, chainJoin_valid, chainC_original, chainD_original,
    chainS_original, chainJoin_original, card_locC, card_locD, card_locS, card_locC_sup_locD,
    locC_sup_locD, locS_le_P, ⟨locSylow, rfl⟩, locQ_le_S, locR_le_S, locZ_mem_S, locT_mem_S,
    locZ_sq, locT_sq, locZ_ne_one, locT_ne_one, le_inf locC_le_P locC_le_centralizer,
    le_inf locD_le_P locD_le_centralizer⟩

end CFSG.Sporadic.Co2Schreier

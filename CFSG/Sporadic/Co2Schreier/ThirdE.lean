
module

public import CFSG.Sporadic.Co2Schreier.ThirdEBase1

public import CFSG.Sporadic.Co2Schreier.ThirdOrder
public import CFSG.Sporadic.Co2Schreier.Action
public import CFSG.Sporadic.Co2Schreier.Cores
public import CFSG.Sporadic.Co2Schreier.Kernel
public import CFSG.Sporadic.Co2Schreier.SylowLemmas
public import CFSG.Sporadic.Schreier.RuSylowB
public import Certificates.Certificate2062
public import CFSG.Sporadic.Co2Schreier.ChainCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Co2Schreier.TextCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Text
public import CFSG.Sporadic.Co2Schreier.ThirdCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.WitCheck
public meta import CFSG.Sporadic.Co2Schreier.SylowCheck
public meta import CFSG.Sporadic.Co2Schreier.CoreCheck
public meta import CFSG.Sporadic.Co2Cert.FaithfulCheck
public import CFSG.Sporadic.Co2Cert.CheckInputs
public import CFSG.Sporadic.Co2Cert.OrderCheckInputs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert CFSG.Sporadic.RuSchreier
  CFSG.Sporadic.SmallF2.Native

theorem eFacts : EFacts := by
  have h := e_check
  simp only [eCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem gA_size : gA.size = 15 := beq_iff_eq.1 eFacts.size

theorem gFacts {i : ℕ} (hi : i < 15) :
    isInvA 2300 gA[i]! (invCand 2300 gA[i]!) = true ∧
      (∀ k < 2300, co2PackedVecs[(gA[i]!)[k]!]! =
        vecMulN 22 (transposeRows 22 ((oddMats witRec).getD i []).toArray) co2PackedVecs[k]!) ∧
      siftA 2300 (rawLevels 2300 co2StrongArrs co2BaseArr) co2BaseArr 0 gA[i]! = true ∧
      eqA 2300 (compA 2300 gA[i]! uArr) (compA 2300 uArr gA[i]!) = true := by
  have h := allLt_iff.1 eFacts.gens i hi
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, fun k hk => beq_iff_eq.1 (allLt_iff.1 h2 k hk), h3, h4⟩

theorem rep_gPerm {i : ℕ} (hi : i < 15) : Rep 2300 gA[i]! (gPerm i) :=
  (rep_permOfArr (gFacts hi).1).1

theorem repTuple_g : RepTuple 2300 gA gTuple := by
  refine ⟨by rw [gA_size, gTuple_length], fun i hi => ?_⟩
  rw [gTuple_length] at hi
  rw [gTuple_getD hi]
  exact rep_gPerm hi

theorem allInv_gA : allInv gA = true := by
  rw [allInv, allLt_iff]
  intro i hi
  rw [gA_size] at hi
  exact (gFacts hi).1

theorem gPerm_mem {i : ℕ} (hi : i < 15) : gPerm i ∈ co2P := by
  rw [← co2Q_originalSubgroup]
  exact (siftA_iff_mem_originalSubgroup co2Q_chainArrays (by norm_num) co2Chain_check.1
    (rep_gPerm hi)).1 (gFacts hi).2.2.1

theorem gPerm_comm {i : ℕ} (hi : i < 15) : locU * gPerm i = gPerm i * locU :=
  ((eqA_iff (rep_compA (rep_gPerm hi) rep_u) (rep_compA rep_u (rep_gPerm hi))).1
    (gFacts hi).2.2.2).symm

theorem locE_le_H3 : locE ≤ locH3 := by
  rw [locE, Subgroup.closure_le]
  intro g hg
  obtain ⟨i, hi, rfl⟩ := (mem_iff_exists_getD (d := 1)).1 hg
  rw [gTuple_length] at hi
  rw [gTuple_getD hi]
  exact mem_locH3.2 ⟨gPerm_mem hi, gPerm_comm hi⟩

theorem eRec_shape : ChainShape eRec 2300 15 26 witRec.third.baseIndices :=
  chainShape_of eFacts.eShape

@[expose] def chainE : RawSchreierDatum 2300 :=
  rawOfArrays 2300 eRec.origArrs eRec.strongArrs eRec.baseArr eRec.wordArrs (by norm_num)
    (by rw [eRec_shape.origArrs_size, eRec_shape.strongArrs_size]; norm_num)
    (baseArr_lt_of_shape eRec_shape thirdBase_lt)
    (baseArr_nodup_of_shape eRec_shape thirdBase_nodup)

theorem chainE_records : eRec.Records chainE :=
  records_rawOfArrays_of_shape eRec_shape _ _ _ _ (by norm_num)

theorem chainE_original : chainE.originalSubgroup = locE := by
  unfold chainE
  refine originalSubgroup_rawOfArrays_of_eqA repTuple_g ?_ (fun k hk => ?_) fun k hk => ?_
  · rw [eRec_origArrs, gA_size, gTuple_length]
  · have hk' : k < 15 := by rwa [eRec_origArrs, gA_size] at hk
    exact (rep_permOfArr (eRec_shape.orig_inv hk')).1
  · have hk' : k < 15 := by rwa [eRec_origArrs, gA_size] at hk
    rw [eRec_origArrs]
    exact (eqA_iff (rep_gPerm hk') (rep_gPerm hk')).2 rfl

theorem card_locE : Nat.card locE = 1474560 := by
  rw [← chainE_original, card_originalSubgroup_of_chainOK chainE_records.2.2 (by norm_num)
    eFacts.eOK]
  change (recordOrbits 2300 eRec).prod = _
  rw [beq_iff_eq.1 eFacts.eOrb]
  rfl

theorem locH3_eq_E : locH3 = locE :=
  (Subgroup.eq_of_le_of_card_ge locE_le_H3 (by rw [card_locE]; exact card_locH3_le)).symm

theorem card_locH3 : Nat.card locH3 = 1474560 := by
  rw [locH3_eq_E, card_locE]

theorem quFacts {i : ℕ} (hi : i < 10) :
    isInvA 2300 quA[i]! (invCand 2300 quA[i]!) = true ∧
      eqA 2300 (compA 2300 quA[i]! quA[i]!) (idA 2300) = true ∧
      ∀ j < 10, eqA 2300 (compA 2300 quA[i]! quA[j]!) (compA 2300 quA[j]! quA[i]!) = true := by
  have h := allLt_iff.1 eFacts.qu i hi
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, fun j hj => allLt_iff.1 h.2 j hj⟩

theorem rep_quPerm {i : ℕ} (hi : i < 10) : Rep 2300 quA[i]! (quPerm i) :=
  (rep_permOfArr (quFacts hi).1).1

theorem repTuple_qu : RepTuple 2300 quA quTuple := by
  refine ⟨by rw [quA_size, quTuple_length], fun i hi => ?_⟩
  rw [quTuple_length] at hi
  rw [quTuple_getD hi]
  exact rep_quPerm hi

theorem quE_facts : EnumFacts quA 1024 quE := enumFacts_of (by norm_num) eFacts.qEnum

theorem card_locQu : Nat.card locQu = 1024 := quE_facts.card repTuple_qu

theorem quPerm_sq {i : ℕ} (hi : i < 10) : quPerm i * quPerm i = 1 :=
  eq_of_eqA (rep_compA (rep_quPerm hi) (rep_quPerm hi)) rep_idA (quFacts hi).2.1

theorem quPerm_comm {i j : ℕ} (hi : i < 10) (hj : j < 10) :
    quPerm i * quPerm j = quPerm j * quPerm i :=
  eq_of_eqA (rep_compA (rep_quPerm hi) (rep_quPerm hj)) (rep_compA (rep_quPerm hj)
    (rep_quPerm hi)) ((quFacts hi).2.2 j hj)

theorem locQu_comm {x y : Equiv.Perm (Fin 2300)} (hx : x ∈ locQu) (hy : y ∈ locQu) :
    x * y = y * x := by
  have hk : ({g | g ∈ quTuple} : Set (Equiv.Perm (Fin 2300))).Pairwise Commute := by
    intro a ha b hb _
    obtain ⟨i, hi, rfl⟩ := mem_quTuple ha
    obtain ⟨j, hj, rfl⟩ := mem_quTuple hb
    exact quPerm_comm hi hj
  have hc := Subgroup.isMulCommutative_closure hk
  exact congrArg Subtype.val (hc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem locQu_sq {x : Equiv.Perm (Fin 2300)} (hx : x ∈ locQu) : x * x = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := mem_quTuple hx
    exact quPerm_sq hi
  | one => rw [mul_one]
  | mul x y hx hy ihx ihy =>
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [locQu_comm hy hx]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x hx ihx =>
    rw [← mul_inv_rev, ihx, inv_one]

theorem quPerm_eq {i : ℕ} (hi : i < 10) :
    quPerm i = prodList gTuple (quRecipe.getD i ([], 0)).1 ^ (quRecipe.getD i ([], 0)).2 := by
  have hl : ∀ j ∈ (quRecipe.getD i ([], 0)).1, j < gTuple.length := by
    intro j hj
    rw [gTuple_length]
    exact quRecipe_lt _ (getD_mem (by simpa [quRecipe] using hi)) j hj
  have h := rep_quPerm hi
  rw [quA_get hi] at h
  exact Rep.unique h (rep_powA (rep_prodArr repTuple_g hl) _)

theorem quPerm_mem_E {i : ℕ} (hi : i < 10) : quPerm i ∈ locE := by
  rw [quPerm_eq hi]
  exact pow_mem (prodList_mem (fun g hg => Subgroup.subset_closure hg) _) _

theorem locQu_le_E : locQu ≤ locE := by
  rw [locQu, Subgroup.closure_le]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_quTuple hx
  exact quPerm_mem_E hi

instance locQu_normal : (locQu.subgroupOf locE).Normal :=
  normal_of_conj_mem fun _ hc _ hx => quE_facts.conj_mem repTuple_qu repTuple_g allInv_gA
    eFacts.qConj hc hx

theorem quRec_shape : ChainShape quRec 1024 15 17 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] :=
  chainShape_of eFacts.qShape

@[expose] def chainQu : RawSchreierDatum 1024 :=
  rawOfArrays 1024 quRec.origArrs quRec.strongArrs quRec.baseArr quRec.wordArrs (by norm_num)
    (by rw [quRec_shape.origArrs_size, quRec_shape.strongArrs_size]; norm_num)
    (baseArr_lt_of_shape quRec_shape (by decide)) (baseArr_nodup_of_shape quRec_shape (by decide))

theorem chainQu_records : quRec.Records chainQu :=
  records_rawOfArrays_of_shape quRec_shape _ _ _ _ (by norm_num)

theorem card_chainQu : Nat.card chainQu.originalSubgroup = 1440 := by
  rw [card_originalSubgroup_of_chainOK chainQu_records.2.2 (by norm_num) eFacts.qOK]
  change (recordOrbits 1024 quRec).prod = _
  rw [beq_iff_eq.1 eFacts.qOrb]
  rfl

theorem chainQu_original : chainQu.originalSubgroup =
    Subgroup.closure {π | ∃ i < gTuple.length, permOfArr 1024 quP[i]! = π} := by
  rw [RawSchreierDatum.originalSubgroup]
  congr 1
  ext π
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  unfold chainQu
  rw [original_toList_rawOfArrays, quRec_shape.origArrs_size, gTuple_length, quRec_origArrs]

theorem card_conjNormal_Qu :
    Nat.card (MulAut.conjNormal (H := locQu.subgroupOf locE)).range = 1440 := by
  rw [← card_chainQu, chainQu_original]
  exact card_range_conjNormal quE_facts repTuple_qu locQu_le_E (hN := locQu_normal) repTuple_g
    allInv_gA eFacts.qConj fun i hi => by
      have := quRec_shape.orig_inv (i := i) (by rwa [gTuple_length] at hi)
      rwa [quRec_origArrs] at this

theorem locE_inf_centralizer_Qu :
    locE ⊓ Subgroup.centralizer (locQu : Set (Equiv.Perm (Fin 2300))) = locQu := by
  have h := card_inf_centralizer_mul locQu_le_E (hN := locQu_normal)
  change Nat.card ↥(locE ⊓ Subgroup.centralizer (locQu : Set (Equiv.Perm (Fin 2300)))) *
    Nat.card (MulAut.conjNormal (H := locQu.subgroupOf locE)).range = Nat.card locE at h
  rw [card_conjNormal_Qu, card_locE] at h
  have hcard : Nat.card ↥(locE ⊓ Subgroup.centralizer
      (locQu : Set (Equiv.Perm (Fin 2300)))) = 1024 :=
    Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 1440) (h.trans (by norm_num))
  have hle : locQu ≤ locE ⊓ Subgroup.centralizer (locQu : Set (Equiv.Perm (Fin 2300))) :=
    fun x hx => Subgroup.mem_inf.2 ⟨locQu_le_E hx, Subgroup.mem_centralizer_iff.2
      fun y hy => locQu_comm hy hx⟩
  exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hcard, card_locQu]))).symm

theorem locH3_inf_centralizer_Qu :
    locH3 ⊓ Subgroup.centralizer (locQu : Set (Equiv.Perm (Fin 2300))) = locQu := by
  rw [locH3_eq_E, locE_inf_centralizer_Qu]

theorem locQu_le_H3 : locQu ≤ locH3 := locQu_le_E.trans locE_le_H3

instance locQu_normal_H3 : (locQu.subgroupOf locH3).Normal := by
  rw [locH3_eq_E]
  exact locQu_normal

end CFSG.Sporadic.Co2Schreier

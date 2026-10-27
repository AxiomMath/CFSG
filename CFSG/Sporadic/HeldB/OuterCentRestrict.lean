module

public import CFSG.Sporadic.HeldB.OuterCentCheck
public import CFSG.Sporadic.HeldB.OuterArith

public noncomputable section

namespace CFSG.Sporadic.HeldB

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native Pointwise
open scoped commutatorElement

theorem rep_heU_inv :
    Rep 8330 (invCand 8330 heUArr) heAutU⁻¹ := by
  have h := permChk_spec heOuterCent_big.2.2.2.1
  rw [h.1.unique rep_heU] at h
  exact h.2

theorem heOuterLetters_length : heOuterLetters.length = 3 := rfl

theorem rep_heLetter
    (h : ℕ) (hh : h < heOuterLetters.length) :
    Rep 8330 heLetterArrs[h]! (heOuterLetters.getD h 1) ∧
      Rep 8330 (heLetterArrs.map (invCand 8330))[h]! (heOuterLetters.getD h 1)⁻¹ := by
  rw [heOuterLetters_length] at hh
  rw [heLetterArrs, heOuterLetters]
  interval_cases h
  · rw [arr3_get0, arr3_map_get0, list3_getD0]
    exact ⟨rep_heGen (by norm_num), rep_heGen_inv (k := 0) (by norm_num)⟩
  · rw [arr3_get1, arr3_map_get1, list3_getD1]
    exact ⟨rep_heGen (by norm_num), rep_heGen_inv (k := 1) (by norm_num)⟩
  · rw [arr3_get2, arr3_map_get2, list3_getD2]
    exact ⟨rep_heU, rep_heU_inv⟩

theorem heOuterLetters_W1 :
    lettersOK heOuterLetters.length heCentW1 = true := by
  rw [heOuterLetters_length]
  exact heOuterCent_big.1

theorem heOuterLetters_W2 :
    lettersOK heOuterLetters.length heCentW2 = true := by
  rw [heOuterLetters_length]
  exact heOuterCent_big.2.1

theorem rep_heC1 :
    Rep 8330 heCArrs[0]! heOuterC1 := by
  rw [heCArrs, arr2_get0, heOuterC1]
  exact rep_wordA_evalSignedWord (fun h hh => (rep_heLetter h hh).1)
    (fun h hh => (rep_heLetter h hh).2) heOuterLetters_W1

theorem rep_heC2 :
    Rep 8330 heCArrs[1]! heOuterC2 := by
  rw [heCArrs, arr2_get1, heOuterC2]
  exact rep_wordA_evalSignedWord (fun h hh => (rep_heLetter h hh).1)
    (fun h hh => (rep_heLetter h hh).2) heOuterLetters_W2

theorem heCs_length : [heOuterC1, heOuterC2].length = 2 := rfl

theorem rep_heCs
    (j : ℕ) (hj : j < [heOuterC1, heOuterC2].length) :
    Rep 8330 heCArrs[j]! ([heOuterC1, heOuterC2].getD j 1) ∧
      Rep 8330 (heCArrs.map (invCand 8330))[j]! ([heOuterC1, heOuterC2].getD j 1)⁻¹ := by
  have hp := heOuterCent_big.2.2.2.2.1
  rw [heCs_length] at hj
  have hr : Rep 8330 heCArrs[j]! ([heOuterC1, heOuterC2].getD j 1) := by
    interval_cases j
    · rw [list2_getD0]
      exact rep_heC1
    · rw [list2_getD1]
      exact rep_heC2
  refine ⟨hr, ?_⟩
  have hs := permChk_spec (hp j hj)
  rw [hs.1.unique hr] at hs
  have e : (heCArrs.map (invCand 8330))[j]! = invCand 8330 heCArrs[j]! := by
    rw [heCArrs]
    interval_cases j
    · rw [arr2_map_get0, arr2_get0]
    · rw [arr2_map_get1, arr2_get1]
  rw [e]
  exact hs.2

theorem rep_heD
    {j : ℕ} (hj : j < 3) : Rep 8330 (heDArr j) (heOuterDGen j) := by
  rw [heDArr, heOuterDGen]
  exact rep_wordA_evalSignedWord (fun h hh => (rep_heCs h hh).1) (fun h hh => (rep_heCs h hh).2)
    (by rw [heCs_length]; exact heOuterCent_big.2.2.1 j hj)

theorem heOuterC1_mem :
    heOuterC1 ∈ heP :=
  (mem_heP_iff_siftA rep_heC1).1 (heOuterCent_big.2.2.2.2.2.2.1 0 (by norm_num))

theorem heOuterC2_mem :
    heOuterC2 ∈ heP :=
  (mem_heP_iff_siftA rep_heC2).1 (heOuterCent_big.2.2.2.2.2.2.1 1 (by norm_num))

theorem heOuterC1_comm :
    heOuterC1 * heAutU = heAutU * heOuterC1 :=
  eq_of_eqA (rep_compA rep_heC1 rep_heU) (rep_compA rep_heU rep_heC1)
    (heOuterCent_big.2.2.2.2.2.1 0 (by norm_num))

theorem heOuterC2_comm :
    heOuterC2 * heAutU = heAutU * heOuterC2 :=
  eq_of_eqA (rep_compA rep_heC2 rep_heU) (rep_compA rep_heU rep_heC2)
    (heOuterCent_big.2.2.2.2.2.1 1 (by norm_num))

theorem heOuterC_le_centralizer :
    heOuterC ≤ heP ⊓ Subgroup.centralizer {heAutU} := by
  rw [heOuterC, Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨⟨heOuterC1_mem, Subgroup.mem_centralizer_singleton_iff.2 heOuterC1_comm⟩,
    ⟨heOuterC2_mem, Subgroup.mem_centralizer_singleton_iff.2 heOuterC2_comm⟩⟩

theorem heOuterC1_mem_C : heOuterC1 ∈ heOuterC := Subgroup.subset_closure (Set.mem_insert _ _)

theorem heOuterC2_mem_C : heOuterC2 ∈ heOuterC :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem heOuterDGen_mem_C (j : ℕ) : heOuterDGen j ∈ heOuterC := by
  rw [heOuterDGen]
  exact evalSignedWord_mem heOuterC (by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h
    · rw [h]
      exact heOuterC1_mem_C
    · rw [h]
      exact heOuterC2_mem_C) _

theorem heOuterD_le_C : heOuterD ≤ heOuterC := by
  rw [heOuterD, Subgroup.closure_le, Set.insert_subset_iff, Set.insert_subset_iff,
    Set.singleton_subset_iff]
  exact ⟨heOuterDGen_mem_C 0, heOuterDGen_mem_C 1, heOuterDGen_mem_C 2⟩

theorem heFixList :
    fixListOK 8330 98 heUArr heFixU = true := heOuterCent_big.2.2.2.2.2.2.2.1

theorem heFixPt_injective :
    Function.Injective (listPt 8330 heFixU (m := 98)) :=
  listPt_injective heFixList

theorem heFixPt_range :
    Set.range (listPt 8330 heFixU (m := 98)) = {x | heAutU x = x} :=
  fixListOK_range rep_heU heFixList

@[expose] def heSigma1P : Equiv.Perm (Fin 98) := permOrId 98 heSigma1

@[expose] def heSigma2P : Equiv.Perm (Fin 98) := permOrId 98 heSigma2

@[expose] def heTauP (j : ℕ) : Equiv.Perm (Fin 98) := permOrId 98 (heTauArr j)

theorem rep_heSigma1 : Rep 98 heSigma1 heSigma1P :=
  (permChk_spec heOuterCent_big.2.2.2.2.2.2.2.2.1).1

theorem rep_heSigma2 : Rep 98 heSigma2 heSigma2P :=
  (permChk_spec heOuterCent_big.2.2.2.2.2.2.2.2.2.1).1

theorem rep_heTau
    {j : ℕ} (hj : j < 3) : Rep 98 (heTauArr j) (heTauP j) :=
  (permChk_spec (heOuterCent_big.2.2.2.2.2.2.2.2.2.2.2.2 j hj).1).1

theorem rep_heTau_inv
    {j : ℕ} (hj : j < 3) : Rep 98 (invCand 98 (heTauArr j)) (heTauP j)⁻¹ :=
  (permChk_spec (heOuterCent_big.2.2.2.2.2.2.2.2.2.2.2.2 j hj).1).2

theorem heOuterC1_agree
    (k : Fin 98) :
    heOuterC1 (listPt 8330 heFixU k) = listPt 8330 heFixU (heSigma1P k) :=
  agreeOK_spec heFixList rep_heC1 rep_heSigma1 heOuterCent_big.2.2.2.2.2.2.2.2.2.2.1 k

theorem heOuterC2_agree
    (k : Fin 98) :
    heOuterC2 (listPt 8330 heFixU k) = listPt 8330 heFixU (heSigma2P k) :=
  agreeOK_spec heFixList rep_heC2 rep_heSigma2 heOuterCent_big.2.2.2.2.2.2.2.2.2.2.2.1 k

theorem heOuterD_agree
    {j : ℕ} (hj : j < 3) (k : Fin 98) :
    heOuterDGen j (listPt 8330 heFixU k) = listPt 8330 heFixU (heTauP j k) :=
  agreeOK_spec heFixList (rep_heD hj) (rep_heTau hj)
    (heOuterCent_big.2.2.2.2.2.2.2.2.2.2.2.2 j hj).2 k

theorem heOuterC_le_stabilizer :
    heOuterC ≤
      MulAction.stabilizer (Equiv.Perm (Fin 8330)) (Set.range (listPt 8330 heFixU (m := 98))) := by
  rw [heOuterC, Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨mem_stabilizer_of_agree heOuterC1_agree, mem_stabilizer_of_agree heOuterC2_agree⟩

@[expose] def heResF :
    heOuterC →* Equiv.Perm (Fin 98) :=
  restrictHom heFixPt_injective heOuterC heOuterC_le_stabilizer

theorem heResF_c1 :
    heResF ⟨heOuterC1, heOuterC1_mem_C⟩ = heSigma1P :=
  restrictHom_eq_of_agree heFixPt_injective heOuterC_le_stabilizer _ heOuterC1_agree

theorem heResF_c2 :
    heResF ⟨heOuterC2, heOuterC2_mem_C⟩ = heSigma2P :=
  restrictHom_eq_of_agree heFixPt_injective heOuterC_le_stabilizer _ heOuterC2_agree

theorem heResF_d
    {j : ℕ} (hj : j < 3) :
    heResF ⟨heOuterDGen j, heOuterDGen_mem_C j⟩ = heTauP j :=
  restrictHom_eq_of_agree heFixPt_injective heOuterC_le_stabilizer _ (heOuterD_agree hj)

theorem heQC_valid : ValidSchreier heQC := heOuterCent_small.1

theorem heQD_valid : ValidSchreier heQD := heOuterCent_small.2.2.1

theorem heQE_valid :
    ValidSchreier heQE := heOuterCent_small.2.2.2.2.1

theorem card_heQC : Nat.card heQC.originalSubgroup = 15120 := by
  rw [← heQC.orderCertificate_eq_card heQC_valid, heOuterCent_small.2.1]

theorem card_heQD : Nat.card heQD.originalSubgroup = 7560 := by
  rw [← heQD.orderCertificate_eq_card heQD_valid, heOuterCent_small.2.2.2.1]

theorem card_heQE : Nat.card heQE.originalSubgroup = 7560 := by
  rw [← heQE.orderCertificate_eq_card heQE_valid, heOuterCent_small.2.2.2.2.2.1]

theorem heQC_eq : heQC.originalSubgroup = Subgroup.closure {heSigma1P, heSigma2P} := by
  rw [heQC, certificate_originalSubgroup]
  congr 1
  ext g
  simp [heSigma1P, heSigma2P]

theorem heQD_eq : heQD.originalSubgroup = Subgroup.closure {heTauP 0, heTauP 1, heTauP 2} := by
  rw [heQD, certificate_originalSubgroup]
  congr 1
  ext g
  simp [heTauGens, heTauP]

theorem heEps_eq {i : ℕ} (hi : i < 2) :
    permOrId 98 (heEpsArr i) = ⁅heTauP i, heTauP 2⁆ := by
  have hrep : Rep 98 (heEpsArr i) ⁅heTauP i, heTauP 2⁆ := by
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    exact rep_compA (rep_heTau (by omega)) (rep_compA (rep_heTau (by norm_num))
      (rep_compA (rep_heTau_inv (by omega)) (rep_heTau_inv (by norm_num))))
  have hp : permChk 98 (heEpsArr i) = true := by
    interval_cases i
    · exact heOuterCent_small.2.2.2.2.2.2.1
    · exact heOuterCent_small.2.2.2.2.2.2.2.1
  exact (permChk_spec hp).1.unique hrep

theorem heQE_eq : heQE.originalSubgroup =
    Subgroup.closure {⁅heTauP 0, heTauP 2⁆, ⁅heTauP 1, heTauP 2⁆} := by
  rw [heQE, certificate_originalSubgroup, ← heEps_eq (by norm_num), ← heEps_eq (by norm_num)]
  congr 1
  ext g
  simp

theorem heResF_range :
    heResF.range = heQC.originalSubgroup := by
  rw [heResF, restrictHom_range heFixPt_injective heOuterC_le_stabilizer rfl, heQC_eq,
    ← heResF, ← heResF_c1, ← heResF_c2]
  congr 1
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    rcases hh with hh | hh
    · left
      congr 1
      exact Subtype.ext hh
    · right
      rw [Set.mem_singleton_iff] at hh ⊢
      congr 1
      exact Subtype.ext hh
  · rintro (rfl | rfl)
    · exact ⟨_, Or.inl rfl, rfl⟩
    · exact ⟨_, Or.inr (Set.mem_singleton _), rfl⟩

theorem subgroupOf_eq_closure {M : Type*} [Group M] {C H : Subgroup M} (hHC : H ≤ C)
    {S : Set M} (hS : H = Subgroup.closure S) :
    H.subgroupOf C = Subgroup.closure {c : C | (c : M) ∈ S} := by
  apply Subgroup.map_injective C.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, MonoidHom.map_closure, inf_eq_left.2 hHC, hS]
  congr 1
  ext g
  constructor
  · intro hg
    have hgC : g ∈ C := hHC (hS ▸ Subgroup.subset_closure hg)
    exact ⟨⟨g, hgC⟩, hg, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact hc

theorem card_eq_card_closure_image {M N : Type*} [Group M] [Group N] {C H : Subgroup M}
    (hHC : H ≤ C) (f : C →* N) (hf : Function.Injective f) {S : Set M}
    (hS : H = Subgroup.closure S) {T : Set N} (hT : f '' {c : C | (c : M) ∈ S} = T) :
    Nat.card H = Nat.card (Subgroup.closure T) := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHC).toEquiv,
    ← Subgroup.card_map_of_injective hf, subgroupOf_eq_closure hHC hS, MonoidHom.map_closure,
    hT]

end CFSG.Sporadic.HeldB

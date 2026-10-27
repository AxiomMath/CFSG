module

public import CFSG.Sporadic.SuzOddCore.ThreeLocalB

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Certificates.RawSchreierDatum CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Certificates.Native

theorem fullExtArrList_size : ∀ k, (fullExtArrList k).size = 8 + k
  | 0 => by simp [fullExtArrList, localStrongIdx]
  | k + 1 => by
    simp only [fullExtArrList, Array.size_push, fullExtArrList_size k]
    omega

theorem fullExtList_length : ∀ k, (fullExtList k).length = 8 + k
  | 0 => by simp [fullExtList, localStrongIdx]
  | k + 1 => by
    simp only [fullExtList, List.length_append, List.length_singleton, fullExtList_length k]
    omega

theorem fullExtArrList_prefix {j : ℕ} : ∀ k d, j < 8 + k →
    (fullExtArrList (k + d))[j]! = (fullExtArrList k)[j]!
  | _, 0, _ => rfl
  | k, d + 1, hj => by
    rw [← fullExtArrList_prefix k d hj, show k + (d + 1) = (k + d) + 1 by omega]
    simp only [fullExtArrList]
    have hlt : j < (fullExtArrList (k + d)).size := by rw [fullExtArrList_size]; omega
    rw [getElem!_pos _ j (by rw [Array.size_push]; omega), Array.getElem_push_lt hlt,
      ← getElem!_pos _ j hlt]

theorem fullExtList_prefix {j : ℕ} : ∀ k d, j < 8 + k →
    (fullExtList (k + d)).getD j 1 = (fullExtList k).getD j 1
  | _, 0, _ => rfl
  | k, d + 1, hj => by
    rw [← fullExtList_prefix k d hj, show k + (d + 1) = (k + d) + 1 by omega]
    simp only [fullExtList]
    rw [List.getD_append _ _ _ _ (by rw [fullExtList_length]; omega)]

theorem fullExtArrs_get {k j : ℕ} (hk : k ≤ 6) (hj : j < 8 + k) :
    (fullExtArrList k)[j]! = fullExtArrs[j]! := by
  have := fullExtArrList_prefix k (6 - k) hj
  rw [show k + (6 - k) = 6 by omega] at this
  exact this.symm

theorem fullExt_get {k j : ℕ} (hk : k ≤ 6) (hj : j < 8 + k) :
    (fullExtList k).getD j 1 = fullExt j := by
  have := fullExtList_prefix k (6 - k) hj
  rw [show k + (6 - k) = 6 by omega] at this
  exact this.symm

theorem localDerivs_letters {k : ℕ} (hk : k < 6) :
    lettersOK (8 + k) (localDerivs.getD (8 + k) []) = true := by
  have h := graphArrays_check.2.2.2.2.2.2.1
  simp only [derivsOK] at h
  have hs : 8 + k < localDerivs.size := by rw [graphArrays_check.2.2.2.2.2.2.2.1]; omega
  have := allLt_spec h hs
  simp only [show ¬ 8 + k < 8 by omega, decide_false, Bool.false_or] at this
  rwa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs, Option.getD_some,
    ← getElem!_pos localDerivs _ hs]

theorem localStrongIdx_eq : localStrongIdx = certStabIdx := rfl

theorem fullExtArrList_push (k : ℕ) :
    (fullExtArrList (k + 1))[8 + k]! =
      wordA 22880 (fullExtArrList k) ((fullExtArrList k).map (invCand 22880))
        (localDerivs.getD (8 + k) []) := by
  have hsz := fullExtArrList_size k
  simp only [fullExtArrList]
  rw [getElem!_pos _ (8 + k) (by rw [Array.size_push, hsz]; omega), Array.getElem_push]
  simp [hsz]

theorem fullExtList_push (k : ℕ) :
    (fullExtList (k + 1)).getD (8 + k) 1 =
      Quiver.SchreierGraph.evalWord (fun h : Fin (8 + k) => (fullExtList k).getD h 1)
        (toLetters (8 + k) (localDerivs.getD (8 + k) [])) := by
  simp only [fullExtList]
  rw [List.getD_append_right _ _ _ _ (by rw [fullExtList_length])]
  simp [fullExtList_length]

theorem rep_fullExtArrList :
    ∀ k, k ≤ 6 → ∀ j < 8 + k,
    Rep 22880 (fullExtArrList k)[j]! ((fullExtList k).getD j 1)
  | 0, _, j, hj => by
    have hj8 : j < localStrongIdx.length := by simp [localStrongIdx]; omega
    have e1 : (fullExtArrList 0)[j]! = certStrongArrs[localStrongIdx[j]]! := by
      rw [fullExtArrList, getElem!_pos _ j (by simpa using hj8), List.getElem_toArray,
        List.getElem_map]
    have e2 : (fullExtList 0).getD j 1 = suzS localStrongIdx[j] := by
      rw [fullExtList, List.getD_eq_getElem _ _ (by simpa using hj8), List.getElem_map]
    rw [e1, e2]
    have hmem : localStrongIdx[j] ∈ certStabIdx := by
      rw [← localStrongIdx_eq]
      exact List.getElem_mem hj8
    exact rep_certStrong (certStabIdx_lt hmem)
  | k + 1, hk, j, hj => by
    have ih := rep_fullExtArrList k (by omega)
    by_cases hjk : j < 8 + k
    · rw [fullExtArrList_prefix (j := j) k 1 hjk, fullExtList_prefix (j := j) k 1 hjk]
      exact ih j hjk
    · have hjeq : j = 8 + k := by omega
      subst hjeq
      rw [fullExtArrList_push, fullExtList_push]
      refine rep_wordA (fun h hh => ih h hh) (fun h hh => ?_) _ (localDerivs_letters (by omega))
      have hlt : h < (fullExtArrList k).size := by rw [fullExtArrList_size]; omega
      rw [getElem!_pos _ h (by simpa using hlt), Array.getElem_map, ← getElem!_pos _ h hlt]
      have hinv := (localChecks_facts.2.2.2.1 h (by omega)).1
      rw [← fullExtArrs_get (by omega : k ≤ 6) (by omega : h < 8 + k)] at hinv
      exact rep_inv_of_isInvA (ih h hh) hinv

theorem rep_fullExt
    {j : ℕ} (hj : j < 14) : Rep 22880 fullExtArrs[j]! (fullExt j) :=
  rep_fullExtArrList 6 le_rfl j hj

theorem fullExtList_mem : ∀ k, ∀ g ∈ fullExtList k, g ∈ suzH0
  | 0, g, hg => by
    simp only [fullExtList, List.mem_map] at hg
    obtain ⟨j, hj, rfl⟩ := hg
    exact Subgroup.subset_closure ⟨j, hj, rfl⟩
  | k + 1, g, hg => by
    simp only [fullExtList, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact fullExtList_mem k g hg
    · refine evalWord_mem (fun h => ?_) _
      rw [List.getD_eq_getElem?_getD]
      cases hh : (fullExtList k)[(h : ℕ)]? with
      | none => exact suzH0.one_mem
      | some a => exact fullExtList_mem k a (List.mem_of_getElem? hh)

theorem fullExt_mem (j : ℕ) : fullExt j ∈ suzH0 := by
  rw [fullExt, List.getD_eq_getElem?_getD]
  cases hh : (fullExtList 6)[j]? with
  | none => exact suzH0.one_mem
  | some a => exact fullExtList_mem 6 a (List.mem_of_getElem? hh)

@[expose] def fullExtH0 (j : ℕ) : suzH0 := ⟨fullExt j, fullExt_mem j⟩

theorem suzRho_fullExt
    {j : ℕ} (hj : j < 14) (hj' : j < localChain.strongCount) :
    suzRho (fullExtH0 j) = localChain.strong.get ⟨j, hj'⟩ := by
  have h2 := (tabRep_suzRho (fullExtH0 j) (rep_fullExt hj)).2
  rw [(localChecks_facts.2.2.2.1 j hj).2] at h2
  exact Rep.unique (n := 280) h2 (localChain_arrays.strong ⟨j, hj'⟩)

theorem tFullOf_size : (tFullOf fullExtArrs).size = 5 := by
  rw [tFullOf, Array.size_ofFn]

theorem tFullOf_get {i : ℕ} (hi : i < 5) :
    (tFullOf fullExtArrs)[i]! =
      wordA 22880 fullExtArrs (fullExtArrs.map (invCand 22880)) (sylowQuotWords.getD i []) := by
  rw [tFullOf, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem sylowQuotWords_letters
    (i : ℕ) : lettersOK 14 (sylowQuotWords.getD i []) = true := by
  rw [List.getD_eq_getElem?_getD]
  cases hh : sylowQuotWords[i]? with
  | none => rfl
  | some w => exact graphArrays_check.2.2.2.2.2.2.2.2.2.1 w (List.mem_of_getElem? hh)

theorem rep_suzSylowT
    {i : ℕ} (hi : i < 5) :
    Rep 22880 (tFullOf fullExtArrs)[i]! (suzSylowT i) := by
  rw [tFullOf_get hi]
  refine rep_wordA (fun h hh => rep_fullExt hh) (fun h hh => ?_) _ (sylowQuotWords_letters i)
  have hlt : h < fullExtArrs.size := by rw [localChecks_facts.1]; exact hh
  rw [getElem!_pos _ h (by simpa using hlt), Array.getElem_map, ← getElem!_pos _ h hlt]
  exact rep_inv_of_isInvA (rep_fullExt hh) (localChecks_facts.2.2.2.1 h hh).1

theorem suzSylowT_mem (i : ℕ) : suzSylowT i ∈ suzH0 :=
  evalWord_mem (ι := fun h : Fin 14 => fullExt h) (fun h => fullExt_mem h) _

@[expose] def sylowTH0 (i : ℕ) : suzH0 := ⟨suzSylowT i, suzSylowT_mem i⟩

@[expose] def zH0 :
    suzH0 := ⟨suzZ, suzZ_mem_suzH0⟩

@[expose] def suzS3H :
    Subgroup suzH0 :=
  Subgroup.closure (insert zH0 {g | ∃ i < 5, sylowTH0 i = g})

theorem suzS3H_map :
    suzS3H.map suzH0.subtype = suzS3 := by
  rw [suzS3H, MonoidHom.map_closure, suzS3, Set.image_insert_eq]
  congr 2
  ext g
  simp only [Set.mem_image, Set.mem_ofPred_eq, Subgroup.coe_subtype]
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨_, ⟨i, hi, rfl⟩, rfl⟩

theorem suzS3_le_suzH0 :
    suzS3 ≤ suzH0 := by
  rw [← suzS3H_map]
  exact Subgroup.map_subtype_le _

theorem suzS3_le_suzP :
    suzS3 ≤ suzP := suzS3_le_suzH0.trans suzH0_le_suzP

theorem suzZ_mem_suzS3 : suzZ ∈ suzS3 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem suzSylowT_mem_suzS3 {i : ℕ} (hi : i < 5) : suzSylowT i ∈ suzS3 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨i, hi, rfl⟩)

theorem suzQ_le_suzS3 : suzQ ≤ suzS3 := by
  rw [suzQ, Subgroup.zpowers_le]
  exact suzZ_mem_suzS3

@[expose] def sylowTBar :

    Set (Equiv.Perm (Fin 280)) := {g | ∃ i < 5, suzRho (sylowTH0 i) = g}

theorem suzS3H_map_rho :
    suzS3H.map suzRho = Subgroup.closure sylowTBar := by
  rw [suzS3H, MonoidHom.map_closure, Set.image_insert_eq]
  have hz : suzRho zH0 = 1 := by
    rw [← MonoidHom.mem_ker, ker_suzRho, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_zpowers _
  rw [hz, Subgroup.closure_insert_one]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_ofPred_eq, sylowTBar]
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨_, ⟨i, hi, rfl⟩, rfl⟩

theorem sylowCenterChecks_facts :
    enumOK 280 (tCompOf (tFullOf fullExtArrs)) (compactEnum (tFullOf fullExtArrs)) = true ∧
    (compactEnum (tFullOf fullExtArrs)).tabs.size = 729 ∧
    (∀ k < (compactEnum (tFullOf fullExtArrs)).tabs.size,
      (!(allLt 5 fun a => comp 280 (tCompOf (tFullOf fullExtArrs))[a]!
          (compactEnum (tFullOf fullExtArrs)).tabs[k]! ==
        comp 280 (compactEnum (tFullOf fullExtArrs)).tabs[k]!
          (tCompOf (tFullOf fullExtArrs))[a]!) ||
        (compactEnum (tFullOf fullExtArrs)).tabs[k]! == idTab 280 ||
        (compactEnum (tFullOf fullExtArrs)).tabs[k]! == centerCompact 3 ||
        (compactEnum (tFullOf fullExtArrs)).tabs[k]! ==
          comp 280 (centerCompact 3) (centerCompact 3)) = true) ∧
    (∀ r < 9, permOK 22880 (centerFull r) = true ∧
      eqA 22880 (centerFull r)
        (compA 22880 (powArr 22880 (centerFull 3) (r / 3)) (powArr 22880 zArr (r % 3))) = true) ∧
    (∀ r < 9, ∀ r' < 9, r < r' → eqA 22880 (centerFull r) (centerFull r') = false) ∧
    eqA 22880 (compA 22880 (centerFull 1) (centerFull 1)) (centerFull 2) = true ∧
    eqA 22880 (compA 22880 (centerFull 3) (centerFull 3)) (centerFull 6) = true ∧
    eqA 22880 (compA 22880 (centerFull 4) (centerFull 4)) (centerFull 8) = true ∧
    eqA 22880 (compA 22880 (centerFull 5) (centerFull 5)) (centerFull 7) = true ∧
    eqA 22880 (centerFull 3) (tFullOf fullExtArrs)[1]! = true ∧
    restrictArr localDomain (centerFull 3) = centerCompact 3 ∧
    (centerCompact 3 == idTab 280) = false ∧
    eqA 22880 (compA 22880 (centerFull 3) zArr) (compA 22880 zArr (centerFull 3)) = true ∧
    (∀ a < 5,
      eqA 22880 (compA 22880 (centerFull 3) (tFullOf fullExtArrs)[a]!)
        (compA 22880 (tFullOf fullExtArrs)[a]! (centerFull 3)) = true ∧
      eqA 22880 (compA 22880 zArr (tFullOf fullExtArrs)[a]!)
        (compA 22880 (tFullOf fullExtArrs)[a]! zArr) = true) ∧
    eqA 22880 (powArr 22880 (centerFull 3) 3) (idA 22880) = true := by
  have h := threeLocal_parts.2.2.1
  simp only [sylowCenterChecks, Bool.and_eq_true, beq_iff_eq, allLt_iff, Bool.not_eq_true',
    and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  refine ⟨h1, h2, fun k hk => ?_, h4, fun r hr r' hr' hrr' => ?_, h6, h7, h8, h9, h10, h11, ?_,
    h13, h14, h15⟩
  · exact h3 k hk
  · have := h5 r hr r' hr'
    simpa [hrr'] using this
  · exact h12

theorem compact_enumerates :
    Enumerates (Subgroup.closure sylowTBar) (compactEnum (tFullOf fullExtArrs)).tabs.toList := by
  refine enumerates_closure ?_ ?_ sylowCenterChecks_facts.1
  · rintro _ ⟨i, hi, rfl⟩
    refine ⟨i, by simpa [tCompOf, tFullOf_size] using hi, ?_⟩
    rw [tCompOf, getElem!_pos _ i (by rw [Array.size_map, tFullOf_size]; exact hi),
      Array.getElem_map, ← getElem!_pos _ i (by rw [tFullOf_size]; exact hi)]
    exact tabRep_suzRho _ (rep_suzSylowT hi)
  · intro i hi
    have hi5 : i < 5 := by simpa [tCompOf, tFullOf_size] using hi
    refine ⟨_, ⟨i, hi5, rfl⟩, ?_⟩
    rw [tCompOf, getElem!_pos _ i (by rw [Array.size_map, tFullOf_size]; exact hi5),
      Array.getElem_map, ← getElem!_pos _ i (by rw [tFullOf_size]; exact hi5)]
    exact tabRep_suzRho _ (rep_suzSylowT hi5)

theorem card_compact :
    Nat.card (Subgroup.closure sylowTBar) = 729 := by
  rw [compact_enumerates.card, Array.length_toList, sylowCenterChecks_facts.2.1]

theorem card_eq_map_mul_ker {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H)
    (K : Subgroup G) : Nat.card K = Nat.card (K.map f) * Nat.card (f.ker.subgroupOf K) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (f.comp K.subtype).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (f.comp K.subtype)).toEquiv,
    MonoidHom.range_comp, Subgroup.range_subtype] at h
  rw [h, ← MonoidHom.comap_ker]
  rfl

theorem card_suzS3H :
    Nat.card suzS3H = 2187 := by
  have hker : suzRho.ker ≤ suzS3H := by
    rw [ker_suzRho]
    intro g hg
    rw [Subgroup.mem_subgroupOf] at hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hg
    have : g = zH0 ^ k := Subtype.ext (by rw [SubgroupClass.coe_zpow]; exact hk.symm)
    rw [this]
    exact suzS3H.zpow_mem (Subgroup.subset_closure (Set.mem_insert _ _)) _
  rw [card_eq_map_mul_ker suzRho suzS3H, suzS3H_map_rho, card_compact,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker).toEquiv, card_ker_suzRho]

theorem card_suzS3 :
    Nat.card suzS3 = 2187 := by
  rw [← suzS3H_map, Subgroup.card_map_of_injective suzH0.subtype_injective, card_suzS3H]

theorem suzP_card_factorization :
    (Nat.card suzP).factorization 3 = 7 := by
  rw [suzP_card, show (448345497600 : ℕ) = 3 ^ 7 * 205004800 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

@[expose] def suzSylowThree :
    Sylow 3 suzP :=
  Sylow.ofCard (suzS3.subgroupOf suzP) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe suzS3_le_suzP).toEquiv, card_suzS3,
      suzP_card_factorization]
    norm_num)

theorem suzSylowThree_coe :
    (suzSylowThree : Subgroup suzP) = suzS3.subgroupOf suzP := rfl

theorem centerFullPerm_three :
    centerFullPerm 3 = suzSylowT 1 :=
  (eqA_iff (rep_centerFull (by norm_num)) (rep_suzSylowT (by norm_num))).1
    sylowCenterChecks_facts.2.2.2.2.2.2.2.2.2.1

theorem rep_powArr' {n : ℕ} {t : Array ℕ} {T : Equiv.Perm (Fin n)} (ht : Rep n t T) (k : ℕ) :
    Rep n (powArr n t k) (T ^ k) := rep_powArr ht k

theorem centerFullPerm_eq
    {r : ℕ} (hr : r < 9) :
    centerFullPerm r = centerFullPerm 3 ^ (r / 3) * suzZ ^ (r % 3) :=
  (eqA_iff (rep_centerFull hr) (rep_compA (rep_powArr' (rep_centerFull (by norm_num)) _)
    (rep_powArr' rep_zArr _))).1 (sylowCenterChecks_facts.2.2.2.1 r hr).2

theorem centerFullPerm_three_mem :
    centerFullPerm 3 ∈ suzS3 := by
  rw [centerFullPerm_three]
  exact suzSylowT_mem_suzS3 (by norm_num)

theorem centerFullPerm_mem
    {r : ℕ} (hr : r < 9) : centerFullPerm r ∈ suzS3 := by
  rw [centerFullPerm_eq hr]
  exact suzS3.mul_mem (suzS3.pow_mem centerFullPerm_three_mem _) (suzS3.pow_mem suzZ_mem_suzS3 _)

theorem commute_of_gens {x : Equiv.Perm (Fin 22880)} (hz : x * suzZ = suzZ * x)
    (ht : ∀ i < 5, x * suzSylowT i = suzSylowT i * x) : ∀ y ∈ suzS3, x * y = y * x := by
  have hle : suzS3 ≤ Subgroup.centralizer {x} := by
    rw [suzS3, Subgroup.closure_le]
    rintro _ (rfl | ⟨i, hi, rfl⟩)
    · exact Subgroup.mem_centralizer_singleton_iff.2 hz.symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 (ht i hi).symm
  intro y hy
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm

theorem centerFullPerm_three_comm_z :
    centerFullPerm 3 * suzZ = suzZ * centerFullPerm 3 :=
  (eqA_iff (rep_compA (rep_centerFull (by norm_num)) rep_zArr)
    (rep_compA rep_zArr (rep_centerFull (by norm_num)))).1
    sylowCenterChecks_facts.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem centerFullPerm_three_comm_t
    {i : ℕ} (hi : i < 5) :
    centerFullPerm 3 * suzSylowT i = suzSylowT i * centerFullPerm 3 :=
  (eqA_iff (rep_compA (rep_centerFull (by norm_num)) (rep_suzSylowT hi))
    (rep_compA (rep_suzSylowT hi) (rep_centerFull (by norm_num)))).1
    (sylowCenterChecks_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i hi).1

theorem suzZ_comm_t
    {i : ℕ} (hi : i < 5) : suzZ * suzSylowT i = suzSylowT i * suzZ :=
  (eqA_iff (rep_compA rep_zArr (rep_suzSylowT hi)) (rep_compA (rep_suzSylowT hi) rep_zArr)).1
    (sylowCenterChecks_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i hi).2

theorem suzZ_central :
    ∀ y ∈ suzS3, suzZ * y = y * suzZ :=
  commute_of_gens rfl fun _ hi => suzZ_comm_t hi

theorem centerFullPerm_three_central :
    ∀ y ∈ suzS3, centerFullPerm 3 * y = y * centerFullPerm 3 :=
  commute_of_gens centerFullPerm_three_comm_z fun _ hi => centerFullPerm_three_comm_t hi

theorem centerFullPerm_central
    {r : ℕ} (hr : r < 9) :
    ∀ y ∈ suzS3, centerFullPerm r * y = y * centerFullPerm r := by
  intro y hy
  rw [centerFullPerm_eq hr]
  have h1 := (Commute.pow_left (centerFullPerm_three_central y hy) (r / 3))
  have h2 := (Commute.pow_left (suzZ_central y hy) (r % 3))
  exact (h1.mul_left h2).eq

theorem centerFullPerm_three_pow :
    centerFullPerm 3 ^ 3 = 1 :=
  (eqA_iff (rep_powArr' (rep_centerFull (by norm_num)) 3) rep_idA).1
    sylowCenterChecks_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2

@[expose] def cH0 :

    suzH0 := ⟨centerFullPerm 3, suzS3_le_suzH0 centerFullPerm_three_mem⟩

theorem tabRep_rho_c :
    TabRep (centerCompact 3) (suzRho cH0) := by
  have := tabRep_suzRho cH0 (rep_centerFull (by norm_num))
  rwa [sylowCenterChecks_facts.2.2.2.2.2.2.2.2.2.2.1] at this

theorem rho_c_ne_one :
    suzRho cH0 ≠ 1 := by
  intro h
  have := (tabRep_rho_c.beq_iff TabRep.idTab).2 h
  rw [sylowCenterChecks_facts.2.2.2.2.2.2.2.2.2.2.2.1] at this
  exact Bool.false_ne_true this

theorem mem_center_records
    {x : Equiv.Perm (Fin 22880)} (hx : x ∈ suzS3)
    (hc : ∀ y ∈ suzS3, x * y = y * x) : ∃ r < 9, centerFullPerm r = x := by
  have hxH : x ∈ suzH0 := suzS3_le_suzH0 hx
  set x' : suzH0 := ⟨x, hxH⟩
  have hx' : x' ∈ suzS3H := by
    have : x ∈ suzS3H.map suzH0.subtype := by rw [suzS3H_map]; exact hx
    obtain ⟨y, hy, hyx⟩ := this
    rwa [show y = x' from Subtype.ext hyx] at hy
  have hρ : suzRho x' ∈ Subgroup.closure sylowTBar := by
    rw [← suzS3H_map_rho]
    exact Subgroup.mem_map_of_mem _ hx'
  obtain ⟨t, ht, hrep⟩ := compact_enumerates.complete _ hρ
  obtain ⟨k, hk, rfl⟩ := exists_getElem!_of_mem ht
  have hcomm : (allLt 5 fun a => comp 280 (tCompOf (tFullOf fullExtArrs))[a]!
      (compactEnum (tFullOf fullExtArrs)).tabs[k]! ==
        comp 280 (compactEnum (tFullOf fullExtArrs)).tabs[k]!
          (tCompOf (tFullOf fullExtArrs))[a]!) = true := by
    rw [allLt_iff]
    intro a ha
    have hta : TabRep (tCompOf (tFullOf fullExtArrs))[a]! (suzRho (sylowTH0 a)) := by
      rw [tCompOf, getElem!_pos _ a (by rw [Array.size_map, tFullOf_size]; exact ha),
        Array.getElem_map, ← getElem!_pos _ a (by rw [tFullOf_size]; exact ha)]
      exact tabRep_suzRho _ (rep_suzSylowT ha)
    rw [(hta.comp hrep).beq_iff (hrep.comp hta), ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (hc _ (suzSylowT_mem_suzS3 ha)).symm
  have h3 := sylowCenterChecks_facts.2.2.1 k hk
  rw [hcomm] at h3
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at h3
  obtain ⟨a, ha, hρa⟩ : ∃ a < 3, suzRho x' = suzRho cH0 ^ a := by
    rcases h3 with (h | h) | h
    · exact ⟨0, by norm_num, by rw [pow_zero]; exact (hrep.beq_iff TabRep.idTab).1 h⟩
    · exact ⟨1, by norm_num, by rw [pow_one]; exact (hrep.beq_iff tabRep_rho_c).1 h⟩
    · exact ⟨2, by norm_num, by
        rw [pow_two]; exact (hrep.beq_iff (tabRep_rho_c.comp tabRep_rho_c)).1 h⟩
  have hker : x' * (cH0 ^ a)⁻¹ ∈ suzRho.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hρa, mul_inv_cancel]
  rw [ker_suzRho, Subgroup.mem_subgroupOf] at hker
  obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.1 hker
  set b' := (b % 3).toNat with hb'
  have hb'lt : b' < 3 := by omega
  have hzb : suzZ ^ b = suzZ ^ b' := by
    rw [zpow_eq_zpow_emod' b suzZ_pow_three, ← zpow_natCast, hb',
      Int.toNat_of_nonneg (Int.emod_nonneg b (by norm_num))]
    rfl
  have hx : x = suzZ ^ b' * centerFullPerm 3 ^ a := by
    have e : ((x' * (cH0 ^ a)⁻¹ : suzH0) : Equiv.Perm (Fin 22880)) =
        x * (centerFullPerm 3 ^ a)⁻¹ := by simp [x', cH0]
    rw [← hzb, hb, e]
    group
  refine ⟨3 * a + b', by omega, ?_⟩
  rw [centerFullPerm_eq (by omega), show (3 * a + b') / 3 = a by omega,
    show (3 * a + b') % 3 = b' by omega, hx]
  exact (Commute.pow_pow (show Commute (centerFullPerm 3) suzZ from centerFullPerm_three_comm_z)
    a b').eq

end CFSG.Sporadic.SuzOddCore

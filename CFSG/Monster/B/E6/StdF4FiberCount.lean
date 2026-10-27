module

public import CFSG.Monster.B.E6.StdF4FiberGroups

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Overlap (K)
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.Classical

theorem mem_closure_iff_jElt {S : Finset (Fin 4)} {idx : List ℕ} (hlt : ∀ i ∈ idx, i < 48)
    (hletters : ∀ i ∈ idx, ∀ k ∈ E6Folded.jWords.getD i [], k ∈ S)
    (hone : E6Folded.idCode ∈ idx.map fun i => E6Folded.jCodes.getD i [])
    (hclosed : ∀ i ∈ idx, ∀ k ∈ S, E6Folded.compose (E6Folded.gc k) (E6Folded.jCodes.getD i []) ∈
      idx.map fun i => E6Folded.jCodes.getD i [])
    (w : Equiv.Perm E6Folded.Λ) :
    w ∈ Subgroup.closure (E6Folded.gen '' (S : Set (Fin 4))) ↔ ∃ i ∈ idx, w = E6Folded.jElt i := by
  have hcw : ∀ m < 48, E6Folded.codeWord (E6Folded.jWords.getD m []) = E6Folded.jCodes.getD m [] :=
    fun m hm => (E6Folded.code_wordProd _).symm.trans (E6Folded.code_jElt hm)
  have hiff := E6Folded.mem_closure_iff_of_list (S := (S : Set (Fin 4)))
    (ws := idx.map fun i => E6Folded.jWords.getD i [])
    (cs := idx.map fun i => E6Folded.jCodes.getD i []) (by simp)
    (fun i hi => by
      have hi' : i < idx.length := by simpa using hi
      rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getD_eq_getElem _ _ hi,
        List.getElem_map, List.getElem_map]
      exact hcw _ (hlt _ (List.getElem_mem _)))
    (fun l hl k hk => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hl
      exact Finset.mem_coe.2 (hletters i hi k hk))
    hone
    (fun i hi k hk => by
      rw [List.getD_eq_getElem _ _ hi, List.getElem_map]
      exact hclosed _ (List.getElem_mem _) k (Finset.mem_coe.1 hk))
    w
  rw [hiff, List.mem_map]
  constructor
  · rintro ⟨i, hi, e⟩
    refine ⟨i, hi, E6Folded.code_injective ?_⟩
    rw [E6Folded.code_jElt (hlt i hi), e]
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, (E6Folded.code_jElt (hlt i hi)).symm⟩

theorem qWeight_jElt {i : ℕ} (hi : i < 48) :
    E6Folded.qWeight (E6Folded.jElt i) = E6Folded.wordWeight (E6Folded.jWords.getD i []) := by
  have h := E6Folded.qWeight_elt (a := 23) (by norm_num) hi
  rw [E6Folded.tElt_23, one_mul] at h
  rw [h, E6Folded.pairWeight, E6Folded.tWords_theta]
  simp

theorem finsum_parabolic_of_list
    {S : Finset (Fin 4)} {idx : List ℕ} (hlt : ∀ i ∈ idx, i < 48)
    (hnd : idx.Nodup)
    (hS : ∀ w, w ∈ Subgroup.closure (E6Folded.gen '' (S : Set (Fin 4))) ↔
      ∃ i ∈ idx, w = E6Folded.jElt i) :
    ∑ᶠ w ∈ (ncs.parabolic (S : Set (Fin 4)) : Set NW), weylWeight ncs E6Folded.letterWeight w =
      (idx.map fun i => E6Folded.wordWeight (E6Folded.jWords.getD i [])).sum := by
  have himage : (Subgroup.closure (E6Folded.gen '' (S : Set (Fin 4))) :
      Set (Equiv.Perm E6Folded.Λ)) = weylPerm '' (ncs.parabolic (S : Set (Fin 4)) : Set NW) := by
    rw [← Subgroup.coe_map, map_parabolic]
  have himage' : (Subgroup.closure (E6Folded.gen '' (S : Set (Fin 4))) :
      Set (Equiv.Perm E6Folded.Λ)) = E6Folded.jElt '' (idx.toFinset : Set ℕ) := by
    ext w
    rw [SetLike.mem_coe, hS w]
    simp only [Set.mem_image, Finset.mem_coe, List.mem_toFinset]
    exact ⟨fun ⟨i, hi, e⟩ => ⟨i, hi, e.symm⟩, fun ⟨i, hi, e⟩ => ⟨i, hi, e.symm⟩⟩
  have hinj : Set.InjOn E6Folded.jElt (idx.toFinset : Set ℕ) := fun i hi m hm h =>
    E6Folded.jElt_inj (hlt i (List.mem_toFinset.1 hi)) (hlt m (List.mem_toFinset.1 hm)) h
  calc ∑ᶠ w ∈ (ncs.parabolic (S : Set (Fin 4)) : Set NW), weylWeight ncs E6Folded.letterWeight w
      = ∑ᶠ w ∈ (ncs.parabolic (S : Set (Fin 4)) : Set NW), E6Folded.qWeight (weylPerm w) :=
        finsum_mem_congr rfl fun w _ => weylWeight_eq_qWeight w
    _ = ∑ᶠ x ∈ weylPerm '' (ncs.parabolic (S : Set (Fin 4)) : Set NW), E6Folded.qWeight x :=
        (finsum_mem_image weylPerm_injective.injOn).symm
    _ = ∑ᶠ x ∈ E6Folded.jElt '' (idx.toFinset : Set ℕ), E6Folded.qWeight x := by
        rw [← himage, himage']
    _ = ∑ᶠ i ∈ (idx.toFinset : Set ℕ), E6Folded.qWeight (E6Folded.jElt i) :=
        finsum_mem_image hinj
    _ = ∑ i ∈ idx.toFinset, E6Folded.qWeight (E6Folded.jElt i) := finsum_mem_coe_finset _ _
    _ = ∑ i ∈ idx.toFinset, E6Folded.wordWeight (E6Folded.jWords.getD i []) :=
        Finset.sum_congr rfl fun i hi => qWeight_jElt (hlt i (List.mem_toFinset.1 hi))
    _ = _ := List.sum_toFinset _ hnd

@[expose] def idx23 : List ℕ := [0, 2, 3, 7, 8, 14]

@[expose] def idx12 : List ℕ := [0, 1, 2, 4, 6, 9, 12, 16]

theorem idx23_checks : (∀ i ∈ idx23, i < 48) ∧ idx23.Nodup ∧
    (∀ i ∈ idx23, ∀ k ∈ E6Folded.jWords.getD i [], k ∈ ({2, 3} : Finset (Fin 4))) ∧
    E6Folded.idCode ∈ idx23.map (fun i => E6Folded.jCodes.getD i []) ∧
    (∀ i ∈ idx23, ∀ k ∈ ({2, 3} : Finset (Fin 4)),
      E6Folded.compose (E6Folded.gc k) (E6Folded.jCodes.getD i []) ∈
        idx23.map fun i => E6Folded.jCodes.getD i []) ∧
    (idx23.map fun i => E6Folded.wordWeight (E6Folded.jWords.getD i [])).sum = 105 := by
  decide +kernel

theorem idx12_checks : (∀ i ∈ idx12, i < 48) ∧ idx12.Nodup ∧
    (∀ i ∈ idx12, ∀ k ∈ E6Folded.jWords.getD i [], k ∈ ({1, 2} : Finset (Fin 4))) ∧
    E6Folded.idCode ∈ idx12.map (fun i => E6Folded.jCodes.getD i []) ∧
    (∀ i ∈ idx12, ∀ k ∈ ({1, 2} : Finset (Fin 4)),
      E6Folded.compose (E6Folded.gc k) (E6Folded.jCodes.getD i []) ∈
        idx12.map fun i => E6Folded.jCodes.getD i []) ∧
    (idx12.map fun i => E6Folded.wordWeight (E6Folded.jWords.getD i [])).sum = 135 := by
  decide +kernel

theorem finsum_parabolic_23 :
    ∑ᶠ w ∈ (ncs.parabolic (({2, 3} : Finset (Fin 4)) : Set (Fin 4)) : Set NW),
      weylWeight ncs E6Folded.letterWeight w = 105 := by
  obtain ⟨hlt, hnd, hl, hone, hcl, hsum⟩ := idx23_checks
  rw [finsum_parabolic_of_list hlt hnd (mem_closure_iff_jElt hlt hl hone hcl), hsum]

theorem finsum_parabolic_12 :
    ∑ᶠ w ∈ (ncs.parabolic (({1, 2} : Finset (Fin 4)) : Set (Fin 4)) : Set NW),
      weylWeight ncs E6Folded.letterWeight w = 135 := by
  obtain ⟨hlt, hnd, hl, hone, hcl, hsum⟩ := idx12_checks
  rw [finsum_parabolic_of_list hlt hnd (mem_closure_iff_jElt hlt hl hone hcl), hsum]

theorem leviParabolic_firstJ :
    leviParabolic firstJ firstJ = stdLevi firstJ := by
  refine le_antisymm (leviParabolic_le_stdLevi two_mem_firstJ subset_rfl) fun l hl => ?_
  have hlP := stdLevi_le_nativeParabolic two_mem_firstJ hl
  have h := (mem_nativeParabolic_iff two_mem_firstJ subset_rfl ⟨l, hlP⟩).mp hlP
  rwa [leviProj_of_mem two_mem_firstJ hl] at h

theorem card_nativeParabolic_firstJ :
    Nat.card (nativeParabolic firstJ) = 3 * 2 ^ 36 * 93555 := by
  rw [card_nativeParabolic, firstJ_eq_J, finsum_parabolic_J_weylWeight]

theorem card_stdRadical_firstJ :
    Nat.card (stdRadical firstJ) = 2 ^ 21 := by
  have h := card_nativeParabolic_eq (I := firstJ) subset_rfl
  rw [card_nativeParabolic_firstJ, leviParabolic_firstJ, card_stdLevi_firstJ] at h
  have e : (3 * 2 ^ 36 * 93555 : ℕ) = 2 ^ 21 * 9196830720 := by norm_num
  rw [e] at h
  exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h).symm

@[expose] def fibLeviCard : Fin 5 → ℕ :=
  ![9196830720, 10321920, 13271040, 10321920, 9196830720]

abbrev fibLevi
    (d : Fin 5) : Subgroup (ModGL Tag.E6 K) :=
  leviParabolic firstJ (fibIF d : Set (Fin 4))

theorem fibIF_subset (d : Fin 5) : (fibIF d : Set (Fin 4)) ⊆ firstJ := by
  intro i hi
  have h : ∀ d : Fin 5, ∀ i ∈ fibIF d, i = 1 ∨ i = 2 ∨ i = 3 := by decide
  rcases h d i (Finset.mem_coe.1 hi) with rfl | rfl | rfl
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)

theorem card_leviParabolic_of_census
    {S : Finset (Fin 4)} (hS : (S : Set (Fin 4)) ⊆ firstJ)
    {N : ℕ} (hN : ∑ᶠ w ∈ (ncs.parabolic (S : Set (Fin 4)) : Set NW),
      weylWeight ncs E6Folded.letterWeight w = N) :
    Nat.card (leviParabolic firstJ (S : Set (Fin 4))) = 3 * 2 ^ 15 * N := by
  have h := card_nativeParabolic_eq hS
  rw [card_nativeParabolic, hN, card_stdRadical_firstJ] at h
  have e : (3 * 2 ^ 36 * N : ℕ) = 2 ^ 21 * (3 * 2 ^ 15 * N) := by ring
  rw [e] at h
  exact (Nat.eq_of_mul_eq_mul_left (by norm_num) h).symm

theorem card_fibLevi
    (d : Fin 5) : Nat.card (fibLevi d) = fibLeviCard d := by
  have hJ : ((({1, 2, 3} : Finset (Fin 4)) : Set (Fin 4))) = firstJ := by
    ext i
    simp [firstJ]
  have h0 : Nat.card (leviParabolic firstJ ((({1, 2, 3} : Finset (Fin 4)) : Set (Fin 4)))) =
      9196830720 := by
    rw [hJ, leviParabolic_firstJ, card_stdLevi_firstJ]
  have h1 : Nat.card (leviParabolic firstJ ((({2, 3} : Finset (Fin 4)) : Set (Fin 4)))) =
      10321920 :=
    (card_leviParabolic_of_census (fibIF_subset 1) finsum_parabolic_23).trans (by norm_num)
  have h2 : Nat.card (leviParabolic firstJ ((({1, 2} : Finset (Fin 4)) : Set (Fin 4)))) =
      13271040 :=
    (card_leviParabolic_of_census (fibIF_subset 2) finsum_parabolic_12).trans (by norm_num)
  fin_cases d
  · exact h0
  · exact h1
  · exact h2
  · exact h1
  · exact h0

end CFSG.Monster.B.E6.StdF4

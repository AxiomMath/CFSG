module

public import CFSG.Sporadic.SuzOddCore.ChainOrder
public import CFSG.Sporadic.SuzOddCore.CertChainCheck
public import CFSG.Sporadic.SuzOddCore.Family

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Certificates.RawSchreierDatum CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Perm CFSG.Perm.Native

theorem rep_certStrong
    {j : ℕ} (hj : j < 10) : Rep 22880 certStrongArrs[j]! (suzS j) := by
  rw [certStrongArrs_get hj]
  exact rep_suzS hj

theorem certArr_size
    {k : ℕ} (hk : k < 12) : (certArr k).size = 22880 := by
  have := arrays_check.1 k hk
  simp only [permOK, Bool.and_eq_true, beq_iff_eq] at this
  exact this.1

theorem rep_certStrongInv
    {j : ℕ} (hj : j < 10) : Rep 22880 certStrongInvs[j]! (suzS j)⁻¹ := by
  have he : certStrongInvs[j]! = invCand 22880 (certArr (j + 2)) := by
    rw [certStrongInvs, getElem!_pos _ j (by rw [Array.size_map, certStrongArrs_size]; exact hj),
      Array.getElem_map, ← getElem!_pos certStrongArrs j (by rw [certStrongArrs_size]; exact hj),
      certStrongArrs_get hj]
  rw [he]
  exact (rep_permC (Bool.and_eq_true_iff.1 (arrays_check.1 (j + 2) (by omega))).2).2

theorem lettersOK_certDerivs {j : ℕ} (hj : j < 10) (h2 : 2 ≤ j) :
    lettersOK j certDerivs[j]! = true := by
  have h := arrays_check.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [derivsOK] at h
  have hjs : j < certDerivs.size := by rw [show certDerivs.size = 10 from rfl]; exact hj
  have := allLt_spec h hjs
  simpa [show ¬ j < 2 by omega] using this

theorem certChain_eqns :
    ChainEqns certChain where
  init j := by
    have hj : (j : ℕ) < 2 := j.2
    rw [certChain_strong_get, certChain_original_get, Fin.val_castLE]
    obtain ⟨h0, h1, -⟩ := certChain_check
    interval_cases h : (j : ℕ)
    · change permC 22880 (certArr 2) = permC 22880 certGenArrs[0]!
      rw [certGenArrs_get_zero, h0]
    · change permC 22880 (certArr 3) = permC 22880 certGenArrs[1]!
      rw [certGenArrs_get_one, h1]
  words j hj := by
    have hj10 : (j : ℕ) < 10 := j.2
    have hj2 : 2 ≤ (j : ℕ) := hj
    rw [certChain_strong_get]
    change suzS j = schreierWordValue certChain.strong.get j _ (toLetters j certDerivs[(j : ℕ)]!)
    have hw := rep_wordA (n := 22880) (S := certStrongArrs) (Sinv := certStrongInvs)
      (gs := suzS) (j := j) (fun h hh => rep_certStrong (by omega))
      (fun h hh => rep_certStrongInv (by omega)) certDerivs[(j : ℕ)]!
      (lettersOK_certDerivs hj10 hj2)
    have he := eq_of_eqA (rep_certStrong hj10) hw ((certChain_check.2.2.1) j hj10 hj2)
    rw [he]
    unfold schreierWordValue
    congr 1
    funext h
    exact (certChain_strong_get ⟨(h : ℕ), by have := h.2; omega⟩).symm
  terminal s hs := by
    exfalso
    obtain ⟨hstrong, hfix⟩ := (certChain.mem_levelGenerators_iff _ s).1 hs
    obtain ⟨j, rfl⟩ := (schreier_vector_mem_toList_iff_get certChain.strong s).1 hstrong
    rw [certChain_strong_get] at hfix
    have hj : (j : ℕ) < 10 := j.2
    have hidx := certChain_check.2.2.2.1 6 le_rfl
    have hnot : (j : ℕ) ∉ levelIdx certStrongArrs certBaseNat.toArray 6 := by
      rw [hidx]; simp [certLevelIdx]
    apply hnot
    rw [levelIdx, List.mem_filter, List.mem_range, certStrongArrs_size]
    refine ⟨hj, ?_⟩
    rw [fixesFirst, allLt_iff]
    intro k hk
    rw [beq_iff_eq]
    have hb : certBaseNat.toArray[k]! = k := by
      interval_cases k <;> rfl
    rw [hb, (rep_certStrong hj).apply (by omega : k < 22880)]
    have hk' : (⟨k, by omega⟩ : Fin 22880) ∈ certChain.base.toList.take certChain.baseCount := by
      rw [List.take_of_length_le (by simp), certChain_base_toList, List.mem_iff_getElem]
      exact ⟨k, by simp; omega, Fin.ext (by interval_cases k <;> rfl)⟩
    exact congrArg Fin.val (hfix _ hk')

theorem certLevelLetters_spec {i l : ℕ} (hl : l ∈ certLevelLetters i) :
    ∃ j ∈ certLevelIdx i, l = 2 * j ∨ l = 2 * j + 1 := by
  simp only [certLevelLetters, List.mem_toArray, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false] at hl
  exact hl

theorem certLevelIdx_lt {i j : ℕ} (hj : j ∈ certLevelIdx i) : j < 10 := by
  simp only [certLevelIdx] at hj
  rcases i with _ | _ | _ | _ | _ | _ | _ | i <;> simp at hj <;> omega

theorem certLetters_get {l : ℕ} (hl : l < 20) :
    certLetters[l]! = if l % 2 = 0 then (certStrongArrs[l / 2]!).map UInt32.ofNat
      else (certStrongInvs[l / 2]!).map UInt32.ofNat := by
  rw [certLetters, getElem!_pos _ l (by simp; exact hl), Array.getElem_ofFn]

theorem rep_certLetters
    {l : ℕ} (hl : l < 20) :
    CFSG.Sporadic.Th.Rep 22880 certLetters[l]! (pairG suzS l) := by
  rw [certLetters_get hl, pairG]
  have hj : l / 2 < 10 := by omega
  have hsz : (certStrongArrs[l / 2]!).size = 22880 := by
    rw [certStrongArrs_get hj]; exact certArr_size (by omega)
  split_ifs
  · exact th_rep_of_rep (rep_certStrong hj) hsz fun x hx =>
      (certChain_check.2.2.2.2.2.2.1 _ hj x hx).1
  · exact th_rep_of_rep (rep_certStrongInv hj) (certChain_check.2.2.2.2.2.2.2 _ hj)
      fun x hx => (certChain_check.2.2.2.2.2.2.1 _ hj x hx).2

theorem certTree_facts
    {i : ℕ} (hi : i < 6) :
    TreeFacts 22880 (certTree i) (certLevelLetters i) (pairG suzS) (certBaseNat.getD i 0) := by
  refine treeOK_facts (fun l hl => ?_) (certChain_check.2.2.2.2.1 i hi)
  obtain ⟨j, hj, rfl | rfl⟩ := certLevelLetters_spec hl
  · exact rep_certLetters (by have := certLevelIdx_lt hj; omega)
  · exact rep_certLetters (by have := certLevelIdx_lt hj; omega)

theorem certLetters_le
    {i : ℕ} (hi : i < 6) :
    lettersGroup (certLevelLetters i) (pairG suzS) ≤ certChain.levelSubgroup i := by
  rw [lettersGroup, Subgroup.closure_le]
  rintro _ ⟨l, hl, rfl⟩
  obtain ⟨j, hj, hlj⟩ := certLevelLetters_spec hl
  have hj10 := certLevelIdx_lt hj
  have hmem : suzS j ∈ certChain.levelSubgroup i := by
    apply Subgroup.subset_closure
    apply (certChain.mem_levelGenerators_iff i (suzS j)).2
    refine ⟨?_, fun b hb => ?_⟩
    · rw [← certChain_strong_get ⟨j, hj10⟩]
      exact schreier_vector_get_mem_toList _ _
    · have hidx := certChain_check.2.2.2.1 i (by omega)
      have hjm : j ∈ levelIdx certStrongArrs certBaseNat.toArray i := by rw [hidx]; exact hj
      rw [levelIdx, List.mem_filter, fixesFirst, allLt_iff] at hjm
      rw [certChain_base_toList] at hb
      have hbv : (b : ℕ) < i ∧ (b : ℕ) < 6 := by
        obtain ⟨m, hm, hmb⟩ := List.mem_take_iff_getElem.1 hb
        have hm' := Nat.lt_min.1 hm
        simp only [List.length_cons, List.length_nil] at hm'
        have hbm : (b : ℕ) = m := by
          rw [← hmb]
          have h6 : m < 6 := hm'.2
          interval_cases m <;> rfl
        omega
      have := hjm.2 b hbv.1
      rw [beq_iff_eq] at this
      have hb' : certBaseNat.toArray[(b : ℕ)]! = b := by
        have h6 := hbv.2
        interval_cases h : (b : ℕ) <;> rfl
      rw [hb', (rep_certStrong hj10).apply b.2] at this
      exact Fin.ext this
  rcases hlj with rfl | rfl
  · simp only [pairG, show 2 * j % 2 = 0 by omega, ↓reduceIte, show 2 * j / 2 = j by omega]
    exact hmem
  · simp only [pairG, show (2 * j + 1) % 2 ≠ 0 by omega, ↓reduceIte,
      show (2 * j + 1) / 2 = j by omega]
    exact (certChain.levelSubgroup i).inv_mem hmem

theorem vector_getElem?_toList {α : Type*} {k : ℕ} (v : Vector α k) {l : List α}
    (h : v.toList = l) (i : Fin k) : l[(i : ℕ)]? = some (v.get i) := by
  subst h
  simp [Vector.get, Vector.getElem_toList]

theorem certChain_base_get (i : Fin certChain.baseCount) :
    ((certChain.base.get i : Fin 22880) : ℕ) = certBaseNat.getD i 0 := by
  have hi : (i : ℕ) < 6 := lt_of_lt_of_eq i.2 certChain_baseCount
  have h1 := vector_getElem?_toList certChain.base certChain_base_toList i
  have h2 : ∀ m < 6, (([0, 1, 2, 3, 4, 5] : List (Fin 22880))[m]?).map Fin.val =
      some (certBaseNat.getD m 0) := by
    intro m hm
    interval_cases m <;> rfl
  have h3 := h2 i hi
  rw [h1, Option.map_some, Option.some.injEq] at h3
  exact h3

theorem certChain_orbit_card_ge
    (i : Fin certChain.baseCount) :
    certOrbitSizes.getD i 0 ≤ Nat.card (certChain.orbitPoints i) := by
  have hi : (i : ℕ) < 6 := lt_of_lt_of_eq i.2 certChain_baseCount
  have hT := certTree_facts hi
  rw [← certChain_check.2.2.2.2.2.1 i hi, ← hT.card_orbit, certChain.orbitPoints_eq_orbit i]
  have hroot : (⟨certBaseNat.getD (i : ℕ) 0, hT.r_lt⟩ : Fin 22880) = certChain.base.get i :=
    Fin.ext (certChain_base_get i).symm
  rw [hroot]
  apply Nat.card_mono (Set.toFinite _)
  rintro _ ⟨⟨g, hg⟩, rfl⟩
  exact ⟨⟨g, certLetters_le hi hg⟩, rfl⟩

theorem certChain_valid :
    ValidSchreier certChain := by
  refine certChain_eqns.validSchreier ?_
  rw [certChain_originalSubgroup, suzP_card]
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin certChain.baseCount)),
      certOrbitSizes.getD i 0 ≤ Nat.card (certChain.orbitPoints i) :=
    fun i _ => certChain_orbit_card_ge i
  refine le_trans ?_ (Finset.prod_le_prod hle)
  rw [Fin.prod_univ_eq_prod_range (fun i => certOrbitSizes.getD i 0) certChain.baseCount,
    certChain_baseCount]
  decide

end CFSG.Sporadic.SuzOddCore

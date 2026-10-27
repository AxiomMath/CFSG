module

public import CFSG.LocalAnalysis.StandardType.TitsOvergroupSound

public section

namespace CFSG.StandardType.TitsOvergroup

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
open CFSG.StandardType.SylowPair

variable {D : PairData} {S : List (Equiv.Perm (Fin D.n))}

@[expose] def pairPVals (D : PairData) (S : List (Equiv.Perm (Fin D.n))) :
    List (Equiv.Perm (Fin D.n)) :=
  D.pW.map (wordVal S)

@[expose] def pairConjGens (D : PairData) (g gi : Tab) : Array Tab :=
  (pGens D).map (conjTab D.n g gi)

@[expose] def pairConjVals (D : PairData) (S : List (Equiv.Perm (Fin D.n)))
    (g : Equiv.Perm (Fin D.n)) : List (Equiv.Perm (Fin D.n)) :=
  (pairPVals D S).map (fun x => g * x * g⁻¹)

@[expose] def pairLetterVals (D : PairData) (S : List (Equiv.Perm (Fin D.n)))
    (g : Equiv.Perm (Fin D.n)) : List (Equiv.Perm (Fin D.n)) :=
  pairPVals D S ++ pairConjVals D S g

theorem getD_append_left {α : Type*} (A B : Array α) (d : α) {j : ℕ} (hj : j < A.size) :
    (A ++ B).getD j d = A.getD j d := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_append_left hj]

theorem getD_append_right {α : Type*} (A B : Array α) (d : α) {j : ℕ} (hj : A.size ≤ j) :
    (A ++ B).getD j d = B.getD (j - A.size) d := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_append_right hj]

theorem getD_map_array {α : Type*} (A : Array α) (f : α → α) (d : α) {k : ℕ}
    (hk : k < A.size) : (A.map f).getD k d = f (A.getD k d) := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_eq_getElem hk]
  rfl

theorem list_getD_map_conj (L : List (Equiv.Perm (Fin D.n))) (g : Equiv.Perm (Fin D.n))
    (j : ℕ) : (L.map (fun x => g * x * g⁻¹)).getD j 1 = g * L.getD j 1 * g⁻¹ := by
  simpa using List.getD_map (l := L) (n := j) (d := (1 : Equiv.Perm (Fin D.n)))
    (f := fun x => g * x * g⁻¹)

theorem pairLetters_rep (hS : Sound D S) (hinvs : invsOK D.n (repT D) (repI D) = true)
    {i : ℕ} (hi : i < D.repW.length) :
    ∀ j, TabRep ((pairLetters D (repT D)[i + 1]! (repI D)[i + 1]!).getD j (idTab D.n))
      ((pairLetterVals D S ((pairReps D S).getD (i + 1) 1)).getD j 1) := by
  intro j
  have hgt : TabRep ((repT D)[i + 1]!) ((pairReps D S).getD (i + 1) 1) := by
    have hsz : (repT D).size = D.repW.length + 1 := by simp [repT]
    have hlt : i + 1 < (repT D).size := by rw [hsz]; omega
    have h1 := repT_rep hS (i + 1)
    rwa [show (repT D).getD (i + 1) (idTab D.n) = (repT D)[i + 1]! by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt, Option.getD_some,
        getElem!_pos (repT D) (i + 1) hlt]] at h1
  have hgit : TabRep ((repI D)[i + 1]!) ((pairReps D S).getD (i + 1) 1)⁻¹ := by
    have hsz : (repI D).size = D.repW.length + 1 := by simp [repI, repT]
    have hlt : i + 1 < (repI D).size := by rw [hsz]; omega
    have h1 := repI_rep hS hinvs (i + 1)
    rwa [show (repI D).getD (i + 1) (idTab D.n) = (repI D)[i + 1]! by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt, Option.getD_some,
        getElem!_pos (repI D) (i + 1) hlt]] at h1
  have hm : (pGens D).size = (pairPVals D S).length := by simp [pGens, pairPVals]
  by_cases hj : j < D.pW.length
  · have hAl : (pairLetters D (repT D)[i + 1]! (repI D)[i + 1]!).getD j (idTab D.n)
        = (pGens D).getD j (idTab D.n) := by
      rw [pairLetters]
      exact getD_append_left _ _ _ (by rw [hm]; simpa [pairPVals] using hj)
    have hAl2 : (pairLetterVals D S ((pairReps D S).getD (i + 1) 1)).getD j 1
        = (pairPVals D S).getD j 1 := by
      rw [pairLetterVals]
      exact List.getD_append _ _ _ _ (by simpa [pairPVals] using hj)
    rw [hAl, hAl2]
    exact pGens_rep hS j
  · have hjle : D.pW.length ≤ j := Nat.le_of_not_lt hj
    have hAl : (pairLetters D (repT D)[i + 1]! (repI D)[i + 1]!).getD j (idTab D.n)
        = (pairConjGens D (repT D)[i + 1]! (repI D)[i + 1]!).getD
            (j - (pGens D).size) (idTab D.n) := by
      rw [pairLetters]
      exact getD_append_right _ _ _ (by rw [hm]; simpa [pairPVals] using hjle)
    have hAl' : (pairConjGens D (repT D)[i + 1]! (repI D)[i + 1]!).getD
          (j - (pGens D).size) (idTab D.n)
        = (pairConjGens D (repT D)[i + 1]! (repI D)[i + 1]!).getD
            (j - (pairPVals D S).length) (idTab D.n) := by
      rw [hm]
    have hAl2 : (pairLetterVals D S ((pairReps D S).getD (i + 1) 1)).getD j 1
        = (pairConjVals D S ((pairReps D S).getD (i + 1) 1)).getD
            (j - (pairPVals D S).length) 1 := by
      rw [pairLetterVals]
      exact List.getD_append_right _ _ _ _ (by simpa [pairPVals] using hjle)
    rw [hAl, hAl', hAl2]
    set k : ℕ := j - (pairPVals D S).length with hkdef
    by_cases hk : k < (pairPVals D S).length
    · have hB : (pairConjGens D (repT D)[i + 1]! (repI D)[i + 1]!).getD k (idTab D.n)
          = conjTab D.n (repT D)[i + 1]! (repI D)[i + 1]!
              ((pGens D).getD k (idTab D.n)) := by
        rw [pairConjGens]
        exact getD_map_array _ _ _ (by rw [hm]; exact hk)
      have hM : (pairConjVals D S ((pairReps D S).getD (i + 1) 1)).getD k 1
          = (pairReps D S).getD (i + 1) 1 * (pairPVals D S).getD k 1 *
              ((pairReps D S).getD (i + 1) 1)⁻¹ := by
        rw [pairConjVals]
        exact list_getD_map_conj _ _ _
      rw [hB, hM]
      exact hgt.conjTab (pGens_rep hS k) hgit
    · have hkle : (pairPVals D S).length ≤ k := Nat.le_of_not_lt hk
      have hB : (pairConjGens D (repT D)[i + 1]! (repI D)[i + 1]!).getD k (idTab D.n)
          = idTab D.n := by
        rw [pairConjGens, Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_none (by rw [Array.size_map, hm]; exact hkle)]
        rfl
      have hM : (pairConjVals D S ((pairReps D S).getD (i + 1) 1)).getD k 1 = 1 := by
        rw [pairConjVals, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_none hkle]
        rfl
      rw [hB, hM]
      exact TabRep.idTab

theorem pairLetters_inv_rep (hS : Sound D S) (hinvs : invsOK D.n (repT D) (repI D) = true)
    {i : ℕ} (hi : i < D.repW.length)
    (hInv : invsOK D.n (pairLetters D (repT D)[i + 1]! (repI D)[i + 1]!)
      ((pairLetters D (repT D)[i + 1]! (repI D)[i + 1]!).map (invTab D.n)) = true) :
    ∀ j, TabRep (((pairLetters D (repT D)[i + 1]! (repI D)[i + 1]!).map (invTab D.n)).getD
        j (idTab D.n)) ((pairLetterVals D S ((pairReps D S).getD (i + 1) 1)).getD j 1)⁻¹ := by
  have hAl := pairLetters_rep hS hinvs hi
  simp only [invsOK, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true] at hInv
  exact CFSG.AGLEmbedding.MaxD2.inv_rep_of_check hAl hInv.1 hInv.2

theorem pairG_le_pairClosure (hS : Sound D S) (hinvs : invsOK D.n (repT D) (repI D) = true)
    (h : checkGen D = true) {i : ℕ} (hi : i < D.repW.length) (hk : D.kind[i]! = 0) :
    pairG D S ≤ pairClosure (pairP D S) ((pairReps D S).getD (i + 1) 1) := by
  have hgen := h
  simp only [checkGen, Bool.and_eq_true, beq_iff_eq] at hgen
  obtain ⟨⟨-, -⟩, hall⟩ := hgen
  rw [allBelow_eq_true] at hall
  have hk' := hall i hi
  rw [show (D.kind[i]! != 0) = false by simp [hk]] at hk'
  rw [Bool.false_or] at hk'
  simp only [Bool.and_eq_true, beq_iff_eq, allBelow_eq_true] at hk'
  obtain ⟨-, hInvs, hwords⟩ := hk'
  have hAl := pairLetters_rep hS hinvs hi
  have hAli := pairLetters_inv_rep hS hinvs hi hInvs
  unfold pairG
  rw [Subgroup.closure_le]
  intro s hs
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
  have hjT : j < D.gT.size := by rw [← hS.len]; exact hj
  have hrepj : TabRep (D.gT[j]!) (S[j]) := by
    have h1 := hS.rep j
    rw [show D.gT.getD j (idTab D.n) = D.gT[j]! by
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hjT, Option.getD_some,
            getElem!_pos D.gT j hjT],
        show S.getD j 1 = S[j] by simp [hj]] at h1
    exact h1
  have hword := hwords j hjT
  have hwordrep := wordT_rep (S := pairLetterVals D S ((pairReps D S).getD (i + 1) 1))
      (pairLetters D (repT D)[i + 1]! (repI D)[i + 1]!)
      ((pairLetters D (repT D)[i + 1]! (repI D)[i + 1]!).map (invTab D.n)) hAl hAli
      ((D.genW[i]!)[j]!)
  have hEq : wordVal (pairLetterVals D S ((pairReps D S).getD (i + 1) 1))
      ((D.genW[i]!)[j]!) = S[j] := by
    rw [hword] at hwordrep
    exact hwordrep.perm_eq hrepj
  rw [← hEq]
  refine wordVal_mem (pairLetterVals D S ((pairReps D S).getD (i + 1) 1))
    (pairClosure (pairP D S) ((pairReps D S).getD (i + 1) 1)) ?_ ((D.genW[i]!)[j]!)
  intro x hx
  rw [pairLetterVals] at hx
  rcases List.mem_append.1 hx with hx | hx
  · exact Subgroup.mem_sup_left (Subgroup.subset_closure hx)
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact Subgroup.mem_sup_right ⟨y, Subgroup.subset_closure hy, by simp [MulAut.conj_apply]⟩

theorem pairReps_mem_side (hS : Sound D S) (hSide : checkSide D = true)
    (h : checkSideMem D = true) {i k : ℕ} (hi : i < D.repW.length) (hk : D.kind[i]! = k + 1) :
    (pairReps D S).getD (i + 1) 1 ∈ pairSide D S k := by
  have hmem := h
  simp only [checkSideMem, allBelow_eq_true] at hmem
  have hk' := hmem i hi
  rw [show (D.kind[i]! == 0) = false by simp [hk]] at hk'
  rw [Bool.false_or] at hk'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hk'
  obtain ⟨hklt, hfound⟩ := hk'
  have hk1 : D.kind[i]! - 1 = k := by omega
  rw [hk1] at hfound hklt
  have hSide' := hSide
  simp only [checkSide, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true] at hSide'
  obtain ⟨-, hSideAll⟩ := hSide'
  obtain ⟨henum, -⟩ := hSideAll k hklt
  have hrepT : TabRep ((repT D)[i + 1]!) ((pairReps D S).getD (i + 1) 1) := by
    have hsz : (repT D).size = D.repW.length + 1 := by simp [repT]
    have hlt : i + 1 < (repT D).size := by rw [hsz]; omega
    have h1 := repT_rep hS (i + 1)
    rw [show (repT D).getD (i + 1) (idTab D.n) = (repT D)[i + 1]! by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt, Option.getD_some,
        getElem!_pos (repT D) (i + 1) hlt]] at h1
    exact h1
  exact (CFSG.AGLEmbedding.MaxD2.found_iff_mem henum (enum_pairSide hS hSide hklt) hrepT).1 hfound

theorem pairSide_le_pairClosure (hS : Sound D S) (hinvs : invsOK D.n (repT D) (repI D) = true)
    {sg : List (List (List Int))} (h : checkSideGen D sg = true) {i k : ℕ}
    (hi : i < D.repW.length) (hk : D.kind[i]! = k + 1) :
    pairSide D S k ≤ pairClosure (pairP D S) ((pairReps D S).getD (i + 1) 1) := by
  have hgen := h
  simp only [checkSideGen, Bool.and_eq_true, beq_iff_eq] at hgen
  obtain ⟨-, hall⟩ := hgen
  rw [allBelow_eq_true] at hall
  have hk' := hall i hi
  rw [show (D.kind[i]! == 0) = false by simp [hk]] at hk'
  rw [Bool.false_or] at hk'
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, allBelow_eq_true] at hk'
  obtain ⟨⟨hklt, -⟩, hInvs, hwords⟩ := hk'
  have hk1 : D.kind[i]! - 1 = k := by omega
  rw [hk1] at hklt hwords
  have hAl := pairLetters_rep hS hinvs hi
  have hAli := pairLetters_inv_rep hS hinvs hi hInvs
  unfold pairSide
  rw [Subgroup.closure_le]
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hj' : j < (D.sideW.getD k []).length := by simpa using hj
  have hjS : j < (sideGens D k).size := by
    rw [show (sideGens D k).size = (D.sideW.getD k []).length by simp [sideGens]]
    exact hj'
  have hsidej : TabRep ((sideGens D k)[j]!)
      (((D.sideW.getD k []).map (wordVal S))[j]) := by
    have h1 := sideGens_rep hS k j
    rw [show (sideGens D k).getD j (idTab D.n) = (sideGens D k)[j]! by
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hjS, Option.getD_some,
            getElem!_pos (sideGens D k) j hjS],
        show ((D.sideW.getD k []).map (wordVal S)).getD j 1
            = ((D.sideW.getD k []).map (wordVal S))[j] by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
          rfl] at h1
    exact h1
  have hword := hwords j hjS
  have hwordrep := wordT_rep (S := pairLetterVals D S ((pairReps D S).getD (i + 1) 1))
      (pairLetters D (repT D)[i + 1]! (repI D)[i + 1]!)
      ((pairLetters D (repT D)[i + 1]! (repI D)[i + 1]!).map (invTab D.n)) hAl hAli
      ((sg[i]!)[j]!)
  have hEq : wordVal (pairLetterVals D S ((pairReps D S).getD (i + 1) 1)) ((sg[i]!)[j]!)
      = ((D.sideW.getD k []).map (wordVal S))[j] := by
    rw [hword] at hwordrep
    exact hwordrep.perm_eq hsidej
  rw [← hEq]
  refine wordVal_mem (pairLetterVals D S ((pairReps D S).getD (i + 1) 1))
    (pairClosure (pairP D S) ((pairReps D S).getD (i + 1) 1)) ?_ ((sg[i]!)[j]!)
  intro x hx
  rw [pairLetterVals] at hx
  rcases List.mem_append.1 hx with hx | hx
  · exact Subgroup.mem_sup_left (Subgroup.subset_closure hx)
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact Subgroup.mem_sup_right ⟨y, Subgroup.subset_closure hy, by simp [MulAut.conj_apply]⟩

theorem pairN_le_normalizer_side (hS : Sound D S) (hSide : checkSide D = true)
    (h : checkSideNorm D = true) {k : ℕ} (hk : k < D.sideW.length) :
    pairN D S ≤ Subgroup.normalizer (pairSide D S k : Set (Equiv.Perm (Fin D.n))) := by
  have hNorm := h
  simp only [checkSideNorm, allBelow_eq_true] at hNorm
  have hnk := hNorm k hk
  unfold pairN
  rw [Subgroup.closure_le]
  intro a ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
  have hj' : j < D.nW.length := by simpa using hj
  refine CFSG.AGLEmbedding.MaxD2.mem_normalizer_of_conj_gens
    (A := {g | g ∈ (D.sideW.getD k []).map (wordVal S)}) ?_
  intro s hs
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
  have hi' : i < (D.sideW.getD k []).length := by simpa using hi
  have hja : j < (nGens D).size := by simpa [nGens] using hj'
  have hia : i < (sideGens D k).size := by simpa [sideGens] using hi'
  exact (conj_mem_of_normalOK (enum_pairSide hS hSide hk) hnk hja hia
    (CFSG.AGLEmbedding.MaxD2.rep_getElem!_of_words S D.gT (giT D) hS.rep hS.gi D.nW hj')
    (CFSG.AGLEmbedding.MaxD2.rep_getElem!_of_words S D.gT (giT D) hS.rep hS.gi
      (D.sideW.getD k []) hi')).1

end CFSG.StandardType.TitsOvergroup

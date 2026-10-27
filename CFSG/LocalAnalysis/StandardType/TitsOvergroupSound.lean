module

public import CFSG.LocalAnalysis.StandardType.TitsOvergroupCheck
public import CFSG.LocalAnalysis.StandardType.SylowPairOvergroup
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.MaxD2PermSound
public import CFSG.Open.Defs

public section

namespace CFSG.StandardType.TitsOvergroup

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
open CFSG.AGLEmbedding.MaxD2 (dcoset conjStab)
open CFSG.StandardType.SylowPair

@[expose] def pairG (D : PairData) (S : List (Equiv.Perm (Fin D.n))) :
    Subgroup (Equiv.Perm (Fin D.n)) :=
  Subgroup.closure {g | g ∈ S}

@[expose] def pairP (D : PairData) (S : List (Equiv.Perm (Fin D.n))) :
    Subgroup (Equiv.Perm (Fin D.n)) :=
  Subgroup.closure {g | g ∈ D.pW.map (wordVal S)}

@[expose] def pairN (D : PairData) (S : List (Equiv.Perm (Fin D.n))) :
    Subgroup (Equiv.Perm (Fin D.n)) :=
  Subgroup.closure {g | g ∈ D.nW.map (wordVal S)}

@[expose] def pairSide (D : PairData) (S : List (Equiv.Perm (Fin D.n))) (k : ℕ) :
    Subgroup (Equiv.Perm (Fin D.n)) :=
  Subgroup.closure {g | g ∈ (D.sideW.getD k []).map (wordVal S)}

@[expose] def pairReps (D : PairData) (S : List (Equiv.Perm (Fin D.n))) :
    List (Equiv.Perm (Fin D.n)) :=
  1 :: D.repW.map (wordVal S)

structure Sound (D : PairData) (S : List (Equiv.Perm (Fin D.n))) : Prop where
  rep : ∀ j, TabRep (D.gT.getD j (idTab D.n)) (S.getD j 1)
  len : S.length = D.gT.size
  inv : checkInv D = true
  card : Nat.card (pairG D S) = D.gOrder

variable {D : PairData} {S : List (Equiv.Perm (Fin D.n))}

theorem Sound.gi (hS : Sound D S) :
    ∀ j, TabRep ((giT D).getD j (idTab D.n)) (S.getD j 1)⁻¹ := by
  have h := hS.inv
  simp only [checkInv, allBelow_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  exact CFSG.AGLEmbedding.MaxD2.inv_rep_of_check (S := S) (gs := D.gT) (gi := giT D)
    hS.rep (by simp [giT]) h

theorem pairP_le_pairG : pairP D S ≤ pairG D S := by
  unfold pairP
  rw [Subgroup.closure_le]
  rintro _ hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact wordVal_mem S (pairG D S) (fun _ hg => Subgroup.subset_closure hg) w

theorem pairN_le_pairG : pairN D S ≤ pairG D S := by
  unfold pairN
  rw [Subgroup.closure_le]
  rintro _ hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact wordVal_mem S (pairG D S) (fun _ hg => Subgroup.subset_closure hg) w

theorem pairSide_le_pairG (k : ℕ) : pairSide D S k ≤ pairG D S := by
  unfold pairSide
  rw [Subgroup.closure_le]
  rintro _ hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact wordVal_mem S (pairG D S) (fun _ hg => Subgroup.subset_closure hg) w

theorem enum_pairP (hS : Sound D S) (h : checkP D = true) :
    Enumerates (pairP D S) (pEnum D).tabs.toList := by
  simp only [checkP, Bool.and_eq_true] at h
  exact CFSG.AGLEmbedding.MaxD2.enumerates_of_words S D.gT (giT D) hS.rep hS.gi D.pW h.1

theorem card_pairP (hS : Sound D S) (h : checkP D = true) :
    Nat.card (pairP D S) = D.pOrder := by
  have h' := h
  simp only [checkP, Bool.and_eq_true, beq_iff_eq] at h'
  rw [(enum_pairP hS h).card, Array.length_toList, h'.2]

theorem enum_pairN (hS : Sound D S) (h : checkN D = true) :
    Enumerates (pairN D S) (nEnum D).tabs.toList := by
  simp only [checkN, Bool.and_eq_true] at h
  exact CFSG.AGLEmbedding.MaxD2.enumerates_of_words S D.gT (giT D) hS.rep hS.gi D.nW h.1

theorem card_pairN (hS : Sound D S) (h : checkN D = true) :
    Nat.card (pairN D S) = D.nOrder := by
  have h' := h
  simp only [checkN, Bool.and_eq_true, beq_iff_eq] at h'
  rw [(enum_pairN hS h).card, Array.length_toList, h'.2]

theorem enum_pairSide (hS : Sound D S) (h : checkSide D = true) {k : ℕ} (hk : k < D.sideW.length) :
    Enumerates (pairSide D S k) (sideEnum D k).tabs.toList := by
  simp only [checkSide, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true] at h
  exact CFSG.AGLEmbedding.MaxD2.enumerates_of_words S D.gT (giT D) hS.rep hS.gi
    (D.sideW.getD k []) (h.2 k hk).1

theorem card_pairSide (hS : Sound D S) (h : checkSide D = true) {k : ℕ} (hk : k < D.sideW.length) :
    Nat.card (pairSide D S k) = D.sideOrder.getD k 0 := by
  have h' := h
  simp only [checkSide, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true] at h'
  rw [(enum_pairSide hS h hk).card, Array.length_toList, (h'.2 k hk).2]

theorem pairN_le_normalizer (hS : Sound D S) (hP : checkP D = true)
    (hNorm : checkNormal D = true) :
    pairN D S ≤ Subgroup.normalizer (pairP D S : Set (Equiv.Perm (Fin D.n))) := by
  unfold pairN
  rw [Subgroup.closure_le]
  intro a ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
  have hj' : j < D.nW.length := by simpa using hj
  refine CFSG.AGLEmbedding.MaxD2.mem_normalizer_of_conj_gens
    (A := {g | g ∈ D.pW.map (wordVal S)}) ?_
  intro s hs
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
  have hi' : i < D.pW.length := by simpa using hi
  have hja : j < (nGens D).size := by simp [nGens, hj']
  have hia : i < (pGens D).size := by simp [pGens, hi']
  exact (conj_mem_of_normalOK (enum_pairP hS hP) hNorm hja hia
    (CFSG.AGLEmbedding.MaxD2.rep_getElem!_of_words S D.gT (giT D) hS.rep hS.gi D.nW hj')
    (CFSG.AGLEmbedding.MaxD2.rep_getElem!_of_words S D.gT (giT D) hS.rep hS.gi D.pW hi')).1

theorem invsOK_of_checkCover (h : checkCover D = true) :
    invsOK D.n (repT D) (repI D) = true := by
  simp only [checkCover, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨_, _⟩, hinvs⟩, _⟩, _⟩ := h
  exact hinvs

theorem repT_rep (hS : Sound D S) :
    ∀ i, TabRep ((repT D).getD i (idTab D.n)) ((pairReps D S).getD i 1) := by
  exact CFSG.AGLEmbedding.MaxD2.rep_cons_array
    (CFSG.AGLEmbedding.MaxD2.rep_map_words S D.gT (giT D) hS.rep hS.gi D.repW)

theorem repI_rep (hS : Sound D S) (hinvs : invsOK D.n (repT D) (repI D) = true) :
    ∀ j, TabRep ((repI D).getD j (idTab D.n)) ((pairReps D S).getD j 1)⁻¹ := by
  simp only [invsOK, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true] at hinvs
  exact CFSG.AGLEmbedding.MaxD2.inv_rep_of_check (gs := repT D) (gi := repI D)
    (repT_rep hS) hinvs.1 hinvs.2

theorem pairReps_mem {g : Equiv.Perm (Fin D.n)} (hg : g ∈ pairReps D S) : g ∈ pairG D S := by
  unfold pairReps at hg
  rcases List.mem_cons.1 hg with rfl | hg
  · exact one_mem _
  · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
    exact wordVal_mem S (pairG D S) (fun _ hg => Subgroup.subset_closure hg) w

theorem pGens_rep (hS : Sound D S) :
    ∀ j, TabRep ((pGens D).getD j (idTab D.n)) ((D.pW.map (wordVal S)).getD j 1) := by
  exact CFSG.AGLEmbedding.MaxD2.rep_map_words S D.gT (giT D) hS.rep hS.gi D.pW

theorem sideGens_rep (hS : Sound D S) (k : ℕ) :
    ∀ j, TabRep ((sideGens D k).getD j (idTab D.n))
      (((D.sideW.getD k []).map (wordVal S)).getD j 1) := by
  exact CFSG.AGLEmbedding.MaxD2.rep_map_words S D.gT (giT D) hS.rep hS.gi
    (D.sideW.getD k [])

end CFSG.StandardType.TitsOvergroup

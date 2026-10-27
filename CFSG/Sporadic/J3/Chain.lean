module

public import CFSG.Sporadic.J3.Group
public import CFSG.Perm.ChainSpec
public import CFSG.Sporadic.Fi23.SlpSpec

public section

namespace CFSG.Sporadic.J3

open Native CFSG.Sporadic.Th CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.Th.Native (ap invT invOK Table)

variable (D : Data)

@[expose] noncomputable def genABG (z : ℤ) : J D :=
  if z = 1 then a D else if z = -1 then (a D)⁻¹ else if z = 2 then b D else (b D)⁻¹

@[expose] noncomputable def gs (j : ℕ) : J D := CFSG.Sporadic.Fi23.slpG (genABG D) D.words j

noncomputable abbrev lvl (i : ℕ) : Subgroup (J D) := levelGroup D.letters D.base (pairG (gs D)) i

abbrev root (h : 0 < D.n) : Fin D.n := ⟨0, h⟩

section Chain

variable {D} {c : ℕ} (hF : Facts D c)
include hF

theorem rep_genT (z : ℤ) : Rep D.n (genT D.n D.tA D.tB z) (genABG D z) := by
  have hO := hF.orbitFacts
  unfold genT genABG
  split_ifs
  · exact rep_a hO
  · exact Rep.inv_of_invOK (rep_a hO) hF.invA
  · exact rep_b hO
  · exact Rep.inv_of_invOK (rep_b hO) hF.invB

theorem letters_size : D.letters.size = 2 * D.words.size :=
  (CFSG.Sporadic.Fi23.slpInv_full (n := D.n) (gens := genT D.n D.tA D.tB) hF.slp).1

theorem rep_letters : ∀ j < D.letters.size / 2, Rep D.n D.letters[2 * j]! (gs D j) := by
  intro j hj
  rw [letters_size hF] at hj
  have hinv := (chainOK_parts hF.chain).2.1
  refine CFSG.Sporadic.Fi23.rep_slpLetters (lt_trans hF.n_lt (by norm_num))
    (rep_genT hF) hF.slp (fun i hi => ?_) j (by omega)
  exact hinv i (by rw [letters_size hF]; omega)

theorem sep : ∀ g : J D, (∀ t < D.basis.size, idx D.n g D.basis[t]! = D.basis[t]!) → g = 1 :=
  eq_one_of_fix_basis hF

theorem chain :
    (∀ i < D.base.size, TreeFacts D.n D.trees[i]! (levelLetters D.letters D.base i)
      (pairG (gs D)) D.base[i]!) ∧
      (∀ i < D.base.size, ∀ g ∈ lvl D i,
        idx D.n g D.base[i]! = D.base[i]! ↔ g ∈ lvl D (i + 1)) ∧
      ∀ i ≤ D.base.size, Nat.card (lvl D i) =
        ∏ l ∈ Finset.Ico i D.base.size, D.trees[l]!.pts.size :=
  chain_facts (rep_letters hF) (sep hF) hF.chain

theorem rep_pairG_all : ∀ l < D.letters.size, Rep D.n D.letters[l]! (pairG (gs D) l) :=
  rep_pairG (rep_letters hF) (by rw [letters_size hF]; omega)
    (chainOK_parts hF.chain).2.1

theorem walkFacts {i : ℕ} (hi : i < D.base.size) :
    WalkFacts D.n D.trees[i]! D.letters (pairG (gs D)) := by
  intro k hk hk0
  obtain ⟨hpar, hlab⟩ := ((chain hF).1 i hi).par k hk hk0
  have hl := levelLetters_lt hlab
  refine ⟨hpar, rep_pairG_all hF _ hl, ?_⟩
  rw [← pairG_invL]
  exact rep_pairG_all hF _ (invL_lt (by rw [letters_size hF]; omega) hl)

theorem gs_zero : gs D 0 = a D := by
  unfold gs
  rw [CFSG.Sporadic.Fi23.slpG_eq, hF.word0]
  simp [wordG, genABG]

theorem gs_one : gs D 1 = b D := by
  unfold gs
  rw [CFSG.Sporadic.Fi23.slpG_eq, hF.word1]
  simp [wordG, genABG]

theorem lvl_zero : lvl D 0 = ⊤ := by
  rw [eq_top_iff, ← closure_ab D, Subgroup.closure_le]
  have hsz := letters_size hF
  have h2 := hF.words_size
  rintro _ (rfl | rfl)
  · have h : pairG (gs D) 0 = a D := by
      rw [show pairG (gs D) 0 = gs D 0 from ite_eq_left rfl, gs_zero hF]
    rw [← h]
    exact lG_mem (mem_levelLetters_zero.2 (by omega))
  · have h : pairG (gs D) 2 = b D := by
      rw [show pairG (gs D) 2 = gs D 1 from ite_eq_left rfl, gs_one hF]
    rw [← h]
    exact lG_mem (mem_levelLetters_zero.2 (by omega))

theorem card_lvl {i : ℕ} (hi : i ≤ D.base.size) :
    Nat.card (lvl D i) = ∏ l ∈ Finset.Ico i D.base.size, D.trees[l]!.pts.size :=
  (chain hF).2.2 i hi

theorem stabilizer_root : MulAction.stabilizer (J D) (root D hF.n_pos) = lvl D 1 := by
  ext g
  rw [MulAction.mem_stabilizer_iff]
  have hg0 : g ∈ lvl D 0 := by rw [lvl_zero hF]; exact Subgroup.mem_top g
  have h := (chain hF).2.1 0 hF.base_pos g hg0
  rw [hF.base0] at h
  rw [← h, idx_of_lt g hF.n_pos]
  exact ⟨fun e => by rw [e], fun e => Fin.ext e⟩

theorem card_stabilizer_root :
    Nat.card (MulAction.stabilizer (J D) (root D hF.n_pos)) =
      ∏ l ∈ Finset.Ico 1 D.base.size, D.trees[l]!.pts.size := by
  rw [stabilizer_root hF, card_lvl hF hF.base_pos]

theorem trees_zero_size : D.trees[0]!.pts.size = D.orbSizes[0]! := by
  have h := congrArg (fun L : List ℕ => L[0]?) hF.sizes
  have h0 : 0 < D.trees.size := by
    rw [(chainOK_parts hF.chain).2.2.1]; exact hF.base_pos
  simp only [orbitSizes, List.getElem?_map, Array.getElem?_toList,
    Array.getElem?_eq_getElem h0, Option.map_some] at h
  rw [getElem!_pos D.trees 0 h0, getElem!_def, ← h]

theorem isPretransitive (horb : D.orbSizes[0]! = D.n) :
    MulAction.IsPretransitive (J D) (Fin D.n) := by
  have hT := (chain hF).1 0 hF.base_pos
  rw [hF.base0] at hT
  have hcard := hT.card_orbit
  rw [trees_zero_size hF, horb] at hcard
  have hall : ∀ p : Fin D.n, p ∈ MulAction.orbit (lettersGroup (levelLetters D.letters D.base 0)
      (pairG (gs D))) (⟨0, hT.r_lt⟩ : Fin D.n) := by
    classical
    have hfin : (MulAction.orbit (lettersGroup (levelLetters D.letters D.base 0) (pairG (gs D)))
        (⟨0, hT.r_lt⟩ : Fin D.n)) = Set.univ := by
      apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) _ (Set.toFinite _)
      rw [Set.ncard_univ, Nat.card_fin, ← Nat.card_coe_set_eq, hcard]
    intro p
    rw [hfin]
    exact Set.mem_univ p
  refine ⟨fun p q => ?_⟩
  have hreach : ∀ r : Fin D.n, ∃ g : J D, g • (⟨0, hT.r_lt⟩ : Fin D.n) = r := by
    intro r
    obtain ⟨⟨g, _⟩, hg⟩ := hall r
    exact ⟨g, hg⟩
  obtain ⟨g, hg⟩ := hreach p
  obtain ⟨h, hh⟩ := hreach q
  exact ⟨h * g⁻¹, by rw [mul_smul, ← hg, inv_smul_smul, hh]⟩

end Chain

end CFSG.Sporadic.J3

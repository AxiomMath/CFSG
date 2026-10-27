module

public import CFSG.Perm.ChainSpec

public section

namespace CFSG.Perm

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm.Native

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]
variable {letters : Array Table} {gs : ℕ → G} {base Q qb : Array ℕ} {trees : Array Tree}
  {chunks : ℕ}

theorem chain_sift_complete [Finite G]
    (hrep : ∀ j < letters.size / 2, Rep n letters[2 * j]! (gs j))
    (hsep : ∀ g : G, (∀ t < Q.size, idx n g Q[t]! = Q[t]!) → g = 1)
    (h : chainOK n letters base Q qb trees chunks = true) {g : G}
    (hg : g ∈ levelGroup letters base (pairG gs) 0) {img : Array ℕ} (hsz : img.size = Q.size)
    (himg : ∀ t < Q.size, img[t]! = idx n g Q[t]!) :
    sift trees letters qb Q 0 img = true := by
  obtain ⟨hTF, hstab, hcard⟩ := chain_facts hrep hsep h
  obtain ⟨h2, hinv, htrees, -, hQ, hqbQ, -, -, -⟩ := chainOK_parts h
  have hrepAll := rep_pairG hrep h2 hinv
  have hWF : ∀ i < base.size, WalkFacts n trees[i]! letters (pairG gs) := by
    intro i hi k hk hk0
    obtain ⟨hpar, hlab⟩ := (hTF i hi).par k hk hk0
    have hl := levelLetters_lt hlab
    refine ⟨hpar, hrepAll _ hl, ?_⟩
    rw [← pairG_invL]
    exact hrepAll _ (invL_lt h2 hl)
  suffices key : ∀ d l, base.size - l = d → l ≤ base.size →
      ∀ g ∈ levelGroup letters base (pairG gs) l, ∀ img : Array ℕ, img.size = Q.size →
        (∀ t < Q.size, img[t]! = idx n g Q[t]!) → sift trees letters qb Q l img = true from
    key _ 0 rfl (Nat.zero_le _) g hg img hsz himg
  intro d
  induction d with
  | zero =>
    intro l hd hl g hg img hsz himg
    obtain rfl : l = base.size := by omega
    have h1 : Nat.card (levelGroup letters base (pairG gs) base.size) = 1 := by
      rw [hcard base.size le_rfl]
      simp
    have hg1 : g = 1 := by
      rw [Subgroup.eq_bot_of_card_eq _ h1] at hg
      exact Subgroup.mem_bot.1 hg
    subst hg1
    rw [sift.eq_def, dite_eq_right (by omega)]
    simp only [tupleEq, Bool.and_eq_true, beq_iff_eq]
    refine ⟨hsz, allIn_eq_true.2 fun t _ ht => ?_⟩
    simp [himg t ht, idx_one]
  | succ d ih =>
    intro l hd hl g hg img hsz himg
    have hlt : l < base.size := by omega
    have hlt' : l < trees.size := by omega
    have hT := hTF l hlt
    have hW := hWF l hlt
    rw [getElem!_pos trees l hlt'] at hT hW
    obtain ⟨hqbl, hQqb⟩ := hqbQ l hlt
    have hbase : base[l]! < n := by rw [← hQqb]; exact hQ _ hqbl
    set r : Fin n := ⟨base[l]!, hbase⟩
    have hgmem : g ∈ lettersGroup (levelLetters letters base l) (pairG gs) := hg
    obtain ⟨k, hk, hkp⟩ := (hT.mem_orbit_iff
      ((⟨g, hgmem⟩ : lettersGroup (levelLetters letters base l) (pairG gs)) • r)).1
      (MulAction.mem_orbit _ _)
    have hkp' : ap trees[l].pts k = idx n g base[l]! := by
      rw [hkp]
      exact smul_val_eq_idx g r
    have himgq : img[qb[l]!]! = idx n g base[l]! := by rw [himg _ hqbl, hQqb]
    have hpos : ap trees[l].pos img[qb[l]!]! = k := by
      rw [himgq, ← hkp', hT.pos_pts k hk]
    rw [sift.eq_def, dite_eq_left hlt']
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [hpos]
    refine ⟨hk, ?_⟩
    have himgn : ∀ t < img.size, img[t]! < n := by
      intro t ht
      rw [hsz] at ht
      rw [himg t ht]
      exact idx_lt _ (hQ t ht)
    obtain ⟨hs', he'⟩ := walkInv_spec (lG := pairG gs) hW hk img himgn
    have htmem : treeG trees[l] (pairG gs) k ∈ levelGroup letters base (pairG gs) l :=
      hT.treeG_mem hk
    have hfix : idx n ((treeG trees[l] (pairG gs) k)⁻¹ * g) base[l]! = base[l]! := by
      rw [idx_mul, ← hkp', ← hT.elt k hk, ← idx_mul, inv_mul_cancel, idx_one]
    have hnext : (treeG trees[l] (pairG gs) k)⁻¹ * g ∈
        levelGroup letters base (pairG gs) (l + 1) :=
      (hstab l hlt _ (mul_mem (inv_mem htmem) hg)).1 hfix
    exact ih (l + 1) (by omega) (by omega) _ hnext _ (by rw [hs', hsz])
      (fun t' ht' => by rw [he' t' (by rwa [hsz]), himg t' ht', idx_mul])

theorem not_mem_levelGroup_of_sift_eq_false [Finite G]
    (hrep : ∀ j < letters.size / 2, Rep n letters[2 * j]! (gs j))
    (hsep : ∀ g : G, (∀ t < Q.size, idx n g Q[t]! = Q[t]!) → g = 1)
    (h : chainOK n letters base Q qb trees chunks = true) {g : G} {img : Array ℕ}
    (hsz : img.size = Q.size) (himg : ∀ t < Q.size, img[t]! = idx n g Q[t]!)
    (hs : sift trees letters qb Q 0 img = false) :
    g ∉ levelGroup letters base (pairG gs) 0 := fun hg => by
  rw [chain_sift_complete hrep hsep h hg hsz himg] at hs
  exact absurd hs (by decide)

end CFSG.Perm

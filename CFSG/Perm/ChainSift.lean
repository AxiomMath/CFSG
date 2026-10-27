module

public import CFSG.Perm.ChainSpec

public section

namespace CFSG.Perm

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm.Native

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]
variable {letters : Array Table} {gs : ℕ → G} {base Q qb : Array ℕ} {trees : Array Tree}
  {chunks : ℕ}

theorem chain_sift_mem (hrep : ∀ j < letters.size / 2, Rep n letters[2 * j]! (gs j))
    (hsep : ∀ g : G, (∀ t < Q.size, idx n g Q[t]! = Q[t]!) → g = 1)
    (h : chainOK n letters base Q qb trees chunks = true) {g : G} {img : Array ℕ}
    (hsz : img.size = Q.size) (himg : ∀ t < Q.size, img[t]! = idx n g Q[t]!)
    (hs : sift trees letters qb Q 0 img = true) :
    g ∈ levelGroup letters base (pairG gs) 0 := by
  obtain ⟨h2, hinv, htrees, -, hQ, -, htree, -, -⟩ := chainOK_parts h
  have hrepAll := rep_pairG hrep h2 hinv
  have hlvRep : ∀ i, ∀ l ∈ levelLetters letters base i, Rep n letters[l]! (pairG gs l) :=
    fun i l hl => hrepAll l (levelLetters_lt hl)
  have hTF : ∀ i < base.size,
      TreeFacts n trees[i]! (levelLetters letters base i) (pairG gs) base[i]! :=
    fun i hi => treeOK_facts (hlvRep i) (htree i hi)
  refine sift_mem (lG := pairG gs) hsep hQ _ trees.size 0 (Nat.sub_zero _) ?_ g img hsz himg hs
  intro l' hl' _
  have hl'm : l' < base.size := by rw [← htrees]; exact hl'
  refine ⟨?_, fun k hk => levelGroup_anti (pairG gs) (Nat.zero_le l') ((hTF l' hl'm).treeG_mem hk)⟩
  intro k hk hk0
  obtain ⟨hpar, hlab⟩ := (hTF l' hl'm).par k hk hk0
  have hl := levelLetters_lt hlab
  refine ⟨hpar, hrepAll _ hl, ?_⟩
  rw [← pairG_invL]
  exact hrepAll _ (invL_lt h2 hl)

end CFSG.Perm

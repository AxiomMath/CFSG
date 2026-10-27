module

public import CFSG.Perm.ChainSpec

public section

namespace CFSG.Perm

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm.Native

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

theorem sift_complete {trees : Array Tree} {letters : Array Table} {lG : ℕ → G}
    {qb Q : Array ℕ} {lvs : ℕ → Array ℕ} (K : ℕ → Subgroup G)
    (hQ : ∀ t < Q.size, Q[t]! < n) (hqb : ∀ l < trees.size, qb[l]! < Q.size)
    (hW : ∀ l < trees.size, WalkFacts n trees[l]! letters lG)
    (hT : ∀ l < trees.size, TreeFacts n trees[l]! (lvs l) lG Q[qb[l]!]!)
    (hK : ∀ l < trees.size, lettersGroup (lvs l) lG = K l)
    (hstab : ∀ l < trees.size, ∀ g ∈ K l,
      idx n g Q[qb[l]!]! = Q[qb[l]!]! → g ∈ K (l + 1))
    (hbot : K trees.size = ⊥) :
    ∀ (d l : ℕ), trees.size - l = d → l ≤ trees.size → ∀ g ∈ K l, ∀ img : Array ℕ,
      img.size = Q.size → (∀ t < Q.size, img[t]! = idx n g Q[t]!) →
        sift trees letters qb Q l img = true := by
  intro d
  induction d with
  | zero =>
    intro l hd hl g hg img hsz himg
    have hl' : l = trees.size := by omega
    subst hl'
    have hg1 : g = 1 := by
      have := hg
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    rw [sift.eq_def, dite_eq_right (by omega)]
    simp only [tupleEq, Bool.and_eq_true, beq_iff_eq]
    refine ⟨hsz, allIn_eq_true.2 fun t _ ht => ?_⟩
    rw [himg t ht, hg1, idx_one]
    simp
  | succ d ih =>
    intro l hd hl g hg img hsz himg
    have hlt : l < trees.size := by omega
    have hTl := hT l hlt
    have hQb : Q[qb[l]!]! < n := hQ _ (hqb l hlt)
    have himgb : img[qb[l]!]! = idx n g Q[qb[l]!]! := himg _ (hqb l hlt)
    have hmem : ∃ k < trees[l]!.pts.size, ap trees[l]!.pts k = img[qb[l]!]! := by
      have h1 : (⟨img[qb[l]!]!, by rw [himgb]; exact idx_lt _ hQb⟩ : Fin n) ∈
          MulAction.orbit (lettersGroup (lvs l) lG) (⟨Q[qb[l]!]!, hTl.r_lt⟩ : Fin n) := by
        refine ⟨⟨g, by rw [hK l hlt]; exact hg⟩, ?_⟩
        apply Fin.ext
        show (g • (⟨Q[qb[l]!]!, hTl.r_lt⟩ : Fin n)).val = img[qb[l]!]!
        rw [smul_val_eq_idx, himgb]
      exact (hTl.mem_orbit_iff _).1 h1
    obtain ⟨k, hk, hkp⟩ := hmem
    have hpos : ap trees[l]!.pos img[qb[l]!]! = k := by
      rw [← hkp, hTl.pos_pts k hk]
    rw [sift.eq_def, dite_eq_left hlt]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    have himgn : ∀ t < img.size, img[t]! < n := by
      intro t ht
      rw [hsz] at ht
      rw [himg t ht]
      exact idx_lt _ (hQ t ht)
    obtain ⟨hs', he'⟩ := walkInv_spec (hW l hlt) hk img himgn
    have hgK : treeG trees[l]! lG k ∈ K l := by
      rw [← hK l hlt]; exact hTl.treeG_mem hk
    have hg' : (treeG trees[l]! lG k)⁻¹ * g ∈ K l := (K l).mul_mem ((K l).inv_mem hgK) hg
    have hfix : idx n ((treeG trees[l]! lG k)⁻¹ * g) Q[qb[l]!]! = Q[qb[l]!]! := by
      rw [idx_mul, ← himgb, ← hkp, ← hTl.elt k hk, ← idx_mul, inv_mul_cancel, idx_one]
    rw [← getElem!_pos trees l hlt, hpos]
    exact ⟨hk, ih (l + 1) (by omega) (by omega) _ (hstab l hlt _ hg' hfix) _
      (by rw [hs', hsz]) (fun t ht => by rw [he' t (by rwa [hsz]), himg t ht, idx_mul])⟩

end CFSG.Perm

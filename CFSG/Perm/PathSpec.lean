module

public import Certificates.Data.CFSGNative.Perm.Path
public import CFSG.Perm.ChainSpec

public section

namespace CFSG.Perm

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm.Native

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

theorem orbPathOK_card_le {T : Tree} {letters : Array Table} {lv : Array ℕ} {lG : ℕ → G} {r : ℕ}
    (hrep : ∀ l ∈ lv, Rep n letters[l]! (lG l)) (h : Perm.Native.orbPathOK n r T letters lv = true) :
    ∃ hr : r < n,
      T.pts.size ≤ Nat.card (MulAction.orbit (lettersGroup lv lG) (⟨r, hr⟩ : Fin n)) := by
  simp only [Perm.Native.orbPathOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hm, h0⟩, hall⟩ := h
  have hat : ∀ k < T.pts.size, ap T.pts k < n ∧ ap T.pos (ap T.pts k) = k ∧
      (k = 0 ∨ (ap T.par k < k ∧ ap T.lab k ∈ lv ∧
        ap letters[ap T.lab k]! (ap T.pts (ap T.par k)) = ap T.pts k)) := by
    intro k hkm
    have := (allIn_eq_true.1 hall) k (Nat.zero_le _) hkm
    simp only [orbPathAt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      Bool.or_eq_true, Array.contains_iff_mem] at this
    obtain ⟨⟨hlt, hpos⟩, hpar⟩ := this
    refine ⟨hlt, hpos, ?_⟩
    rcases hpar with h | ⟨⟨h1, h2⟩, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, h3⟩
  have hpar : ∀ k < T.pts.size, 0 < k → ap T.par k < k ∧ ap T.lab k ∈ lv := by
    intro k hkm hk0
    rcases (hat k hkm).2.2 with h | h
    · omega
    · exact ⟨h.1, h.2.1⟩
  have hr : r < n := by
    rw [← h0]
    exact (hat 0 hm).1
  have helt : ∀ k < T.pts.size, idx n (treeG T lG k) r = ap T.pts k := by
    intro k hkm
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rw [treeG.eq_def]
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp [idx_one, h0]
      · obtain ⟨hpk, hlab⟩ := hpar k hkm hk0
        rw [dite_eq_left ⟨hk0, hpk⟩, idx_mul, ih _ hpk (lt_trans hpk hkm)]
        rcases (hat k hkm).2.2 with h | ⟨-, -, he⟩
        · omega
        · rw [← hrep _ hlab _ ((hat _ (lt_trans hpk hkm)).1), he]
  have hmem : ∀ k < T.pts.size, treeG T lG k ∈ lettersGroup lv lG := by
    intro k hk
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rw [treeG.eq_def]
      split_ifs with hg
      · exact (lettersGroup lv lG).mul_mem (lG_mem (hpar k hk hg.1).2)
          (ih _ hg.2 (lt_trans hg.2 hk))
      · exact (lettersGroup lv lG).one_mem
  refine ⟨hr, ?_⟩
  let f : Fin T.pts.size → MulAction.orbit (lettersGroup lv lG) (⟨r, hr⟩ : Fin n) :=
    fun k => ⟨⟨ap T.pts k, (hat k k.2).1⟩, ⟨treeG T lG k, hmem k k.2⟩, Fin.ext (by
      change ((treeG T lG k) • (⟨r, hr⟩ : Fin n)).val = ap T.pts k
      rw [smul_val_eq_idx, helt k k.2])⟩
  have hf : Function.Injective f := by
    intro a b hab
    have e : ap T.pts a = ap T.pts b := congrArg (fun q => q.1.val) hab
    apply Fin.ext
    rw [← (hat a a.2).2.1, ← (hat b b.2).2.1, e]
  have := Nat.card_le_card_of_injective f hf
  simpa using this

end CFSG.Perm

end

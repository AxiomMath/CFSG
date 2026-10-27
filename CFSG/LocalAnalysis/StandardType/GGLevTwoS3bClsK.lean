module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bTables3

public section

namespace CFSG.StandardType.LevTwo

theorem levTwoS3u_clsOrbit_of {n : ℕ} {roots : List (List ℤ)} (hnodup : roots.Nodup)
    (hlen : ∀ l ∈ roots, l.length = n) (cl : List (ℕ × ℕ)) (hpos : 0 < cl.length) (pm : ℕ)
    (h : (List.range roots.length).all (fun i => pm.testBit i ||
      (cl.getD (if cl.findIdx (fun p => p.2.testBit i) < cl.length then
        cl.findIdx (fun p => p.2.testBit i) else 0) (0, 0)).2.testBit i) = true) :
    ∀ i : Fin (roots.map (levTwoS3u_vec n)).length, ¬ pm.testBit i.val →
      (cl.getD (levTwoS3u_clsOf roots cl hpos
        ((roots.map (levTwoS3u_vec n)).get i)).1 (0, 0)).2.testBit i.val = true := by
  intro i hi
  have hi' : i.val < roots.length := by simpa using i.2
  have hget : (roots.map (levTwoS3u_vec n)).get i = levTwoS3u_vec n (roots.get ⟨i.val, hi'⟩) := by
    simp
  have hidx : levTwoS3u_idx roots ((roots.map (levTwoS3u_vec n)).get i) = i.val := by
    rw [hget]
    exact levTwoS3u_idx_vec_get hnodup hlen ⟨i.val, hi'⟩
  have h1 := List.all_eq_true.1 h i.val (List.mem_range.2 hi')
  simp only [Bool.not_eq_true] at hi
  rw [hi, Bool.false_or] at h1
  unfold levTwoS3u_clsOf
  split
  · rename_i hc
    rw [hidx] at hc
    rw [if_pos hc] at h1
    simpa only [hidx] using h1
  · rename_i hc
    rw [hidx] at hc
    rw [if_neg hc] at h1
    exact h1

end CFSG.StandardType.LevTwo

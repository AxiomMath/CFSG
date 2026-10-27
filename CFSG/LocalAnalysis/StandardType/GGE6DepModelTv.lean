module

public import CFSG.LocalAnalysis.StandardType.GGE6DepModelDefs
import CFSG.LocalAnalysis.StandardType.GGE6DepModelTvK

public section

namespace CFSG.StandardType

namespace E6Dep

private def tvM_0112 : Mat6 :=
  !![1, 0, 1, 0, 1, 0; 0, 1, 2, 0, 2, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0;
    0, 0, 2, 0, 2, 1]

private def tvM_0122 : Mat6 :=
  !![1, 0, 2, 0, 2, 0; 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0;
    0, 0, 1, 0, 1, 1]

private def tvM_0211 : Mat6 :=
  !![1, 0, 1, 0, 1, 0; 0, 1, 2, 0, 2, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0;
    0, 0, 1, 0, 1, 1]

private def tvM_0221 : Mat6 :=
  !![1, 0, 2, 0, 2, 0; 0, 1, 1, 0, 1, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0;
    0, 0, 2, 0, 2, 1]

private def tvM_1021 : Mat6 :=
  !![1, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 1; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 1;
    0, 0, 0, 0, 0, 1]

private def tvM_1022 : Mat6 :=
  !![1, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 2; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 2;
    0, 0, 0, 0, 0, 1]

private def tvM_1102 : Mat6 :=
  !![1, 0, 1, 0, 0, 1; 0, 1, 2, 0, 0, 2; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 2, 0, 1, 2;
    0, 0, 0, 0, 0, 1]

private def tvM_1111 : Mat6 :=
  !![1, 0, 2, 0, 1, 1; 0, 1, 1, 0, 2, 2; 0, 0, 2, 0, 2, 2; 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 2;
    0, 0, 0, 0, 0, 1]

private def tvM_1201 : Mat6 :=
  !![1, 0, 1, 0, 0, 2; 0, 1, 2, 0, 0, 1; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 2, 0, 1, 1;
    0, 0, 0, 0, 0, 1]

private def tvM_1212 : Mat6 :=
  !![1, 0, 2, 0, 1, 2; 0, 1, 1, 0, 2, 1; 0, 0, 2, 0, 2, 1; 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 0, 1;
    0, 0, 0, 0, 0, 1]

private def tvM_2011 : Mat6 :=
  !![1, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 2; 0, 0, 0, 1, 0, 1; 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

private def tvM_2012 : Mat6 :=
  !![1, 0, 0, 0, 0, 2; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 1; 0, 0, 0, 1, 0, 2; 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

private def tvM_2102 : Mat6 :=
  !![1, 0, 2, 0, 0, 2; 0, 1, 1, 0, 0, 1; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 1;
    0, 0, 0, 0, 0, 1]

private def tvM_2121 : Mat6 :=
  !![1, 1, 2, 1, 1, 0; 0, 0, 1, 2, 2, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 1, 2, 1, 2, 0;
    0, 2, 1, 2, 2, 1]

private def tvM_2201 : Mat6 :=
  !![1, 0, 2, 0, 0, 1; 0, 1, 1, 0, 0, 2; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 2;
    0, 0, 0, 0, 0, 1]

private def tvM_2222 : Mat6 :=
  !![1, 1, 2, 1, 1, 0; 0, 0, 1, 2, 2, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 1, 2, 1, 2, 0;
    0, 1, 2, 1, 1, 1]

private theorem tv_0112 : IsTv6 (evalWord (gensAll 0 1 1 2) [5, 6, 5, 6]) := by
  rw [show evalWord (gensAll 0 1 1 2) [5, 6, 5, 6] = tvM_0112 by decide +kernel]
  exact TvK.isTv6_of ![1, 2, 0, 0, 0, 2] ![0, 0, 1, 0, 1, 0] _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem tv_0122 : IsTv6 (evalWord (gensAll 0 1 2 2) [5, 6, 5, 6]) := by
  rw [show evalWord (gensAll 0 1 2 2) [5, 6, 5, 6] = tvM_0122 by decide +kernel]
  exact TvK.isTv6_of ![1, 2, 0, 0, 0, 2] ![0, 0, 2, 0, 2, 0] _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem tv_0211 : IsTv6 (evalWord (gensAll 0 2 1 1) [5, 6, 5, 6]) := by
  rw [show evalWord (gensAll 0 2 1 1) [5, 6, 5, 6] = tvM_0211 by decide +kernel]
  exact TvK.isTv6_of ![1, 2, 0, 0, 0, 1] ![0, 0, 1, 0, 1, 0] _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem tv_0221 : IsTv6 (evalWord (gensAll 0 2 2 1) [5, 6, 5, 6]) := by
  rw [show evalWord (gensAll 0 2 2 1) [5, 6, 5, 6] = tvM_0221 by decide +kernel]
  exact TvK.isTv6_of ![1, 2, 0, 0, 0, 1] ![0, 0, 2, 0, 2, 0] _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem tv_1021 : IsTv6 (evalWord (gensAll 1 0 2 1) [5, 6]) := by
  rw [show evalWord (gensAll 1 0 2 1) [5, 6] = tvM_1021 by decide +kernel]
  exact TvK.isTv6_of ![1, 2, 0, 0, 2, 0] ![0, 0, 0, 0, 0, 2] _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem tv_1022 : IsTv6 (evalWord (gensAll 1 0 2 2) [5, 6]) := by
  rw [show evalWord (gensAll 1 0 2 2) [5, 6] = tvM_1022 by decide +kernel]
  exact TvK.isTv6_of ![1, 2, 0, 0, 2, 0] ![0, 0, 0, 0, 0, 1] _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem tv_1102 : IsTv6 (evalWord (gensAll 1 1 0 2) [5, 6, 5, 6]) := by
  rw [show evalWord (gensAll 1 1 0 2) [5, 6, 5, 6] = tvM_1102 by decide +kernel]
  exact TvK.isTv6_of ![1, 2, 0, 0, 2, 0] ![0, 0, 1, 0, 0, 1] _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem tv_1111 : IsTv6 (evalWord (gensAll 1 1 1 1) [2, 5, 2, 6, 2, 5, 2, 6]) := by
  rw [show evalWord (gensAll 1 1 1 1) [2, 5, 2, 6, 2, 5, 2, 6] = tvM_1111 by decide +kernel]
  exact TvK.isTv6_of ![1, 2, 2, 0, 2, 0] ![0, 0, 2, 0, 1, 1] _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem tv_1201 : IsTv6 (evalWord (gensAll 1 2 0 1) [5, 6, 5, 6]) := by
  rw [show evalWord (gensAll 1 2 0 1) [5, 6, 5, 6] = tvM_1201 by decide +kernel]
  exact TvK.isTv6_of ![1, 2, 0, 0, 2, 0] ![0, 0, 1, 0, 0, 2] _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem tv_1212 : IsTv6 (evalWord (gensAll 1 2 1 2) [2, 5, 2, 6, 2, 5, 2, 6]) := by
  rw [show evalWord (gensAll 1 2 1 2) [2, 5, 2, 6, 2, 5, 2, 6] = tvM_1212 by decide +kernel]
  exact TvK.isTv6_of ![1, 2, 2, 0, 2, 0] ![0, 0, 2, 0, 1, 2] _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem tv_2011 :
    IsTv6 (evalWord (gensAll 2 0 1 1)
      [0, 1, 2, 3, 4, 3, 2, 1, 0, 5, 2, 1, 3, 2, 6, 2, 3, 1, 2, 5]) := by
  rw [show evalWord (gensAll 2 0 1 1)
      [0, 1, 2, 3, 4, 3, 2, 1, 0, 5, 2, 1, 3, 2, 6, 2, 3, 1, 2, 5] = tvM_2011 by
    decide +kernel]
  exact TvK.isTv6_of ![1, 0, 2, 1, 0, 0] ![0, 0, 0, 0, 0, 1] _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem tv_2012 :
    IsTv6 (evalWord (gensAll 2 0 1 2)
      [0, 1, 2, 3, 4, 3, 2, 1, 0, 5, 2, 1, 3, 2, 6, 2, 3, 1, 2, 5]) := by
  rw [show evalWord (gensAll 2 0 1 2)
      [0, 1, 2, 3, 4, 3, 2, 1, 0, 5, 2, 1, 3, 2, 6, 2, 3, 1, 2, 5] = tvM_2012 by
    decide +kernel]
  exact TvK.isTv6_of ![1, 0, 2, 1, 0, 0] ![0, 0, 0, 0, 0, 2] _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem tv_2102 : IsTv6 (evalWord (gensAll 2 1 0 2) [5, 6, 5, 6]) := by
  rw [show evalWord (gensAll 2 1 0 2) [5, 6, 5, 6] = tvM_2102 by decide +kernel]
  exact TvK.isTv6_of ![1, 2, 0, 0, 2, 0] ![0, 0, 2, 0, 0, 2] _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem tv_2121 : IsTv6 (evalWord (gensAll 2 1 2 1) [2, 5, 2, 6, 2, 5, 2, 6]) := by
  rw [show evalWord (gensAll 2 1 2 1) [2, 5, 2, 6, 2, 5, 2, 6] = tvM_2121 by decide +kernel]
  exact TvK.isTv6_of ![1, 2, 0, 0, 1, 2] ![0, 1, 2, 1, 1, 0] _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem tv_2201 : IsTv6 (evalWord (gensAll 2 2 0 1) [5, 6, 5, 6]) := by
  rw [show evalWord (gensAll 2 2 0 1) [5, 6, 5, 6] = tvM_2201 by decide +kernel]
  exact TvK.isTv6_of ![1, 2, 0, 0, 2, 0] ![0, 0, 2, 0, 0, 1] _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem tv_2222 : IsTv6 (evalWord (gensAll 2 2 2 2) [2, 5, 2, 6, 2, 5, 2, 6]) := by
  rw [show evalWord (gensAll 2 2 2 2) [2, 5, 2, 6, 2, 5, 2, 6] = tvM_2222 by decide +kernel]
  exact TvK.isTv6_of ![1, 2, 0, 0, 1, 1] ![0, 1, 2, 1, 1, 0] _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem exists_transvection (s t u w : ZMod 3) (h : s * u + t * w = 2) (hw : w ≠ 0)
    (hs : ¬ (s = 0 ∧ u = 0)) :
    ∃ word : List (Fin 7), IsTv6 (evalWord (gensAll s t u w) word) := by
  have hmem : (s, t, u, w) ∈
      ({(0, 1, 1, 2), (0, 1, 2, 2), (0, 2, 1, 1), (0, 2, 2, 1), (1, 0, 2, 1), (1, 0, 2, 2),
        (1, 1, 0, 2), (1, 1, 1, 1), (1, 2, 0, 1), (1, 2, 1, 2), (2, 0, 1, 1), (2, 0, 1, 2),
        (2, 1, 0, 2), (2, 1, 2, 1), (2, 2, 0, 1), (2, 2, 2, 2)} :
        Finset (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3)) := by
    revert s t u w h hw hs
    decide
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact ⟨_, tv_0112⟩
  · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact ⟨_, tv_0122⟩
  · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact ⟨_, tv_0211⟩
  · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact ⟨_, tv_0221⟩
  · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact ⟨_, tv_1021⟩
  · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact ⟨_, tv_1022⟩
  · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact ⟨_, tv_1102⟩
  · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact ⟨_, tv_1111⟩
  · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact ⟨_, tv_1201⟩
  · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact ⟨_, tv_1212⟩
  · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact ⟨_, tv_2011⟩
  · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact ⟨_, tv_2012⟩
  · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact ⟨_, tv_2102⟩
  · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact ⟨_, tv_2121⟩
  · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact ⟨_, tv_2201⟩
  · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact ⟨_, tv_2222⟩

end E6Dep

end CFSG.StandardType

end

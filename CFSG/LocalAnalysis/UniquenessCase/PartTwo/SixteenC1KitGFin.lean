module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitBFin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LargeExtraspecial.O62 CFSG.LargeExtraspecial.O62.Code

@[expose] def s16c1g_cands : List (List ℕ × List ℕ) := [
  ([16, 32], [3, 7, 11, 14]),
  ([24, 57], [18, 26, 36, 37]),
  ([13, 37], [11, 22, 42, 54]),
  ([21, 32], [11, 14, 34, 40]),
  ([12, 36], [3, 31, 33, 63]),
  ([11, 41], [14, 21, 40, 53]),
  ([3, 21], [11, 16, 31, 56]),
  ([14, 20], [7, 16, 21, 57]),
  ([11, 52], [3, 24, 48, 53]),
  ([18, 32], [12, 14, 33, 37]),
  ([14, 54], [11, 21, 37, 50]),
  ([3, 38], [11, 24, 32, 36]),
  ([7, 40], [3, 20, 41, 52]),
  ([11, 42], [13, 22, 37, 54]),
  ([31, 41], [21, 26, 33, 50])]

@[expose] def s16c1g_goodE (p : List ℕ × List ℕ) : Bool :=
  s16c1b_okWord p.1 && s16c1b_okWord p.2 &&
    mul (wordC p.1) (mul (wordC p.1) (wordC p.1)) == one &&
    mul (wordC p.2) (mul (wordC p.2) (wordC p.2)) == one &&
    wordC p.1 != one && wordC p.2 != one &&
    mul (wordC p.1) (wordC p.2) == mul (wordC p.2) (wordC p.1) &&
    wordC p.2 != wordC p.1 && wordC p.2 != mul (wordC p.1) (wordC p.1)

@[expose] def s16c1g_planeList (a b : ℕ) : List ℕ := [0, a, b, a ^^^ b]

@[expose] def s16c1g_plane (a b : ℕ) : Set V₀ :=
  {v | ∃ n ∈ s16c1g_planeList a b, vec n = v}

@[expose] def s16c1g_isPlane (a b : ℕ) : Bool :=
  a != 0 && b != 0 && a != b && !qB true a && !qB true b && !qB true (a ^^^ b)

@[expose] def s16c1g_stabPlane (c a b : ℕ) : Bool :=
  (s16c1g_planeList a b).all fun n => (s16c1g_planeList a b).contains (act c n)

@[expose] def s16c1g_stabE (p : List ℕ × List ℕ) (a b : ℕ) : Bool :=
  s16c1g_stabPlane (wordC p.1) a b && s16c1g_stabPlane (wordC p.2) a b

@[expose] def s16c1g_checkPlanes : Bool :=
  s16c1g_cands.all s16c1g_goodE &&
    (List.range 64).all fun a => (List.range 64).all fun b =>
      !s16c1g_isPlane a b || s16c1g_cands.any fun p => s16c1g_stabE p a b

theorem s16c1g_checkPlanes_ok : s16c1g_checkPlanes = true := by decide +kernel

theorem s16c1g_exists_cand {a b : ℕ} (ha : a < 64) (hb : b < 64)
    (hpl : s16c1g_isPlane a b = true) :
    ∃ p ∈ s16c1g_cands, s16c1g_goodE p = true ∧ s16c1g_stabE p a b = true := by
  have h := s16c1g_checkPlanes_ok
  simp only [s16c1g_checkPlanes, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true] at h
  obtain ⟨hgood, hall⟩ := h
  rcases hall a ha b hb with h' | ⟨p, hp, hpa⟩
  · rw [hpl] at h'
    exact absurd h' (by decide)
  · exact ⟨p, hp, hgood p hp, hpa⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

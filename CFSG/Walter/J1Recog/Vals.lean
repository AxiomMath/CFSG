module

public import CFSG.Walter.J1Recog.Pres

public section

namespace CFSG.Walter.J1Recog

open Word

variable {G : Type*} [Group G]

@[expose] def hVals (t n m : G) : List G :=
  [t ^ 2, n ^ 7, m ^ 3, m⁻¹ * n * m * n⁻¹ ^ 2, t⁻¹ * m⁻¹ * t * m,
    t⁻¹ * (n⁻¹ * t * n)⁻¹ * t * (n⁻¹ * t * n),
    t⁻¹ * ((n ^ 2)⁻¹ * t * n ^ 2)⁻¹ * t * ((n ^ 2)⁻¹ * t * n ^ 2),
    n⁻¹ ^ 3 * t * n * t * n ^ 2 * t, m⁻¹ * n⁻¹ * t * n * m * n⁻¹ ^ 2 * t * n ^ 2,
    m⁻¹ * n⁻¹ ^ 2 * t * n ^ 2 * m * n⁻¹ ^ 2 * t * n * t * n * t]

@[expose] def p1Vals (t n m s u : G) : List G :=
  hVals t n m ++ [s ^ 2, s⁻¹ * m⁻¹ * s * m, (s * n) ^ 2, (t * s) ^ 5, u ^ 2, (u * m) ^ 2,
    u⁻¹ * t⁻¹ * u * t, u⁻¹ * s⁻¹ * u * s]

@[expose] def ctVals (t n x : G) : List G :=
  [(x * t * (n⁻¹ * t * n)) ^ 5, (x * t * ((n ^ 2)⁻¹ * t * n ^ 2)) ^ 3,
    (x * (n⁻¹ * t * n) * ((n ^ 2)⁻¹ * t * n ^ 2)) ^ 5]

@[expose] def extraVal (c : Case) (t n m u : G) : G :=
  let a := m * u
  let a' := (n⁻¹ * t * n)⁻¹ * a * (n⁻¹ * t * n)
  let b := n * t * u * n⁻¹
  let b2 := (m * n ^ 4)⁻¹ * (t * u) * (m * n ^ 4)
  match c with
  | .O1a => b⁻¹ * a⁻¹ * b * a
  | .O1b => b⁻¹ * a'⁻¹ * b * a'
  | .O2a => b2⁻¹ * a⁻¹ * b2 * a
  | .O2b => b2⁻¹ * a'⁻¹ * b2 * a'

@[expose] def relVals (c : Case) (t n m s u : G) : List G :=
  p1Vals t n m s u ++ (match c with
    | .O1a | .O1b => ctVals t n u
    | .O2a | .O2b => ctVals t n (t * u)) ++ [extraVal c t n m u]

theorem map_ev_hRaw {k : ℕ} (f : Fin k → G) (t n m : Word k) :
    (hRaw t n m).map (ev f) = hVals (ev f t) (ev f n) (ev f m) := by
  simp [hRaw, hVals, mul_assoc]

theorem map_ev_reduce {k : ℕ} (f : Fin k → G) (l : List (Word k)) :
    (l.map FreeGroup.reduce).map (ev f) = l.map (ev f) := by
  rw [List.map_map]
  exact List.map_congr_left fun w _ => ev_reduce f w

theorem map_ev_rels (c : Case) (f : Fin 5 → G) :
    (rels c).map (ev f) = relVals c (f 0) (f 1) (f 2) (f 3) (f 4) := by
  have hH : (hRaw wt wn wm).map (ev f) = hVals (f 0) (f 1) (f 2) := by
    rw [map_ev_hRaw]
    simp [wt, wn, wm]
  cases c <;>
  · simp only [rels, map_ev_reduce, List.map_append, p1Raw, relVals, p1Vals, hH]
    simp [ct1Raw, ct2Raw, ctVals, extraRel, extraVal, wt, wn, wm, ws, wu, wa, wb, wb2,
      mul_assoc]

theorem map_ev_hRels (f : Fin 3 → G) : hRels.map (ev f) = hVals (f 0) (f 1) (f 2) := by
  rw [hRels, map_ev_reduce, map_ev_hRaw]
  simp

theorem forall_ev_rels_iff (c : Case) (f : Fin 5 → G) :
    (∀ w ∈ rels c, ev f w = 1) ↔ ∀ x ∈ relVals c (f 0) (f 1) (f 2) (f 3) (f 4), x = 1 := by
  rw [← map_ev_rels, List.forall_mem_map]

end CFSG.Walter.J1Recog

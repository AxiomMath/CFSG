module

public import CFSG.Quasithin.Recognition.G112A2D6ZornBasic

public section

namespace CFSG.Quasithin.G112A2

open CFSG.Open

@[expose] def z6cU (u x : z6O) : z6O := quasithinZornMul (quasithinZornMul u x) (z6Bar u)

@[expose] def z6MV (M : Fin 3 → Fin 3 → ZMod 2) (v : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 :=
  fun i => M i 0 * v 0 + M i 1 * v 1 + M i 2 * v 2

@[expose] def z6S (M N : Fin 3 → Fin 3 → ZMod 2) (x : z6O) : z6O :=
  (x.2.2.2, z6MV N x.2.2.1, z6MV M x.2.1, x.1)

@[expose] def z6Ms : List ((Fin 3 → Fin 3 → ZMod 2) × (Fin 3 → Fin 3 → ZMod 2)) :=
  [(![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]], ![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]]),
    (![![0, 0, 1], ![0, 1, 1], ![1, 1, 0]], ![![1, 1, 1], ![1, 1, 0], ![1, 0, 0]]),
    (![![0, 1, 0], ![1, 1, 0], ![0, 0, 1]], ![![1, 1, 0], ![1, 0, 0], ![0, 0, 1]]),
    (![![0, 1, 0], ![1, 1, 1], ![0, 1, 1]], ![![0, 1, 1], ![1, 0, 0], ![1, 0, 1]]),
    (![![0, 1, 1], ![1, 0, 0], ![1, 0, 1]], ![![0, 1, 0], ![1, 1, 1], ![0, 1, 1]]),
    (![![0, 1, 1], ![1, 0, 1], ![1, 1, 1]], ![![1, 0, 1], ![0, 1, 1], ![1, 1, 1]]),
    (![![1, 0, 0], ![0, 0, 1], ![0, 1, 0]], ![![1, 0, 0], ![0, 0, 1], ![0, 1, 0]]),
    (![![1, 0, 1], ![0, 0, 1], ![1, 1, 0]], ![![1, 1, 0], ![1, 1, 1], ![0, 1, 0]]),
    (![![1, 1, 0], ![1, 0, 0], ![0, 0, 1]], ![![0, 1, 0], ![1, 1, 0], ![0, 0, 1]]),
    (![![1, 1, 1], ![1, 0, 0], ![1, 0, 1]], ![![0, 1, 0], ![1, 0, 1], ![0, 1, 1]])]

theorem z6_mv_add (M : Fin 3 → Fin 3 → ZMod 2) (v w : Fin 3 → ZMod 2) :
    z6MV M (v + w) = z6MV M v + z6MV M w := by
  funext i
  simp only [z6MV, Pi.add_apply]
  ring

theorem z6_mv_smul (M : Fin 3 → Fin 3 → ZMod 2) (c : ZMod 2) (v : Fin 3 → ZMod 2) :
    z6MV M (c • v) = c • z6MV M v := by
  funext i
  simp only [z6MV, Pi.smul_apply, smul_eq_mul]
  ring

@[expose] def z6cUL (u : z6O) : z6O →ₗ[ZMod 2] z6O where
  toFun := z6cU u
  map_add' x y := by
    simp only [z6cU, z6_mul_add_right, z6_mul_add_left]
  map_smul' c x := by
    rcases z6_zmod2 c with rfl | rfl
    · simp [z6cU, z6_mul_zero_left, z6_mul_zero_right]
    · simp [z6cU]

@[expose] def z6SL (M N : Fin 3 → Fin 3 → ZMod 2) : z6O →ₗ[ZMod 2] z6O where
  toFun := z6S M N
  map_add' x y := by
    obtain ⟨a, u, v, b⟩ := x
    obtain ⟨a', u', v', b'⟩ := y
    simp only [z6S, Prod.mk_add_mk, z6_mv_add]
  map_smul' c x := by
    obtain ⟨a, u, v, b⟩ := x
    simp only [z6S, Prod.smul_mk, RingHom.id_apply, z6_mv_smul]

theorem z6_coords (P : z6O → Prop)
    (h : ∀ a b p0 p1 p2 q0 q1 q2 : ZMod 2, P (a, ![p0, p1, p2], ![q0, q1, q2], b)) : ∀ u : z6O, P u := by
  rintro ⟨a, p, q, b⟩
  have hp : p = ![p 0, p 1, p 2] := by
    funext i
    fin_cases i <;> rfl
  have hq : q = ![q 0, q 1, q 2] := by
    funext i
    fin_cases i <;> rfl
  have := h a b (p 0) (p 1) (p 2) (q 0) (q 1) (q 2)
  rw [← hp, ← hq] at this
  exact this

set_option synthInstance.maxSize 4096 in
theorem z6_F1_c : ∀ a b p0 p1 p2 q0 q1 q2 : ZMod 2,
    z6Tr ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) = 1 →
    z6Nrm ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) = 1 → ∀ i j : Fin 8,
    z6cU ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) (quasithinZornMul (z6E i) (z6E j)) =
      quasithinZornMul (z6cU ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) (z6E i))
        (z6cU ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) (z6E j)) := by
  decide +kernel

theorem z6_F1 : ∀ u : z6O, z6Tr u = 1 → z6Nrm u = 1 → ∀ i j : Fin 8,
    z6cU u (quasithinZornMul (z6E i) (z6E j)) =
      quasithinZornMul (z6cU u (z6E i)) (z6cU u (z6E j)) :=
  z6_coords (fun u => z6Tr u = 1 → z6Nrm u = 1 → ∀ i j : Fin 8,
    z6cU u (quasithinZornMul (z6E i) (z6E j)) =
      quasithinZornMul (z6cU u (z6E i)) (z6cU u (z6E j))) z6_F1_c

set_option synthInstance.maxSize 4096 in
theorem z6_F2_c : ∀ a b p0 p1 p2 q0 q1 q2 : ZMod 2,
    z6Tr ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) = 1 →
    z6Nrm ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) = 1 → ∀ i : Fin 8,
    z6cU ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O)
      (z6cU ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O)
        (z6cU ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) (z6E i))) = z6E i := by
  decide +kernel

theorem z6_F2 : ∀ u : z6O, z6Tr u = 1 → z6Nrm u = 1 → ∀ i : Fin 8,
    z6cU u (z6cU u (z6cU u (z6E i))) = z6E i :=
  z6_coords (fun u => z6Tr u = 1 → z6Nrm u = 1 → ∀ i : Fin 8,
    z6cU u (z6cU u (z6cU u (z6E i))) = z6E i) z6_F2_c

set_option synthInstance.maxSize 4096 in
theorem z6_F2one_c : ∀ a b p0 p1 p2 q0 q1 q2 : ZMod 2,
    z6Tr ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) = 1 →
    z6Nrm ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) = 1 →
    z6cU ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) z6One = z6One := by
  decide +kernel

theorem z6_F2one : ∀ u : z6O, z6Tr u = 1 → z6Nrm u = 1 → z6cU u z6One = z6One :=
  z6_coords (fun u => z6Tr u = 1 → z6Nrm u = 1 → z6cU u z6One = z6One) z6_F2one_c

set_option synthInstance.maxSize 4096 in
theorem z6_F3_c : ∀ a b p0 p1 p2 q0 q1 q2 : ZMod 2,
    z6Tr ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) = 1 →
    z6Nrm ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) = 1 → ∀ i : Fin 8,
    z6cU (z6Bar ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O)) (z6E i) =
      z6cU ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O)
        (z6cU ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) (z6E i)) := by
  decide +kernel

theorem z6_F3 : ∀ u : z6O, z6Tr u = 1 → z6Nrm u = 1 → ∀ i : Fin 8,
    z6cU (z6Bar u) (z6E i) = z6cU u (z6cU u (z6E i)) :=
  z6_coords (fun u => z6Tr u = 1 → z6Nrm u = 1 → ∀ i : Fin 8,
    z6cU (z6Bar u) (z6E i) = z6cU u (z6cU u (z6E i))) z6_F3_c

set_option synthInstance.maxSize 4096 in
theorem z6_F4_c : ∀ a b p0 p1 p2 q0 q1 q2 c d s0 s1 s2 t0 t1 t2 : ZMod 2,
    z6Tr ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) = 1 →
    z6Nrm ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) = 1 →
    z6Tr ((c, ![s0, s1, s2], ![t0, t1, t2], d) : z6O) = 0 →
    z6cU ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) ((c, ![s0, s1, s2], ![t0, t1, t2], d) : z6O) =
        ((c, ![s0, s1, s2], ![t0, t1, t2], d) : z6O) →
    s0 = 0 ∧ s1 = 0 ∧ s2 = 0 ∧ t0 = 0 ∧ t1 = 0 ∧ t2 = 0 ∧ c = d := by
  decide +kernel

theorem z6_F4 : ∀ u : z6O, z6Tr u = 1 → z6Nrm u = 1 → ∀ x : z6O, z6Tr x = 0 →
    z6cU u x = x → x.2.1 = 0 ∧ x.2.2.1 = 0 ∧ x.1 = x.2.2.2 := by
  refine z6_coords (fun u => z6Tr u = 1 → z6Nrm u = 1 → ∀ x : z6O, z6Tr x = 0 →
    z6cU u x = x → x.2.1 = 0 ∧ x.2.2.1 = 0 ∧ x.1 = x.2.2.2) ?_
  intro a b p0 p1 p2 q0 q1 q2 h1 h2
  refine z6_coords (fun x => z6Tr x = 0 →
    z6cU ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) x = x →
      x.2.1 = 0 ∧ x.2.2.1 = 0 ∧ x.1 = x.2.2.2) ?_
  intro c d s0 s1 s2 t0 t1 t2 hx hfix
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ :=
    z6_F4_c a b p0 p1 p2 q0 q1 q2 c d s0 s1 s2 t0 t1 t2 h1 h2 hx hfix
  refine ⟨?_, ?_, e6⟩
  · funext i
    fin_cases i <;> simp [e0, e1, e2]
  · funext i
    fin_cases i <;> simp [e3, e4, e5]

set_option synthInstance.maxSize 4096 in
theorem z6_F5_c : ∀ a b p0 p1 p2 q0 q1 q2 : ZMod 2,
    z6Tr ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) = 1 →
    z6Nrm ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) = 1 →
    ∃ p ∈ z6Ms, z6S p.1 p.2 ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) =
      z6Bar ((a, ![p0, p1, p2], ![q0, q1, q2], b) : z6O) := by
  decide +kernel

theorem z6_F5 : ∀ u : z6O, z6Tr u = 1 → z6Nrm u = 1 →
    ∃ p ∈ z6Ms, z6S p.1 p.2 u = z6Bar u :=
  z6_coords (fun u => z6Tr u = 1 → z6Nrm u = 1 → ∃ p ∈ z6Ms, z6S p.1 p.2 u = z6Bar u) z6_F5_c

theorem z6_S1 : ∀ p ∈ z6Ms, ∀ i j : Fin 8,
    z6S p.1 p.2 (quasithinZornMul (z6E i) (z6E j)) =
      quasithinZornMul (z6S p.1 p.2 (z6E i)) (z6S p.1 p.2 (z6E j)) := by
  decide +kernel

theorem z6_S2 : ∀ p ∈ z6Ms, ∀ i : Fin 8, z6S p.1 p.2 (z6S p.1 p.2 (z6E i)) = z6E i := by
  decide +kernel

end CFSG.Quasithin.G112A2


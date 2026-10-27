
module

public import CFSG.Sporadic.Schreier.J4SConjBase
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

@[expose] def bfs11 (gens : Array (Array ℕ)) (s : ℕ) : Array ℕ × Array ℕ × Array ℕ := Id.run do
  let mut seen : Array Bool := Array.replicate 2048 false
  seen := seen.set! s true
  let mut pts : Array ℕ := #[s]
  let mut par : Array ℕ := #[0]
  let mut lab : Array ℕ := #[0]
  let mut i := 0
  for _ in [0:2048] do
    if i < pts.size then
      let p := pts[i]!
      for g in [0:gens.size] do
        let q := app11 gens[g]! p
        if !seen[q]! then
          seen := seen.set! q true
          pts := pts.push q
          par := par.push i
          lab := lab.push g
      i := i + 1
  return (pts, par, lab)

@[expose] def bfsOK (gens : Array (Array ℕ)) (s n : ℕ) (B : Array ℕ × Array ℕ × Array ℕ) :
    Bool :=
  B.1.size == n && B.2.1.size == n && B.2.2.size == n && B.1[0]! == s &&
    (List.range n).all fun i => decide (B.1[i]! < 2048) &&
      (i == 0 || (decide (B.2.1[i]! < i) && decide (B.2.2[i]! < gens.size) &&
        B.1[i]! == app11 gens[B.2.2[i]!]! B.1[B.2.1[i]!]!)) &&
      (List.range i).all fun k => B.1[k]! != B.1[i]!

section BFS

variable {gens : Array (Array ℕ)} {s n : ℕ} {B : Array ℕ × Array ℕ × Array ℕ}

theorem bfsOK_parts (hB : bfsOK gens s n B = true) :
    B.1[0]! = s ∧ ∀ i < n, B.1[i]! < 2048 ∧
      (0 < i → B.2.1[i]! < i ∧ B.2.2[i]! < gens.size ∧
        B.1[i]! = app11 gens[B.2.2[i]!]! B.1[B.2.1[i]!]!) ∧
      ∀ k < i, B.1[k]! ≠ B.1[i]! := by
  unfold bfsOK at hB
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne, ne_eq] at hB
  obtain ⟨⟨⟨⟨-, -⟩, -⟩, h0⟩, hall⟩ := hB
  refine ⟨h0, fun i hi => ?_⟩
  obtain ⟨⟨hlt, hpar⟩, hdist⟩ := hall i hi
  refine ⟨hlt, fun hi0 => ?_, hdist⟩
  rcases hpar with h | h
  · omega
  · exact ⟨h.1.1, h.1.2, h.2⟩

theorem bfsOK_lt (hB : bfsOK gens s n B = true) {i : ℕ} (hi : i < n) : B.1[i]! < 2048 :=
  ((bfsOK_parts hB).2 i hi).1

theorem bfsOK_ne (hB : bfsOK gens s n B = true) {i k : ℕ} (hi : i < n) (hk : k < n)
    (hik : i ≠ k) : B.1[i]! ≠ B.1[k]! := by
  rcases Nat.lt_or_gt_of_ne hik with h | h
  · exact ((bfsOK_parts hB).2 k hk).2.2 i h
  · exact fun e => ((bfsOK_parts hB).2 i hi).2.2 k h e.symm

theorem reach_of_bfsOK (hB : bfsOK gens s n B = true) (L : Subgroup J)
    (hgens : ∀ g < gens.size, ∃ k ∈ L, ∀ a, k * η a * k⁻¹ = η (app11 gens[g]! a)) :
    ∀ i < n, ∃ k ∈ L, k * η s * k⁻¹ = η B.1[i]! := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · refine ⟨1, L.one_mem, ?_⟩
      rw [(bfsOK_parts hB).1]
      group
    · obtain ⟨hp, hg, he⟩ := ((bfsOK_parts hB).2 i hi).2.1 hi0
      obtain ⟨k, hk, hke⟩ := ih _ hp (by omega)
      obtain ⟨kg, hkg, hkge⟩ := hgens _ hg
      refine ⟨kg * k, L.mul_mem hkg hk, ?_⟩
      rw [he, ← hkge, ← hke]
      group

end BFS

@[expose] def wordCols (w : List ℤ) : Array ℕ := Array.ofFn (n := 11) fun j => app11W w (2 ^ j.val)

theorem prod_ofFn_one : ∀ n : ℕ, (List.ofFn fun _ : Fin n => (1 : J)).prod = 1
  | 0 => rfl
  | n + 1 => by rw [List.ofFn_succ, List.prod_cons, prod_ofFn_one n, one_mul]

theorem prod_ofFn_single : ∀ {n : ℕ} (j : Fin n) (g : J),
    (List.ofFn fun i : Fin n => if i = j then g else 1).prod = g
  | 0, j, _ => j.elim0
  | n + 1, j, g => by
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases ?_ (fun j' => ?_) j
    · rw [ite_eq_left rfl]
      have h1 : (List.ofFn fun i : Fin n => if i.succ = (0 : Fin (n + 1)) then g else 1) =
          List.ofFn fun _ : Fin n => (1 : J) :=
        List.ofFn_inj.2 (funext fun i => ite_eq_right (Fin.succ_ne_zero i))
      rw [h1, prod_ofFn_one, mul_one]
    · rw [ite_eq_right (Fin.succ_ne_zero j').symm, one_mul]
      have h2 : (List.ofFn fun i : Fin n => if i.succ = j'.succ then g else 1) =
          List.ofFn fun i : Fin n => if i = j' then g else 1 :=
        List.ofFn_inj.2 (funext fun i => by simp only [Fin.succ_inj])
      rw [h2]
      exact prod_ofFn_single j' g

theorem η_two_pow (j : Fin 11) : η (2 ^ j.val) = u j := by
  unfold η
  have h : (List.ofFn fun i : Fin 11 => if (2 ^ j.val).testBit i then u i else 1) =
      List.ofFn fun i : Fin 11 => if i = j then u j else 1 := by
    refine List.ofFn_inj.2 (funext fun i => ?_)
    rw [Nat.testBit_two_pow]
    by_cases h : i = j
    · subst h
      rw [ite_eq_left (by simp), ite_eq_left rfl]
    · rw [ite_eq_right (by simpa [Fin.ext_iff, eq_comm] using h), ite_eq_right h]
  rw [h]
  exact prod_ofFn_single j (u j)

@[expose] def closedOK (gens : Array (Array ℕ)) (pts : Array ℕ) (n : ℕ) : Bool :=
  (List.range n).all fun i => (List.range gens.size).all fun g =>
    (List.range n).any fun k => pts[k]! == app11 gens[g]! pts[i]!

theorem closedOK_spec {gens : Array (Array ℕ)} {pts : Array ℕ} {n : ℕ}
    (h : closedOK gens pts n = true) :
    ∀ i < n, ∀ g < gens.size, ∃ k < n, pts[k]! = app11 gens[g]! pts[i]! := by
  intro i hi g hg
  unfold closedOK at h
  rw [List.all_eq_true] at h
  have h1 := h i (List.mem_range.2 hi)
  rw [List.all_eq_true] at h1
  have h2 := h1 g (List.mem_range.2 hg)
  obtain ⟨k, hk, e⟩ := List.any_eq_true.1 h2
  exact ⟨k, List.mem_range.1 hk, beq_iff_eq.1 e⟩

@[expose] def xyGens : Array (Array ℕ) := #[xColumns, yColumns]

@[expose] def xyInvGens : Array (Array ℕ) := #[xInvColumns, yInvColumns]

@[expose] def orb1 : Array ℕ × Array ℕ × Array ℕ := bfs11 xyGens 1

@[expose] def orb14 : Array ℕ × Array ℕ × Array ℕ := bfs11 xyGens 14

@[expose] def coverCheck : Bool :=
  (List.range 2048).all fun a => a == 0 || (List.range 1771).any (fun i => orb1.1[i]! == a) ||
    (List.range 276).any (fun i => orb14.1[i]! == a)

@[expose] noncomputable def sgen (m : ℕ) : J := signedWord x y (strongWords[m]!)

@[expose] def sCols (m : ℕ) : Array ℕ := wordCols (strongWords[m]!)

@[expose] def gens1 : Array (Array ℕ) := #[sCols 1, sCols 2, sCols 3, sCols 4, sCols 5, sCols 6,
  sCols 7, sCols 8]

@[expose] def gens2 : Array (Array ℕ) := #[sCols 3, sCols 4, sCols 5, sCols 7, sCols 8]

@[expose] def idx1 : Array ℕ := #[1, 2, 3, 4, 5, 6, 7, 8]

@[expose] def idx2 : Array ℕ := #[3, 4, 5, 7, 8]

@[expose] def fixCheck : Bool :=
  (List.range 8).all (fun g => app11 gens1[g]! 1 == 1) &&
    (List.range 5).all fun g => app11 gens2[g]! 1 == 1 && app11 gens2[g]! 2 == 2

@[expose] def orbB : Array ℕ × Array ℕ × Array ℕ := bfs11 gens1 2

@[expose] def orbC : Array ℕ × Array ℕ × Array ℕ := bfs11 gens2 4

theorem sgen_mem_K (m : ℕ) : sgen m ∈ K := signedWord_mem_K _

end CFSG.Sporadic.J4Schreier

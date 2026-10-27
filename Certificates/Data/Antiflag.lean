module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod

public section

namespace Certificates.Antiflag

abbrev Pt (n : ℕ) : Type := (Fin n → ZMod 2) × (Fin n → ZMod 2)

@[expose] def tv {n : ℕ} (i j : Fin n) (p : Pt n) : Pt n :=
  (p.1 + Pi.single i (p.1 j), p.2 + Pi.single j (p.2 i))

@[expose] def sw {n : ℕ} (p : Pt n) : Pt n := (p.2, p.1)

@[expose] def globalGens (n : ℕ) : List (Pt n → Pt n) :=
  sw :: (List.finRange n).flatMap fun i =>
    ((List.finRange n).filter fun j => j ≠ i).map fun j => tv i j

@[expose] def stabGens (n : ℕ) : List (Pt n → Pt n) :=
  sw :: ((List.finRange n).filter fun i => i.val ≠ 0).flatMap fun i =>
    ((List.finRange n).filter fun j => j ≠ i ∧ j.val ≠ 0).map fun j => tv i j

@[expose] def ev (n k : ℕ) : Fin n → ZMod 2 := fun i => if i.val = k then 1 else 0

@[expose] def base (n : ℕ) : Pt n := (ev n 0, ev n 0)

@[expose] def antiflags (n : ℕ) : Finset (Pt n) := Finset.univ.filter fun p => p.1 ⬝ᵥ p.2 = 1

@[expose] def reps (n : ℕ) : List (Pt n) :=
  [(ev n 0 + ev n 1, ev n 0), (ev n 0 + ev n 1, ev n 0 + ev n 2), (ev n 1, ev n 1),
    (ev n 0 + ev n 1, ev n 1)]

@[expose] def applyWord {n : ℕ} (gens : List (Pt n → Pt n)) (w : List ℕ) (p : Pt n) : Pt n :=
  w.foldr (fun i q => (gens.getD i id) q) p

@[expose] def Facts (n : ℕ) : Prop :=
  (∀ r ∈ reps n, r ∈ antiflags n) ∧
  (∀ ω ∈ antiflags n, ∃ w, applyWord (globalGens n) w (base n) = ω) ∧
  (∀ ω ∈ antiflags n, ω ≠ base n → ∃ r ∈ reps n, ∃ w, applyWord (stabGens n) w r = ω) ∧
  ∀ r ∈ reps n, ∃ w₀, applyWord (globalGens n) w₀ (base n) = r ∧
    ∀ ω ∈ antiflags n, ∃ w,
      applyWord (stabGens n ++ [applyWord (globalGens n) w₀]) w (base n) = ω

end Certificates.Antiflag

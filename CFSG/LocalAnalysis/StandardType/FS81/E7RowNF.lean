module

public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreE7Irr

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.E7Row

open scoped Matrix

inductive Gen
  | sw (i j : Fin 8)
  | ng (i j : Fin 8)
  | t1
  deriving DecidableEq

@[expose] def Gen.act : Gen → Coords 8 → Coords 8
  | .sw i j, v => fun k => v (Equiv.swap i j k)
  | .ng i j, v => fun k => if k = i ∨ k = j then -(v k) else v k
  | .t1, v => fun k => if k = 1 then -(v k) else v k

@[expose] def Gen.Valid : Gen → Prop
  | .sw i j => 2 ≤ i.val ∧ 2 ≤ j.val
  | .ng i j => 2 ≤ i.val ∧ 2 ≤ j.val ∧ i ≠ j
  | .t1 => True

instance (g : Gen) : Decidable g.Valid := by
  cases g <;> unfold Gen.Valid <;> infer_instance

@[expose] def frame : List (Fin 8) := [2, 3, 4, 5, 6, 7]

@[expose] def wtF (v : Coords 8) : ℕ := (frame.filter fun i => v i ≠ 0).length

@[expose] def prodF (v : Coords 8) : ZMod 3 := v 2 * v 3 * v 4 * v 5 * v 6 * v 7

@[expose] def negs (v : Coords 8) : List (Fin 8) := frame.filter fun i => v i = -1

@[expose] def framePairs : List (Fin 8 × Fin 8) :=
  [(2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 4), (3, 5), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7),
    (5, 6), (5, 7), (6, 7)]

@[expose] def frameAdj : List (Fin 8 × Fin 8) := [(2, 3), (3, 4), (4, 5), (5, 6), (6, 7)]

@[expose] def invs (v : Coords 8) : ℕ := (framePairs.filter fun p => v p.1 = 0 ∧ v p.2 ≠ 0).length

@[expose] def sgnPot (v : Coords 8) : ℕ :=
  if wtF v = 6 ∧ (negs v).length = 1 ∧ v 7 = -1 then 0 else (negs v).length

@[expose] def pot (v : Coords 8) : ℕ :=
  invs v * 64 + sgnPot v * 2 + if v 1 = -1 then 1 else 0

@[expose] def step (v : Coords 8) : Option Gen :=
  match frameAdj.find? (fun p => v p.1 = 0 ∧ v p.2 ≠ 0) with
  | some p => some (.sw p.1 p.2)
  | none =>
    if v 1 = -1 then some .t1 else
    match negs v with
    | i :: j :: _ => some (.ng i j)
    | [i] => if wtF v = 6 then (if i = 7 then none else some (.sw i 7)) else some (.ng i 7)
    | [] => none

@[expose] def nf (v : Coords 8) : Coords 8 := fun i =>
  if i = 0 then v 0 else if i = 1 then v 1 * v 1 else
    if i.val - 1 ≤ wtF v then (if wtF v = 6 ∧ i = 7 then prodF v else 1) else 0

set_option maxRecDepth 100000 in
theorem step_none : ∀ v : Coords 8, step v = none → nf v = v := by
  decide +kernel

@[expose] def StepOK (v : Coords 8) : Prop :=
  match step v with
  | none => True
  | some g => g.Valid ∧ pot (g.act v) < pot v ∧ nf (g.act v) = nf v

instance (v : Coords 8) : Decidable (StepOK v) := by
  unfold StepOK
  split <;> infer_instance

set_option maxRecDepth 100000 in
theorem step_some : ∀ v : Coords 8, StepOK v := by
  decide +kernel

theorem Gen.act_act (g : Gen) (v : Coords 8) : g.act (g.act v) = v := by
  funext k
  cases g with
  | sw i j => simp [Gen.act]
  | ng i j =>
    simp only [Gen.act]
    by_cases h : k = i ∨ k = j
    · rw [if_pos h, if_pos h]
      exact neg_neg _
    · rw [if_neg h, if_neg h]
  | t1 =>
    simp only [Gen.act]
    by_cases h : k = 1
    · rw [if_pos h, if_pos h]
      exact neg_neg _
    · rw [if_neg h, if_neg h]

theorem mem_iff_nf_mem {Ω : Set (Coords 8)} (hΩ : ∀ g : Gen, g.Valid → ∀ v ∈ Ω, g.act v ∈ Ω)
    (v : Coords 8) : v ∈ Ω ↔ nf v ∈ Ω := by
  induction h : pot v using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    have hs := step_some v
    unfold StepOK at hs
    rcases hstep : step v with _ | g
    · rw [step_none v hstep]
    · rw [hstep] at hs
      obtain ⟨hg, hpot, hnf⟩ := hs
      have key := ih (pot (g.act v)) (h ▸ hpot) (g.act v) rfl
      rw [hnf] at key
      rw [← key]
      constructor
      · exact hΩ g hg v
      · intro hv
        have := hΩ g hg _ hv
        rwa [Gen.act_act] at this

end CFSG.StandardType.FrameRoute.FS81.E7Row

end

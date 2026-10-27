module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheck
public import Mathlib.Data.List.Basic

public section

namespace CFSG.KC.ONanSmall

variable {M : Type*} [Group M] {D : Type*}

@[expose] def pickRun (L₀ : List M) (inv : M → Bool) (conj : M → M → M → Bool)
    (gen : D → Option M) : List M → List M → List (ℕ × D) → Option (List M)
  | reps, [], _ => some reps
  | reps, t :: ts, W =>
    if inv t then
      match W with
      | [] => none
      | (j, d) :: W' =>
        if j == reps.length then
          if L₀.any fun g => reps.any fun r => conj g t r then none
          else pickRun L₀ inv conj gen (reps ++ [t]) ts W'
        else
          match gen d with
          | some g => if j < reps.length && conj g t (reps.getD j 1) then
              pickRun L₀ inv conj gen reps ts W' else none
          | none => none
    else pickRun L₀ inv conj gen reps ts W

@[expose] def genP : List (List M) → List ℕ → Option M
  | [], [] => some 1
  | T :: Ts, i :: d =>
    match T[i]?, genP Ts d with
    | some t, some x => some (t * x)
    | _, _ => none
  | _, _ => none

end CFSG.KC.ONanSmall

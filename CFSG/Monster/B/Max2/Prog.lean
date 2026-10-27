module

public import Mathlib.Algebra.Group.Hom.Defs
public import Certificates.Data.CFSGNative.MonsterB.IntertwinerData

public section

namespace CFSG.Monster.B

open Bin

@[expose] def progStepM {M : Type*} [Monoid M] (r : ℕ → M) (ins : ℕ × ℕ × ℕ) : ℕ → M :=
  Function.update r ins.2.2 (r ins.1 * r ins.2.1)

@[expose] def progInit {M : Type*} [Monoid M] (a b : M) : ℕ → M :=
  fun i => if i = 1 then a else if i = 2 then b else 1

@[expose] def progRegs {M : Type*} [Monoid M] (a b : M) : ℕ → M :=
  max2Prog.foldl progStepM (progInit a b)

theorem map_foldl_progStepM {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) :
    ∀ (l : List (ℕ × ℕ × ℕ)) (r : ℕ → M) (k : ℕ),
      f (l.foldl progStepM r k) = l.foldl progStepM (fun i => f (r i)) k
  | [], r, k => rfl
  | ins :: l, r, k => by
    rw [List.foldl_cons, List.foldl_cons, map_foldl_progStepM f l]
    have e : (fun i => f (progStepM r ins i)) = progStepM (fun i => f (r i)) ins := by
      funext i
      unfold progStepM
      by_cases h : i = ins.2.2
      · subst h; simp
      · simp [Function.update_of_ne h]
    rw [e]

theorem map_progRegs {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) (a b : M) (k : ℕ) :
    f (progRegs a b k) = progRegs (f a) (f b) k := by
  unfold progRegs
  rw [map_foldl_progStepM]
  have e : (fun i => f (progInit a b i)) = progInit (f a) (f b) := by
    funext i
    unfold progInit
    split_ifs <;> simp
  rw [e]

end CFSG.Monster.B

end

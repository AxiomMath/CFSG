module

public import CFSG.LieType.Multipliers.CoverWords
public import CFSG.Certificates.Kernel.Misc.Coset.PG

public section

namespace CertificateChecks.KernelCosetJ

open CFSG.LieType.Multipliers CFSG.KC.MiscCoset

@[expose] def invRevN (u : List (ℕ × Bool)) : List (ℕ × Bool) :=
  (u.map fun l => (l.1, !l.2)).reverse

@[expose] def commN (u v : List (ℕ × Bool)) : List (ℕ × Bool) :=
  u ++ v ++ invRevN u ++ invRevN v

@[expose] def coverN (m : ℕ) (R : List (List (ℕ × Bool))) (w : Fin m → List (ℕ × Bool)) :
    List (List (ℕ × Bool)) :=
  (List.finRange m).flatMap (fun i => R.map fun r => commN [(i.val, true)] r) ++
    (List.finRange m).map fun i => (i.val, false) :: w i

theorem encW_invRev {m : ℕ} (u : List (Fin m × Bool)) :
    encW (FreeGroup.invRev u) = invRevN (encW u) := by
  simp [encW, invRevN, FreeGroup.invRev, List.map_reverse]

theorem encW_commWord {m : ℕ} (u v : List (Fin m × Bool)) :
    encW (commWord u v) = commN (encW u) (encW v) := by
  rw [commWord, commN, ← encW_invRev, ← encW_invRev]
  simp only [encW, List.map_append]

theorem map_encW_coverWords {m : ℕ} (R : List (List (Fin m × Bool)))
    (w : Fin m → List (Fin m × Bool)) :
    (coverWords R w).map encW = coverN m (R.map encW) fun i => encW (w i) := by
  simp only [coverWords, coverN, List.map_append, List.map_flatMap, List.map_map]
  congr 1
  congr 1
  funext i
  simp only [Function.comp_def]
  congr 1
  funext r
  rw [encW_commWord]
  rfl

@[expose] def decodeW (m : ℕ) [NeZero m] (ws : List (List (ℕ × Bool))) :
    List (List (Fin m × Bool)) :=
  ws.map (List.map fun l => (Fin.ofNat m l.1, l.2))

theorem decode_encW {m : ℕ} [NeZero m] (w : List (Fin m × Bool)) :
    (encW w).map (fun l => (Fin.ofNat m l.1, l.2)) = w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    simp only [encW, List.map_cons] at ih ⊢
    rw [ih]
    simp [Fin.ofNat, Nat.mod_eq_of_lt l.1.isLt]

theorem decodeW_map_encW {m : ℕ} [NeZero m] (ws : List (List (Fin m × Bool))) :
    decodeW m (ws.map encW) = ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [decodeW, List.map_cons] at ih ⊢
    rw [ih, decode_encW]

theorem eq_decodeW {m : ℕ} [NeZero m] {ws : List (List (Fin m × Bool))}
    {L : List (List (ℕ × Bool))} (h : ws.map encW = L) : ws = decodeW m L := by
  rw [← h, decodeW_map_encW]

end CertificateChecks.KernelCosetJ

end

module

public import CFSG.Permutation.FinPackCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11A11KernK

open Equiv Finset CFSG.Permutation.FinPack

theorem h16 : 8 ≤ 16 := by norm_num

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def iffB (a b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false b) b a

theorem andB_iff {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem iffB_iff {a b : Bool} : iffB a b = true ↔ (a = true ↔ b = true) := by
  cases a <;> cases b <;> decide

@[expose] noncomputable def sameB (i j k l : ℕ) : Bool :=
  andB (iffB (Nat.beq (i / 4) (j / 4)) (Nat.beq (k / 4) (l / 4)))
    (iffB (Nat.beq (i / 2) (j / 2)) (Nat.beq (k / 2) (l / 2)))

theorem sameB_iff {i j k l : ℕ} : sameB i j k l = true ↔
    ((i / 4 = j / 4 ↔ k / 4 = l / 4) ∧ (i / 2 = j / 2 ↔ k / 2 = l / 2)) := by
  rw [sameB, andB_iff, iffB_iff, iffB_iff, Nat.beq_eq, Nat.beq_eq, Nat.beq_eq, Nat.beq_eq]

@[expose] noncomputable def blkB (c : ℕ) : Bool :=
  allLtK (fun i => allLtK (fun j => sameB i j (rd c i) (rd c j)) 8) 8

@[expose] noncomputable def pullB (c G : ℕ) : Bool :=
  allLtK (fun x => allLtK (fun y => sameB (rd c x) (rd c y) (rd c (rd G x)) (rd c (rd G y))) 8) 8

theorem rd_enc8 (w : Perm (Fin 8)) {i : ℕ} (hi : i < 8) : rd (enc w) i = (w ⟨i, hi⟩ : ℕ) :=
  rd_enc h16 w ⟨i, hi⟩

theorem allLt8_iff {f : ℕ → ℕ → Bool} :
    allLtK (fun i => allLtK (fun j => f i j) 8) 8 = true ↔
      ∀ i j : Fin 8, f i j = true := by
  rw [allLtK_iff]
  constructor
  · intro H i j
    exact allLtK_iff.1 (H i i.2) j j.2
  · intro H i hi
    rw [allLtK_iff]
    intro j hj
    exact H ⟨i, hi⟩ ⟨j, hj⟩

theorem blkB_iff (w : Perm (Fin 8)) : blkB (enc w) = true ↔
    ∀ i j : Fin 8, (((i : ℕ) / 4 = (j : ℕ) / 4 ↔ ((w i : Fin 8) : ℕ) / 4 = ((w j : Fin 8) : ℕ) / 4) ∧
      ((i : ℕ) / 2 = (j : ℕ) / 2 ↔ ((w i : Fin 8) : ℕ) / 2 = ((w j : Fin 8) : ℕ) / 2)) := by
  rw [blkB, allLt8_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  change sameB (i : ℕ) (j : ℕ) (rd (enc w) i) (rd (enc w) j) = true ↔ _
  rw [sameB_iff, rd_enc h16 w i, rd_enc h16 w j]

theorem pullB_iff (w g : Perm (Fin 8)) {G : ℕ} (hG : enc g = G) : pullB (enc w) G = true ↔
    ∀ x y : Fin 8, ((((w x : Fin 8) : ℕ) / 4 = ((w y : Fin 8) : ℕ) / 4 ↔
        ((w (g x) : Fin 8) : ℕ) / 4 = ((w (g y) : Fin 8) : ℕ) / 4) ∧
      (((w x : Fin 8) : ℕ) / 2 = ((w y : Fin 8) : ℕ) / 2 ↔
        ((w (g x) : Fin 8) : ℕ) / 2 = ((w (g y) : Fin 8) : ℕ) / 2)) := by
  rw [← hG, pullB, allLt8_iff]
  refine forall_congr' fun x => forall_congr' fun y => ?_
  change sameB (rd (enc w) x) (rd (enc w) y) (rd (enc w) (rd (enc g) x)) (rd (enc w) (rd (enc g) y)) =
    true ↔ _
  rw [sameB_iff, rd_enc h16 g x, rd_enc h16 g y, rd_enc h16 w x, rd_enc h16 w y, rd_enc h16 w (g x),
    rd_enc h16 w (g y)]

theorem cnt_blkB : cntK 8 blkB 8 0 0 0 = 128 := by decide +kernel

theorem card_blk_K (P : Perm (Fin 8) → Prop) [DecidablePred P]
    (hP : ∀ w, P w ↔ ∀ i j : Fin 8,
      (((i : ℕ) / 4 = (j : ℕ) / 4 ↔ ((w i : Fin 8) : ℕ) / 4 = ((w j : Fin 8) : ℕ) / 4) ∧
        ((i : ℕ) / 2 = (j : ℕ) / 2 ↔ ((w i : Fin 8) : ℕ) / 2 = ((w j : Fin 8) : ℕ) / 2))) :
    (univ.filter P).card = 128 := by
  rw [Finset.filter_congr fun w _ => (hP w).trans (blkB_iff w).symm, card_filter_eq_cntK, cnt_blkB]

@[expose] noncomputable def qPull (c : ℕ) : Bool :=
  blkB c || !(pullB c 1733567248 && pullB c 1985220658 && pullB c 839939668)

theorem qPull_walk : walkK 8 qPull 8 0 0 0 = true := by decide +kernel

theorem pull_blk_K (g₁ g₂ g₃ : Perm (Fin 8)) (h₁ : enc g₁ = 1733567248)
    (h₂ : enc g₂ = 1985220658) (h₃ : enc g₃ = 839939668) (w : Perm (Fin 8))
    (p₁ : pullB (enc w) (enc g₁) = true) (p₂ : pullB (enc w) (enc g₂) = true)
    (p₃ : pullB (enc w) (enc g₃) = true) : blkB (enc w) = true := by
  have h := walkK_sound qPull_walk w
  rw [qPull.eq_1, ← h₁, ← h₂, ← h₃, p₁, p₂, p₃] at h
  simpa using h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11A11KernK

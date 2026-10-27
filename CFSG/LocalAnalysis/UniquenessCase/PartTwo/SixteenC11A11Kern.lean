module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic.NormNum.Ineq
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11A11KernK

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Equiv

@[expose] def S16C11A11Blk8F (σ : Fin 8 → Fin 8) : Prop :=
  ∀ i j : Fin 8, (((i : ℕ) / 4 = (j : ℕ) / 4 ↔ ((σ i : Fin 8) : ℕ) / 4 = ((σ j : Fin 8) : ℕ) / 4) ∧
    ((i : ℕ) / 2 = (j : ℕ) / 2 ↔ ((σ i : Fin 8) : ℕ) / 2 = ((σ j : Fin 8) : ℕ) / 2))

instance (σ : Fin 8 → Fin 8) : Decidable (S16C11A11Blk8F σ) := by
  unfold S16C11A11Blk8F
  infer_instance

@[expose] def S16C11A11Blk8 (w : Perm (Fin 8)) : Prop :=
  ∀ i j : Fin 8, (((i : ℕ) / 4 = (j : ℕ) / 4 ↔ ((w i : Fin 8) : ℕ) / 4 = ((w j : Fin 8) : ℕ) / 4) ∧
    ((i : ℕ) / 2 = (j : ℕ) / 2 ↔ ((w i : Fin 8) : ℕ) / 2 = ((w j : Fin 8) : ℕ) / 2))

instance : DecidablePred S16C11A11Blk8 := fun w => by
  unfold S16C11A11Blk8
  infer_instance

theorem s16c11_a11_blk8_iff_blk8F (w : Perm (Fin 8)) :
    S16C11A11Blk8 w ↔ S16C11A11Blk8F w :=
  Iff.rfl

@[expose] def S16C11A11Pull (a : Fin 8 → Fin 8) (g : Perm (Fin 8)) : Prop :=
  ∀ x y : Fin 8, (((a x : Fin 8) : ℕ) / 4 = ((a y : Fin 8) : ℕ) / 4 ↔
      ((a (g x) : Fin 8) : ℕ) / 4 = ((a (g y) : Fin 8) : ℕ) / 4) ∧
    (((a x : Fin 8) : ℕ) / 2 = ((a y : Fin 8) : ℕ) / 2 ↔
      ((a (g x) : Fin 8) : ℕ) / 2 = ((a (g y) : Fin 8) : ℕ) / 2)

instance (a : Fin 8 → Fin 8) (g : Perm (Fin 8)) : Decidable (S16C11A11Pull a g) := by
  unfold S16C11A11Pull
  infer_instance

@[expose] def S16C11A11PullLt (k : ℕ) (a : Fin 8 → Fin 8) (g : Perm (Fin 8)) : Prop :=
  ∀ x y : Fin 8, ((x : ℕ) < k ∧ (y : ℕ) < k ∧ ((g x : Fin 8) : ℕ) < k ∧
      ((g y : Fin 8) : ℕ) < k) →
    ((((a x : Fin 8) : ℕ) / 4 = ((a y : Fin 8) : ℕ) / 4 ↔
        ((a (g x) : Fin 8) : ℕ) / 4 = ((a (g y) : Fin 8) : ℕ) / 4) ∧
      (((a x : Fin 8) : ℕ) / 2 = ((a y : Fin 8) : ℕ) / 2 ↔
        ((a (g x) : Fin 8) : ℕ) / 2 = ((a (g y) : Fin 8) : ℕ) / 2))

instance (k : ℕ) (a : Fin 8 → Fin 8) (g : Perm (Fin 8)) : Decidable (S16C11A11PullLt k a g) := by
  unfold S16C11A11PullLt
  infer_instance

@[expose] def s16c11A11g1 : Perm (Fin 8) := swap 2 3 * swap 6 7

@[expose] def s16c11A11g2 : Perm (Fin 8) := swap 0 2 * swap 1 3

@[expose] def s16c11A11g3 : Perm (Fin 8) := swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7

@[expose] def S16C11A11PullLt3 (k : ℕ) (a : Fin 8 → Fin 8) : Prop :=
  S16C11A11PullLt k a s16c11A11g1 ∧ S16C11A11PullLt k a s16c11A11g2 ∧
    S16C11A11PullLt k a s16c11A11g3

instance (k : ℕ) (a : Fin 8 → Fin 8) : Decidable (S16C11A11PullLt3 k a) := by
  unfold S16C11A11PullLt3
  infer_instance

@[expose] def S16C11A11Tab (l : List (Fin 8)) : Fin 8 → Fin 8 := fun x => l.getD (x : ℕ) 0

@[expose] def S16C11A11Search : (k : ℕ) → (acc : List (Fin 8)) → Prop
  | 0, acc => S16C11A11Blk8F (S16C11A11Tab acc)
  | k + 1, acc => ∀ f : Fin 8, f ∉ acc →
      S16C11A11PullLt3 (acc.length + 1) (S16C11A11Tab (acc ++ [f])) →
        S16C11A11Search k (acc ++ [f])

instance S16C11A11SearchDec : (k : ℕ) → (acc : List (Fin 8)) → Decidable (S16C11A11Search k acc)
  | 0, acc => by
      unfold S16C11A11Search
      infer_instance
  | k + 1, acc => by
      unfold S16C11A11Search
      haveI : ∀ f : Fin 8, Decidable (S16C11A11Search k (acc ++ [f])) :=
        fun f => S16C11A11SearchDec k (acc ++ [f])
      infer_instance

theorem s16c11_a11_card_blk8 :
    (Finset.univ.filter fun w : Perm (Fin 8) => S16C11A11Blk8 w).card = 128 :=
  SixteenC11A11KernK.card_blk_K _ fun _ => Iff.rfl

theorem s16c11_a11_search : S16C11A11Search 8 [] := by
  have F : ∀ a : Fin 8 → Fin 8, Function.Injective a → S16C11A11PullLt3 8 a →
      S16C11A11Blk8F a := by
    intro a ha hP
    let σ : Perm (Fin 8) := Equiv.ofBijective a (Finite.injective_iff_bijective.1 ha)
    have pull : ∀ g : Perm (Fin 8), S16C11A11PullLt 8 a g →
        SixteenC11A11KernK.pullB (CFSG.Permutation.FinPack.enc σ)
          (CFSG.Permutation.FinPack.enc g) = true := by
      intro g hg
      rw [SixteenC11A11KernK.pullB_iff σ g rfl]
      intro x y
      exact hg x y ⟨x.2, y.2, (g x).2, (g y).2⟩
    obtain ⟨p1, p2, p3⟩ := hP
    have hb := SixteenC11A11KernK.pull_blk_K s16c11A11g1 s16c11A11g2 s16c11A11g3
      (by decide +kernel) (by decide +kernel) (by decide +kernel) σ (pull _ p1) (pull _ p2)
      (pull _ p3)
    rw [SixteenC11A11KernK.blkB_iff] at hb
    exact hb
  have C : ∀ k (acc : List (Fin 8)), acc.Nodup → acc.length + k = 8 →
      (k = 0 → S16C11A11PullLt3 8 (S16C11A11Tab acc)) → S16C11A11Search k acc := by
    intro k
    induction k with
    | zero =>
      intro acc hnd hl hP
      rw [S16C11A11Search.eq_1]
      refine F _ (fun x y hxy => ?_) (hP rfl)
      have hx : (x : ℕ) < acc.length := by have := x.2; omega
      have hy : (y : ℕ) < acc.length := by have := y.2; omega
      have e : acc[(x : ℕ)] = acc[(y : ℕ)] := by
        have ex : S16C11A11Tab acc x = acc[(x : ℕ)] := by
          rw [S16C11A11Tab, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx, Option.getD_some]
        have ey : S16C11A11Tab acc y = acc[(y : ℕ)] := by
          rw [S16C11A11Tab, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hy, Option.getD_some]
        rw [← ex, ← ey, hxy]
      exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 e)
    | succ k ih =>
      intro acc hnd hl _
      rw [S16C11A11Search.eq_2]
      intro f hf hP
      refine ih (acc ++ [f]) (List.Nodup.append hnd (List.nodup_singleton f)
        (List.disjoint_singleton.2 hf)) (by rw [List.length_append, List.length_singleton]; omega)
        fun hk => ?_
      have e : acc.length + 1 = 8 := by omega
      rw [e] at hP
      exact hP
  exact C 8 [] List.nodup_nil rfl fun h => absurd h (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

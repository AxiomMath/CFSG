module

public import CFSG.RankThree.GF2n.Stroth80.Sec715TriOctId
public import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases

public section

namespace CFSG.RankThree.GF2n.Stroth80.Tri

abbrev SignVec := Fin 4 → Bool

namespace SignVec

@[expose] def neg (s : SignVec) : SignVec := fun i => !s i

@[expose] def minusCount (s : SignVec) : ℕ := (Finset.univ.filter fun i => s i = false).card

@[expose] def step (i j : Fin 4) (u v : Bool) (s : SignVec) : Option SignVec :=
  if s i = !u ∧ s j = !v then some (Function.update (Function.update s i u) j v) else none

theorem neg_apply (s : SignVec) (i : Fin 4) : s.neg i = !s i := rfl

theorem step_minusCount_mod : ∀ (i j : Fin 4) (u v : Bool) (s s' : SignVec), i ≠ j →
    step i j u v s = some s' → s'.minusCount % 2 = s.minusCount % 2 := by
  decide

theorem step_ne_neg : ∀ (i j : Fin 4) (u v : Bool) (s : SignVec), i ≠ j →
    step i j u v s ≠ some s.neg := by
  decide

theorem step_neg_iff : ∀ (i j : Fin 4) (u v : Bool) (s s' : SignVec), i ≠ j →
    (step i j u v s' = some s.neg ↔ step i j u v s = some s'.neg) := by
  decide

theorem step_apply_left {i j : Fin 4} {u v : Bool} {s s' : SignVec} (hij : i ≠ j)
    (h : step i j u v s = some s') : s' i = u := by
  by_cases hc : s i = !u ∧ s j = !v
  · rw [step, if_pos hc, Option.some.injEq] at h
    subst h
    rw [Function.update_of_ne hij, Function.update_self]
  · rw [step, if_neg hc] at h
    exact absurd h (by simp)

theorem step_not_both {i j : Fin 4} {u v : Bool} {s₁ s₂ t : SignVec} (hij : i ≠ j) :
    ¬ (step i j u v s₁ = some t ∧ step i j u v s₂ = some t.neg) := by
  rintro ⟨h1, h2⟩
  have e1 := step_apply_left hij h1
  have e2 := step_apply_left hij h2
  rw [neg_apply, e1] at e2
  cases u <;> simp at e2

theorem step_neg_neg : ∀ (i j : Fin 4) (u v : Bool) (s s' : SignVec), i ≠ j →
    step i j u v s = some s' → step i j u v s'.neg = some s.neg := by
  decide

theorem step_ne_self : ∀ (i j : Fin 4) (u v : Bool) (s s' : SignVec), i ≠ j →
    step i j u v s = some s' → s' ≠ s := by
  decide

@[expose] def Adj (s s' : SignVec) : Prop := ∃ i j u v, i ≠ j ∧ step i j u v s = some s'

instance : DecidableRel Adj := fun s s' => by unfold Adj; infer_instance

theorem step_conn : ∀ s s' : SignVec, s.minusCount % 2 = s'.minusCount % 2 →
    s = s' ∨ Adj s s' ∨ ∃ s'', Adj s s'' ∧ Adj s'' s' := by
  decide

end SignVec

structure ZLab (e : ℕ) where
  lab : Fin 4 ⊕ Fin 4 → SignVec
  injective : Function.Injective lab
  minusCount_mod : ∀ m, (lab m).minusCount % 2 = e % 2
  surjective : ∀ s : SignVec, s.minusCount % 2 = e % 2 → ∃ m, lab m = s
  swap : ∀ m, lab m.swap = (lab m).neg

@[expose] def labEven : Fin 4 ⊕ Fin 4 → SignVec :=
  Sum.elim ![![true, true, true, true], ![true, true, false, false],
      ![true, false, true, false], ![true, false, false, true]]
    ![![false, false, false, false], ![false, false, true, true],
      ![false, true, false, true], ![false, true, true, false]]

@[expose] def labOdd : Fin 4 ⊕ Fin 4 → SignVec :=
  Sum.elim (fun k i => decide (i = k)) (fun k i => decide (i ≠ k))

@[expose] def flip3 (s : SignVec) : SignVec := Function.update s 3 (!s 3)

@[expose] def zlabEven : ZLab 0 where
  lab := labEven
  injective := by decide
  minusCount_mod := by decide
  surjective := by decide
  swap := by decide

@[expose] def zlabOdd : ZLab 1 where
  lab := labOdd
  injective := by decide
  minusCount_mod := by decide
  surjective := by decide
  swap := by decide

@[expose] def zlabEvenFlip : ZLab 1 where
  lab m := flip3 (labEven m)
  injective := by decide
  minusCount_mod := by decide
  surjective := by decide
  swap := by decide

@[expose] def zlabOddFlip : ZLab 0 where
  lab m := flip3 (labOdd m)
  injective := by decide
  minusCount_mod := by decide
  surjective := by decide
  swap := by decide

@[expose] def octMulTab : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4 → Option (Fin 4 ⊕ Fin 4)
  | .inl i, .inl j =>
    ![![some (.inl 0), some (.inl 1), some (.inl 2), some (.inl 3)],
      ![none, none, some (.inr 3), some (.inr 2)],
      ![none, some (.inr 3), none, some (.inr 1)],
      ![none, some (.inr 2), some (.inr 1), none]] i j
  | .inl i, .inr j =>
    ![![none, none, none, none],
      ![some (.inl 1), some (.inl 0), none, none],
      ![some (.inl 2), none, some (.inl 0), none],
      ![some (.inl 3), none, none, some (.inl 0)]] i j
  | .inr i, .inl j =>
    ![![none, none, none, none],
      ![some (.inr 1), some (.inr 0), none, none],
      ![some (.inr 2), none, some (.inr 0), none],
      ![some (.inr 3), none, none, some (.inr 0)]] i j
  | .inr i, .inr j =>
    ![![some (.inr 0), some (.inr 1), some (.inr 2), some (.inr 3)],
      ![none, none, some (.inl 3), some (.inl 2)],
      ![none, some (.inl 3), none, some (.inl 1)],
      ![none, some (.inl 2), some (.inl 1), none]] i j

set_option maxHeartbeats 2000000 in
theorem octMul_single_single {K : Type*} [CommRing K] [CharP K 2] (m n : Fin 4 ⊕ Fin 4) :
    octMul (Pi.single m 1 : Oct K) (Pi.single n 1) =
      (octMulTab m n).elim 0 (fun p => Pi.single p 1) := by
  rcases m with i | i <;> rcases n with j | j <;> fin_cases i <;> fin_cases j <;>
  refine oct_ext_coords ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
  simp only [octA_octMul, octB_octMul, octU_octMul, octW_octMul, dot3, cross3_apply_zero,
    cross3_apply_one, cross3_apply_two] <;>
  simp [octMulTab, octA, octB, octU, octW, Pi.single_apply, CharTwo.neg_eq]

@[expose] def natIdx (k : Fin 4) (r : Bool) : Fin 4 ⊕ Fin 4 := if r then .inl k else .inr k

structure ZLabPair (e : ℕ) where
  X : ZLab e
  Y : ZLab (1 - e)
  σ : Fin 4 ⊕ Fin 4 ≃ Fin 4 ⊕ Fin 4
  σ_pair : ∀ i, (σ (.inl i) = .inl i ∨ σ (.inl i) = .inr i) ∧ σ (.inr i) = (σ (.inl i)).swap
  mul_some : ∀ (m n : Fin 4 ⊕ Fin 4) (k : Fin 4), (∀ i, X.lab m i = Y.lab n i ↔ i = k) →
    octMulTab m n = some (σ (natIdx k (X.lab m k)))
  mul_none : ∀ (m n : Fin 4 ⊕ Fin 4), (¬ ∃ k, ∀ i, X.lab m i = Y.lab n i ↔ i = k) →
    octMulTab m n = none

@[expose] def swap3 : Fin 4 ⊕ Fin 4 ≃ Fin 4 ⊕ Fin 4 :=
  Function.Involutive.toPerm
    (fun m => match m with
      | .inl i => if i = 3 then .inr 3 else .inl i
      | .inr i => if i = 3 then .inl 3 else .inr i)
    (by intro m; revert m; decide)

@[expose] def zlabPair : ∀ (e : ℕ), e < 2 → ZLabPair e
  | 0, _ =>
    { X := zlabEven
      Y := zlabOdd
      σ := Equiv.refl _
      σ_pair := by decide
      mul_some := by decide
      mul_none := by decide }
  | 1, _ =>
    { X := zlabEvenFlip
      Y := zlabOddFlip
      σ := swap3
      σ_pair := by decide
      mul_some := by decide
      mul_none := by decide }
  | e + 2, h => absurd h (by omega)

end CFSG.RankThree.GF2n.Stroth80.Tri

end

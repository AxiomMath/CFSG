module

public import CFSG.Quasithin.Background.G6Natural
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin

open G6

abbrev lka_E : Type := ↥(coreMod 5)

@[expose] def lka_w : lka_E :=
  ⟨Multiplicative.ofAdd ![1, 1, 1, 1, 0], by rw [mem_coreMod]; decide⟩

@[expose] def lka_t1 : ↥(alternatingGroup (Fin 5)) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def lka_t2 : ↥(alternatingGroup (Fin 5)) :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def lka_diag (γ : ↥(alternatingGroup (Fin 5))) (x : lka_E × lka_E) : lka_E × lka_E :=
  (coreAct 5 γ.1 x.1, coreAct 5 γ.1 x.2)

@[expose] def lka_v (i : Fin 5) : PermMod 5 :=
  Multiplicative.ofAdd (fun j => if j = i then 0 else 1)

@[expose] def lka_g (i : Fin 5) : Equiv.Perm (Fin 5) :=
  if i = 0 then Equiv.swap 0 4 * Equiv.swap 1 2
  else if i = 1 then Equiv.swap 1 4 * Equiv.swap 2 3
  else if i = 2 then Equiv.swap 2 4 * Equiv.swap 0 1
  else if i = 3 then Equiv.swap 3 4 * Equiv.swap 0 1
  else 1

theorem lka_fix_pair (m : lka_E) (h1 : coreAct 5 lka_t1.1 m = m) (h2 : coreAct 5 lka_t2.1 m = m) :
    m = 1 ∨ m = lka_w := by
  have aux : ∀ x : PermMod 5, (∑ i, Multiplicative.toAdd x i = 0) →
      permAct 5 (Equiv.swap 0 1 * Equiv.swap 2 3) x = x →
      permAct 5 (Equiv.swap 0 2 * Equiv.swap 1 3) x = x →
      x = 1 ∨ x = Multiplicative.ofAdd ![1, 1, 1, 1, 0] := by
    decide
  obtain ⟨x, hx⟩ := m
  have h1' : permAct 5 (Equiv.swap 0 1 * Equiv.swap 2 3) x = x := congrArg Subtype.val h1
  have h2' : permAct 5 (Equiv.swap 0 2 * Equiv.swap 1 3) x = x := congrArg Subtype.val h2
  rcases aux x hx h1' h2' with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem lka_gen (P : lka_E → Prop) (h1 : P 1) (hmul : ∀ a b, P a → P b → P (a * b))
    (hact : ∀ (γ : ↥(alternatingGroup (Fin 5))) (m : lka_E), P m → P (coreAct 5 γ.1 m))
    (hw : P lka_w) (m : lka_E) : P m := by
  have hmemV : ∀ i : Fin 5, lka_v i ∈ coreMod 5 := by
    intro i
    rw [mem_coreMod]
    revert i
    decide
  have hG : ∀ i : Fin 5, lka_g i ∈ alternatingGroup (Fin 5) := by
    intro i
    rw [Equiv.Perm.mem_alternatingGroup]
    revert i
    decide
  have hact5 : ∀ i : Fin 5, permAct 5 (lka_g i) (lka_w : PermMod 5) = lka_v i := by
    intro i
    revert i
    decide
  have hV : ∀ i : Fin 5, P ⟨lka_v i, hmemV i⟩ := by
    intro i
    have := hact ⟨lka_g i, hG i⟩ lka_w hw
    have e : coreAct 5 (lka_g i) lka_w = ⟨lka_v i, hmemV i⟩ := Subtype.ext (hact5 i)
    rwa [show (⟨lka_g i, hG i⟩ : ↥(alternatingGroup (Fin 5))).1 = lka_g i from rfl, e] at this
  have cases : ∀ x : PermMod 5, (∑ i, Multiplicative.toAdd x i = 0) →
      x = 1 ∨ (∃ i, x = lka_v i) ∨ ∃ i j, x = lka_v i * lka_v j := by
    decide
  obtain ⟨x, hx⟩ := m
  rcases cases x hx with rfl | ⟨i, rfl⟩ | ⟨i, j, rfl⟩
  · exact h1
  · exact hV i
  · exact hmul ⟨lka_v i, hmemV i⟩ ⟨lka_v j, hmemV j⟩ (hV i) (hV j)

theorem lka_mulAut_pow_fix {X : Type*} [Group X] [Finite X] (F : Set X)
    (hcard : Nat.card ↥F ≤ 4) (φ : MulAut X) (hφ : ∀ x, x ∈ F ↔ φ x ∈ F) :
    ∀ x ∈ F, (φ ^ 24) x = x := by
  intro x hx
  set σ : Equiv.Perm X := MulAut.toPerm X φ with hσ
  have hσF : ∀ y, σ y ∈ F ↔ y ∈ F := fun y => (hφ y).symm
  have h1 : (σ.subtypePerm hσF) ^ 24 = 1 := by
    have h2 : (σ.subtypePerm hσF) ^ Nat.card (Equiv.Perm ↥F) = 1 := pow_card_eq_one'
    rw [Nat.card_perm] at h2
    have h3 : (Nat.card ↥F).factorial ∣ 24 := by
      have := Nat.factorial_dvd_factorial hcard
      simpa [Nat.factorial] using this
    obtain ⟨t, ht⟩ := h3
    rw [ht, pow_mul, h2, one_pow]
  have h4 := congrArg (fun τ : Equiv.Perm ↥F => ((τ ⟨x, hx⟩ : ↥F) : X)) h1
  rw [Equiv.Perm.subtypePerm_pow] at h4
  have h5 : (σ ^ 24) x = (φ ^ 24) x := by
    rw [hσ, ← map_pow]
    rfl
  simpa [h5] using h4

theorem lka_w_fixed : coreAct 5 lka_t1.1 lka_w = lka_w ∧ coreAct 5 lka_t2.1 lka_w = lka_w := by
  constructor <;> apply Subtype.ext <;> decide

theorem lka_eq_one_of_fix (g : MulAut (lka_E × lka_E))
    (hg : ∀ (γ : ↥(alternatingGroup (Fin 5))) (x : lka_E × lka_E),
      g (lka_diag γ x) = lka_diag γ (g x))
    (h1 : g (lka_w, 1) = (lka_w, 1)) (h2 : g (1, lka_w) = (1, lka_w)) : g = 1 := by
  have hP1 : ∀ m : lka_E, g (m, 1) = (m, 1) := by
    intro m
    refine lka_gen (fun m => g (m, 1) = (m, 1)) ?_ ?_ ?_ h1 m
    · exact map_one g
    · intro a b ha hb
      have e : ((a * b, (1 : lka_E)) : lka_E × lka_E) = (a, 1) * (b, 1) := by simp
      show g (a * b, 1) = (a * b, 1)
      rw [e, map_mul, ha, hb]
    · intro γ m hm
      have e : ((coreAct 5 γ.1 m, (1 : lka_E)) : lka_E × lka_E) = lka_diag γ (m, 1) := by
        simp [lka_diag]
      show g (coreAct 5 γ.1 m, 1) = (coreAct 5 γ.1 m, 1)
      rw [e, hg, show g (m, 1) = (m, 1) from hm]
  have hP2 : ∀ m : lka_E, g (1, m) = (1, m) := by
    intro m
    refine lka_gen (fun m => g (1, m) = (1, m)) ?_ ?_ ?_ h2 m
    · exact map_one g
    · intro a b ha hb
      have e : (((1 : lka_E), a * b) : lka_E × lka_E) = (1, a) * (1, b) := by simp
      show g (1, a * b) = (1, a * b)
      rw [e, map_mul, ha, hb]
    · intro γ m hm
      have e : (((1 : lka_E), coreAct 5 γ.1 m) : lka_E × lka_E) = lka_diag γ (1, m) := by
        simp [lka_diag]
      show g (1, coreAct 5 γ.1 m) = (1, coreAct 5 γ.1 m)
      rw [e, hg, show g (1, m) = (1, m) from hm]
  refine MulEquiv.ext fun x => ?_
  obtain ⟨a, b⟩ := x
  have e : ((a, b) : lka_E × lka_E) = (a, 1) * (1, b) := by simp
  rw [MulAut.one_apply, e, map_mul, hP1, hP2]

theorem lka_pow_one (φ : MulAut (lka_E × lka_E))
    (hφ : ∀ (γ : ↥(alternatingGroup (Fin 5))) (x : lka_E × lka_E),
      φ (lka_diag γ x) = lka_diag γ (φ x)) : φ ^ 24 = 1 := by
  classical
  set F : Set (lka_E × lka_E) := {x | lka_diag lka_t1 x = x ∧ lka_diag lka_t2 x = x} with hF
  have hmem : ∀ x, x ∈ F ↔ φ x ∈ F := by
    intro x
    simp only [hF, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [← hφ, h1], by rw [← hφ, h2]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨φ.injective (by rw [hφ, h1]), φ.injective (by rw [hφ, h2])⟩
  have hsub : F ⊆ ↑({(1, 1), (lka_w, 1), (1, lka_w), (lka_w, lka_w)} : Finset (lka_E × lka_E)) := by
    rintro ⟨a, b⟩ ⟨h1, h2⟩
    have ha1 : coreAct 5 lka_t1.1 a = a := congrArg Prod.fst h1
    have ha2 : coreAct 5 lka_t2.1 a = a := congrArg Prod.fst h2
    have hb1 : coreAct 5 lka_t1.1 b = b := congrArg Prod.snd h1
    have hb2 : coreAct 5 lka_t2.1 b = b := congrArg Prod.snd h2
    rcases lka_fix_pair a ha1 ha2 with rfl | rfl <;>
      rcases lka_fix_pair b hb1 hb2 with rfl | rfl <;> simp
  have hcard : Nat.card ↥F ≤ 4 := by
    rw [Nat.card_coe_set_eq]
    calc F.ncard ≤ (↑({(1, 1), (lka_w, 1), (1, lka_w), (lka_w, lka_w)} :
            Finset (lka_E × lka_E)) : Set (lka_E × lka_E)).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = ({(1, 1), (lka_w, 1), (1, lka_w), (lka_w, lka_w)} : Finset (lka_E × lka_E)).card :=
          Set.ncard_coe_finset _
      _ ≤ 4 := Finset.card_le_four
  have hfix := lka_mulAut_pow_fix F hcard φ hmem
  have hgcomm : ∀ (n : ℕ) (γ : ↥(alternatingGroup (Fin 5))) (x : lka_E × lka_E),
      (φ ^ n) (lka_diag γ x) = lka_diag γ ((φ ^ n) x) := by
    intro n γ x
    induction n generalizing x with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφ, ih]
  obtain ⟨hw1, hw2⟩ := lka_w_fixed
  refine lka_eq_one_of_fix (φ ^ 24) (hgcomm 24) (hfix _ ⟨?_, ?_⟩) (hfix _ ⟨?_, ?_⟩)
  · simp [lka_diag, hw1]
  · simp [lka_diag, hw2]
  · simp [lka_diag, hw1]
  · simp [lka_diag, hw2]

end CFSG.Quasithin

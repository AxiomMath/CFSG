module

public import CFSG.RankThree.PartOne.KA5L.Frame

public noncomputable section

namespace CFSG.RankThree.PartOne.KA5L

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.E6 (chainRoot)

open CFSG.RankThree.PartOne.KE
open CFSG.ClassicalInvolution.WeakCT
open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

@[expose] def adj6 (a b : Fin 6) : Bool := (a.val + 1 == b.val) || (b.val + 1 == a.val)

@[expose] def reachN : ℕ → Fin 6 → Fin 6 → Bool
  | 0, a, b => adj6 a b
  | n + 1, a, b => reachN n a b ||
      decide (∃ k : Fin 6, a ≠ k ∧ k ≠ b ∧ a ≠ b ∧ reachN n a k = true ∧ reachN n k b = true)

theorem reachN_all : ∀ a b : Fin 6, a ≠ b → reachN 3 a b = true := by
  decide +kernel

theorem a5Root_ne_pair : ∀ a k b : Fin 6, a ≠ k → k ≠ b → a ≠ b →
    a5Root a k ≠ a5Root k b ∧ a5Root a k ≠ -a5Root k b := by
  decide +kernel

section Step

variable {L : Type} [Field L]

@[expose] def A5Transv (L : Type) [Field L] (a b : Fin 6) : Prop :=
  ∃ ε : Lˣ, ∀ (hab : a ≠ b) (t : L),
    a5Frame L (Matrix.SpecialLinearGroup.transvection hab t) =
      pinnedX Tag.E7 L (a5Root a b) ((ε : L) * t)

theorem A5Transv.step {a k b : Fin 6} (hak : a ≠ k) (hkb : k ≠ b) (hab : a ≠ b)
    (h1 : A5Transv L a k) (h2 : A5Transv L k b) : A5Transv L a b := by
  obtain ⟨ε1, he1⟩ := h1
  obtain ⟨ε2, he2⟩ := h2
  have hα : IsRoot Tag.E7 (a5Root a k) := isRoot_a5Root hak
  have hβ : IsRoot Tag.E7 (a5Root k b) := isRoot_a5Root hkb
  obtain ⟨hne, hne'⟩ := a5Root_ne_pair a k b hak hkb hab
  obtain ⟨hκ, hcomm⟩ := (simply_laced_root_commutator_unit Tag.E7
    (Or.inr (Or.inr (Or.inl rfl))) hα hβ hne hne').1 (by
      rw [a5Root_add]
      exact isRoot_a5Root hab)
  have hκ' : ((commConst Tag.E7 (a5Root a k) (a5Root k b) (1, 1) : ℤ) : L) ≠ 0 := by
    rcases hκ with h | h <;> simp [h]
  refine ⟨ε1 * ε2 * Units.mk0 _ hκ', fun hab' t => ?_⟩
  have hc := Matrix.SpecialLinearGroup.commutatorElement_transvection hak hkb hab' t 1
  rw [mul_one] at hc
  rw [← hc, map_commutatorElement, he1 hak t, he2 hkb 1, hcomm L, a5Root_add]
  congr 1
  simp only [Units.val_mul, Units.val_mk0]
  ring

end Step

section All

variable {L : Type} [Field L]

theorem A5Transv.adjacent {a b : Fin 6} (h : adj6 a b = true) : A5Transv L a b := by
  simp only [adj6, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · obtain ⟨c, rfl, rfl⟩ : ∃ c : Fin 5, c.castSucc = a ∧ c.succ = b :=
      ⟨⟨a.val, by omega⟩, Fin.ext rfl, Fin.ext (by simp [h])⟩
    refine ⟨1, fun hab t => ?_⟩
    rw [show hab = (Fin.castSucc_lt_succ (i := c)).ne from rfl, a5Frame_castSucc, a5Root_succ,
      ← pinnedX_single, Units.val_one, one_mul]
  · obtain ⟨c, rfl, rfl⟩ : ∃ c : Fin 5, c.succ = a ∧ c.castSucc = b :=
      ⟨⟨b.val, by omega⟩, Fin.ext (by simp [h]), Fin.ext rfl⟩
    refine ⟨1, fun hab t => ?_⟩
    rw [show hab = (Fin.castSucc_lt_succ (i := c)).ne' from rfl, a5Frame_succ, a5Root_succ_swap,
      ← pinnedX_neg_single, Units.val_one, one_mul]

theorem A5Transv.of_reachN : ∀ (n : ℕ) (a b : Fin 6), reachN n a b = true →
    A5Transv L a b := by
  intro n
  induction n with
  | zero => exact fun a b h => A5Transv.adjacent h
  | succ n ih =>
    intro a b h
    simp only [reachN, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨k, hak, hkb, hab, h1, h2⟩
    · exact ih a b h
    · exact A5Transv.step hak hkb hab (ih a k h1) (ih k b h2)

theorem a5Frame_transv (a b : Fin 6) (hab : a ≠ b) :
    ∃ ε : Lˣ, ∀ t : L, a5Frame L (Matrix.SpecialLinearGroup.transvection hab t) =
      pinnedX Tag.E7 L (a5Root a b) ((ε : L) * t) := by
  obtain ⟨ε, hε⟩ := A5Transv.of_reachN (L := L) 3 a b (reachN_all a b hab)
  exact ⟨ε, hε hab⟩

end All

end CFSG.RankThree.PartOne.KA5L

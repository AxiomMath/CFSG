module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AltPermInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X35Basic

public section

namespace CFSG.QuasithinUnique.Setup.X3
open Equiv CFSG.QuasithinUnique

set_option maxRecDepth 100000

private def rest7 (a b c : Fin 7) : Fin 7 :=
  ⟨(6 - (a.val + b.val + c.val)) % 7, Nat.mod_lt _ (by decide)⟩

private def other7 (x : Fin 7) : Fin 7 := ⟨(9 - x.val) % 7, Nat.mod_lt _ (by decide)⟩

private def ofTrip7 (t : Fin 7 × Fin 7 × Fin 7 × Fin 7) (i : Fin 7) : Fin 7 :=
  if i.val = 0 then t.1 else if i.val = 1 then t.2.1 else if i.val = 2 then t.2.2.1
  else if i.val = 3 then rest7 t.1 t.2.1 t.2.2.1 else if i.val = 4 then t.2.2.2
  else if i.val = 5 then other7 t.2.2.2 else 6

private def trip7B (t : Fin 7 × Fin 7 × Fin 7 × Fin 7) : Bool :=
  (List.finRange 7).all fun i => (List.finRange 7).all fun j =>
    (i == j || ofTrip7 t i != ofTrip7 t j) &&
    (decide (blkX7 i = blkX7 j) == decide (blkX7 (ofTrip7 t i) = blkX7 (ofTrip7 t j))) &&
    (decide (blkY7 i = blkY7 j) == decide (blkY7 (ofTrip7 t i) = blkY7 (ofTrip7 t j)))

private theorem trip7B_iff (t : Fin 7 × Fin 7 × Fin 7 × Fin 7) : trip7B t = true ↔
    ∀ i j, ((i = j ∨ ofTrip7 t i ≠ ofTrip7 t j) ∧
      (blkX7 i = blkX7 j ↔ blkX7 (ofTrip7 t i) = blkX7 (ofTrip7 t j))) ∧
      (blkY7 i = blkY7 j ↔ blkY7 (ofTrip7 t i) = blkY7 (ofTrip7 t j)) := by
  simp only [trip7B, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_decide]

private theorem six_of7 :
    ∀ a b g : Fin 7, a ≠ b → blkX7 a ≠ blkX7 g → blkX7 b ≠ blkX7 g → g = 6 := by
  decide +kernel

private theorem rest_of7 : ∀ a b c d : Fin 7, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    blkY7 a = blkY7 d → blkY7 b = blkY7 d → blkY7 c = blkY7 d → d = rest7 a b c := by
  decide +kernel

private theorem other_of7 : ∀ e f : Fin 7, e ≠ f → e ≠ 6 → f ≠ 6 → blkY7 e = blkY7 6 →
    blkY7 f = blkY7 6 → f = other7 e := by
  decide +kernel

private theorem eq_ofTrip7 (σ : Perm (Fin 7)) (hX : σ ∈ relStab blkX7)
    (hY : σ ∈ relStab blkY7) (i : Fin 7) : σ i = ofTrip7 (σ 0, σ 1, σ 2, σ 4) i := by
  have hX' : ∀ i j, blkX7 i = blkX7 j ↔ blkX7 (σ i) = blkX7 (σ j) := hX
  have hY' : ∀ i j, blkY7 i = blkY7 j ↔ blkY7 (σ i) = blkY7 (σ j) := hY
  have hne : ∀ i j : Fin 7, i ≠ j → σ i ≠ σ j := fun _ _ h => σ.injective.ne h
  have h6 : σ 6 = 6 := six_of7 (σ 0) (σ 1) (σ 6) (hne 0 1 (by decide))
    (fun e => absurd ((hX' 0 6).2 e) (by decide)) (fun e => absurd ((hX' 1 6).2 e) (by decide))
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact rest_of7 _ _ _ _ (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 0 3 (by decide))
      (hne 1 2 (by decide)) (hne 1 3 (by decide)) (hne 2 3 (by decide))
      ((hY' 0 3).1 rfl) ((hY' 1 3).1 rfl) ((hY' 2 3).1 rfl)
  · rfl
  · refine other_of7 _ _ (hne 4 5 (by decide)) (h6 ▸ hne 4 6 (by decide))
      (h6 ▸ hne 5 6 (by decide)) ?_ ?_
    · rw [← h6]
      exact (hY' 4 6).1 rfl
    · rw [← h6]
      exact (hY' 5 6).1 rfl
  · exact h6

private noncomputable def trip7Equiv :
    {σ : Perm (Fin 7) // σ ∈ relStab blkX7 ∧ σ ∈ relStab blkY7} ≃
      {t : Fin 7 × Fin 7 × Fin 7 × Fin 7 // trip7B t = true} where
  toFun σ := ⟨(σ.1 0, σ.1 1, σ.1 2, σ.1 4), by
    have hX : ∀ i j, blkX7 i = blkX7 j ↔ blkX7 (σ.1 i) = blkX7 (σ.1 j) := σ.2.1
    have hY : ∀ i j, blkY7 i = blkY7 j ↔ blkY7 (σ.1 i) = blkY7 (σ.1 j) := σ.2.2
    rw [trip7B_iff]
    intro i j
    rw [← eq_ofTrip7 σ.1 σ.2.1 σ.2.2 i, ← eq_ofTrip7 σ.1 σ.2.1 σ.2.2 j]
    exact ⟨⟨(em (i = j)).imp_right σ.1.injective.ne, hX i j⟩, hY i j⟩⟩
  invFun t := ⟨Equiv.ofBijective (ofTrip7 t.1) (Finite.injective_iff_bijective.1 fun i j hij =>
      (((trip7B_iff t.1).1 t.2 i j).1.1.resolve_right (not_not.2 hij))),
    fun i j => ((trip7B_iff t.1).1 t.2 i j).1.2, fun i j => ((trip7B_iff t.1).1 t.2 i j).2⟩
  left_inv σ := Subtype.ext (Equiv.ext fun i => (eq_ofTrip7 σ.1 σ.2.1 σ.2.2 i).symm)
  right_inv t := Subtype.ext rfl

private theorem card7_h :
    Fintype.card
          {σ : Perm (Fin 7) // σ ∈ relStab blkX7 ∧ σ ∈ relStab blkY7} = 48 := by
  rw [Fintype.card_congr trip7Equiv]
  decide +kernel

private def mate8 (x : Fin 8) : Fin 8 :=
  ⟨if x.val % 2 = 0 then x.val + 1 else x.val - 1, by split <;> omega⟩

private def ofQuad8 (t : Fin 8 × Fin 8 × Fin 8 × Fin 8) (i : Fin 8) : Fin 8 :=
  let x := if i.val < 2 then t.1 else if i.val < 4 then t.2.1 else if i.val < 6 then t.2.2.1
    else t.2.2.2
  if i.val % 2 = 0 then x else mate8 x

private def quad8B (t : Fin 8 × Fin 8 × Fin 8 × Fin 8) : Bool :=
  (List.finRange 8).all fun i => (List.finRange 8).all fun j =>
    (i == j || ofQuad8 t i != ofQuad8 t j) &&
    (decide (blkX8 i = blkX8 j) == decide (blkX8 (ofQuad8 t i) = blkX8 (ofQuad8 t j))) &&
    (decide (blkY8 i = blkY8 j) == decide (blkY8 (ofQuad8 t i) = blkY8 (ofQuad8 t j)))

private theorem quad8B_iff (t : Fin 8 × Fin 8 × Fin 8 × Fin 8) : quad8B t = true ↔
    ∀ i j, ((i = j ∨ ofQuad8 t i ≠ ofQuad8 t j) ∧
      (blkX8 i = blkX8 j ↔ blkX8 (ofQuad8 t i) = blkX8 (ofQuad8 t j))) ∧
      (blkY8 i = blkY8 j ↔ blkY8 (ofQuad8 t i) = blkY8 (ofQuad8 t j)) := by
  simp only [quad8B, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_decide]

private theorem mate8_of : ∀ x y : Fin 8, x ≠ y → blkY8 x = blkY8 y → y = mate8 x := by
  decide +kernel

private theorem eq_ofQuad8 (σ : Perm (Fin 8)) (h : σ ∈ relStab blkY8) (i : Fin 8) :
    σ i = ofQuad8 (σ 0, σ 2, σ 4, σ 6) i := by
  have h' : ∀ i j, blkY8 i = blkY8 j ↔ blkY8 (σ i) = blkY8 (σ j) := h
  fin_cases i
  · rfl
  · exact mate8_of _ _ (σ.injective.ne (a₁ := 0) (a₂ := 1) (by decide)) ((h' 0 1).1 rfl)
  · rfl
  · exact mate8_of _ _ (σ.injective.ne (a₁ := 2) (a₂ := 3) (by decide)) ((h' 2 3).1 rfl)
  · rfl
  · exact mate8_of _ _ (σ.injective.ne (a₁ := 4) (a₂ := 5) (by decide)) ((h' 4 5).1 rfl)
  · rfl
  · exact mate8_of _ _ (σ.injective.ne (a₁ := 6) (a₂ := 7) (by decide)) ((h' 6 7).1 rfl)

private noncomputable def quad8Equiv :
    {σ : Perm (Fin 8) // σ ∈ relStab blkX8 ∧ σ ∈ relStab blkY8} ≃
      {t : Fin 8 × Fin 8 × Fin 8 × Fin 8 // quad8B t = true} where
  toFun σ := ⟨(σ.1 0, σ.1 2, σ.1 4, σ.1 6), by
    have hX : ∀ i j, blkX8 i = blkX8 j ↔ blkX8 (σ.1 i) = blkX8 (σ.1 j) := σ.2.1
    have hY : ∀ i j, blkY8 i = blkY8 j ↔ blkY8 (σ.1 i) = blkY8 (σ.1 j) := σ.2.2
    rw [quad8B_iff]
    intro i j
    rw [← eq_ofQuad8 σ.1 σ.2.2 i, ← eq_ofQuad8 σ.1 σ.2.2 j]
    exact ⟨⟨(em (i = j)).imp_right σ.1.injective.ne, hX i j⟩, hY i j⟩⟩
  invFun t := ⟨Equiv.ofBijective (ofQuad8 t.1) (Finite.injective_iff_bijective.1 fun i j hij =>
      (((quad8B_iff t.1).1 t.2 i j).1.1.resolve_right (not_not.2 hij))),
    fun i j => ((quad8B_iff t.1).1 t.2 i j).1.2, fun i j => ((quad8B_iff t.1).1 t.2 i j).2⟩
  left_inv σ := Subtype.ext (Equiv.ext fun i => (eq_ofQuad8 σ.1 σ.2.2 i).symm)
  right_inv t := Subtype.ext rfl

private theorem card8_h :
    Fintype.card
          {σ : Perm (Fin 8) // σ ∈ relStab blkX8 ∧ σ ∈ relStab blkY8} = 128 := by
  rw [Fintype.card_congr quad8Equiv]
  decide +kernel

end CFSG.QuasithinUnique.Setup.X3

namespace Certificates

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X3 in
open Equiv CFSG.QuasithinUnique in
theorem certificate4138 : (Fintype.card
            {σ : Perm (Fin 7) // σ ∈ relStab blkX7 ∧ σ ∈ relStab blkY7} = 48)
    ∧ (Fintype.card
            {σ : Perm (Fin 8) // σ ∈ relStab blkX8 ∧ σ ∈ relStab blkY8} = 128) :=
  ⟨CFSG.QuasithinUnique.Setup.X3.card7_h, CFSG.QuasithinUnique.Setup.X3.card8_h⟩

end Certificates
